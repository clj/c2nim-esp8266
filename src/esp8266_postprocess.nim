import
  strutils, os, times, parseopt, c2nim/compiler/llstream, c2nim/compiler/ast,
  c2nim/compiler/renderer, c2nim/compiler/options, c2nim/compiler/msgs,
  c2nim/clex, c2nim/cparse, c2nim/postprocessor, macros, ropes,
  c2nim/compiler/idents, tables, sequtils

type
  pp_states = enum
    in_const
    in_object
    remove_pragma_header
    is_neg
  pp_state = set[pp_states]

var
  as_declerations = initTable[string, TNodeKind]()
  returns_declerations = initTable[string, string]()
  params_declarations = initTable[string, Table[string, string]]()
  global_remove_pragma_header = false


proc debug(n: PNode, level: int = 0) =
  var val: string
  case n.kind:
  of nkCharLit..nkUInt64Lit:
    val = $n.intVal
  of nkFloatLit..nkFloat128Lit:
    val = $n.floatVal
  of nkStrLit..nkTripleStrLit:
    val = $n.strVal
  of nkSym:
    val = $n.sym
  of nkIdent:
    val = n.ident.s
  else:
    discard
  if val != "":
    val = " (" & val & ")"

  echo(spaces(level) & $n.kind & val)

  for i in 0 ..< n.safeLen:
    debug(n.sons[i], level + 1)


proc getIdent(s: string): PIdent = getIdent(identCache, s)


proc pp(n: var PNode, stmtList: PNode = nil, idx: int = -1, state: pp_state = {}) =
  case n.kind
  of nkIntLit:
    # Mark all int literals in const declarations (`in_const`) with
    # 'u32 or 'i32 if the value is negative (`is_neg`)
    if in_const in state:
      var node_type: TNodeKind
      if is_neg in state:
        node_type = nkInt32Lit
      else:
        node_type = nkUInt32Lit
      let m = newNodeI(node_type, n.info)
      m.intVal = n.intVal
      m.flags = n.flags
      m.comment = n.comment
      n = m
  of nkPrefix:
    # set `is_neg` - to record if a literal might be negative
    var state = state
    if in_const in state and n.sons[0].kind == nkIdent and n.sons[0].ident.s == "-":
      state = state + {is_neg}
    for i in 1 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)
  of nkStmtList:
    # Fix nested struct which generates a spurious var and header pragma
    # Also set `remove_pragma_header` - to actually remove the pragma during recursion
    # e.g.:
    # next* {.importc: "next".}: tuple[sle_next: ptr station_info] ##  next element
    # vs
    # var next* {.importc: "next", header: "user_interface.h".}: tuple[sle_next: ptr station_info] ##  next element
    # From:
    # struct bss_info {
    #   struct {
    #       struct bss_info *stqe_next;  /* next element */
    #   } next;
    # ...
    # }
    var updated_state = state
    if in_object in updated_state:
      if n[0].kind == nkStmtList and n[0][0].kind == nkVarSection:
        # Remove the two nkStmtList and the nkVarSection
        n = n[0][0][0]
        # Remove the importc pragma
        updated_state = updated_state + {remove_pragma_header}
    for i in 0 ..< n.safeLen: pp(n.sons[i], n, i, updated_state)
  # of nkRecList:
  #   var consts: seq[int] = @[]
  #   for i in 0 ..< n.safeLen:
  #     pp(n.sons[i], stmtList, idx, state)
  #     if n.sons[i].kind == nkConstSection:
  #       consts.insert(i)
  #   for i in consts:
  #     var c = n.sons[i]
  #     delete(n.sons, i)
  #     insert(stmtList.sons, c, idx)
  of nkConstSection:
    # set `in_const` - so we know that we are in a const section
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state + {in_const})
  of nkTemplateDef:
    # Turn templates marked "#as proc" into procs
    var name: string
    if n[0].kind == nkPostfix:
      name = n[0][1].ident.s
    elif n[0].kind == nkIdent:
      name = n[0].ident.s
    else:
      raise newException(ValueError, "Unknown ident for nkTemplateDef")
    if name in as_declerations:
      if as_declerations[name] != nkProcDef:
        return
    # Pragmas
    let p = newNodeI(nkPragma, n.info)
    p.add(newNodeI(nkIdent, n.info))
    p[0].ident = getIdent("noconv")
    # Pragma: importc
    p.add(newNodeI(nkExprColonExpr, n.info))
    p[1].add(newNodeI(nkIdent, n.info))
    p[1][0].ident = getIdent("importc")
    p[1].add(newNodeI(nkStrLit, n.info))
    p[1][1].strVal = $(n[0][1])
    # Pragma: header
    p.add(newNodeI(nkExprColonExpr, n.info))
    p[2].add(newNodeI(nkIdent, n.info))
    p[2][0].ident = getIdent("header")
    p[2].add(newNodeI(nkStrLit, n.info))
    p[2][1].strVal = toFilename(gConfig, n.info).extractFilename
    # Fix formal params (stmt->uint32)
    if n[3][0].ident == getIdent("untyped") or n[3][0].ident == getIdent("expr"):
      if name in returns_declerations:
        n[3][0].ident = getIdent(returns_declerations[name])
      else:
        n[3].sons[0] = newNodeI(nkEmpty, n.info)
    # Fix formal params (expr->uint32)
    for i in 0 ..< n[3].safeLen:
      if n[3][i].kind != nkIdentDefs:
        continue
      let idx = n[3][i].safeLen - 2
      if n[3][i][idx].kind == nkIdent and n[3][i][idx].ident.s == "untyped":
        n[3][i][idx].ident = getIdent("uint32")
    # Replace template with proc
    let emptyNode = newNodeI(nkEmpty, n.info)
    let m = newProcNode(nkProcDef, n.info, body=emptyNode,
                        params=n[3], name=n[0], pattern=emptyNode,
                        genericParams=emptyNode, pragmas=p, exceptions=emptyNode)
    n = m
  of nkCommentStmt:
    # Parse the unoffical directives which are stored in comments
    for line in n.comment.splitLines():
      # // #as (template|proc|type) IDENT
      let as_pos = line.find("#as ")
      if as_pos != -1:
        proc as_type(s: string): TNodeKind =
          if s == "template":
            return nkTemplateDef
          elif s == "proc":
            return nkProcDef
          elif s == "type":
            return nkTypeDef
          else:
            raise newException(ValueError, "Unknown #as type: " & s)
        let args = line[as_pos..^1].split()
        as_declerations[args[2]] = as_type(args[1])
      # // #returns TYPE IDENT
      let returns_pos = line.find("#returns ")
      if returns_pos != -1:
        let args = line[returns_pos..^1].split()
        returns_declerations[args[2]] = args[1]
      # // #noheader
      let no_header_pos = line.find("#noheader")
      if no_header_pos != -1:
        global_remove_pragma_header = true
      # // #params IDENT IDENT TYPE, IDENT TYPE, ...
      let params_pos = line.find("#params")
      if params_pos != -1:
        let args = line[params_pos..^1].split(maxSplit=2)
        let params = args[2].split(',')
        for param in params:
          let mapping = param.strip().split()
          if not (args[1] in params_declarations):
            params_declarations[args[1]] = initTable[string, string]()
          params_declarations[args[1]][mapping[0]] = mapping[1]
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)
  of nkObjectTy:
    # set `in_object` - so we know that we are in an object declaration
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state + {in_object})
  of nkPragma:
    # Remove header pragmas
    if remove_pragma_header in state:
      for i in 0 ..< n.safeLen:
        if n[i].kind == nkExprColonExpr and n[i][0].kind == nkIdent and n[i][0].ident == getIdent("header"):
          delete(n.sons, i, i)
          break
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)
  of nkTypeDef:
    if n.safeLen >= 3 and n[2].kind == nkEnumTy:
      # Add importc and header pragma to enums
      let pragma = n[0][1]
      # Pragma: importc
      let p1 = newNodeI(nkExprColonExpr, n.info)
      p1.add(newNodeI(nkIdent, n.info))
      p1[0].ident = getIdent("importc")
      p1.add(newNodeI(nkStrLit, n.info))
      p1[1].strVal = $(n[0][0][1])
      pragma.add(p1)
      # Pragma: header
      let p2 = newNodeI(nkExprColonExpr, n.info)
      p2.add(newNodeI(nkIdent, n.info))
      p2[0].ident = getIdent("header")
      p2.add(newNodeI(nkStrLit, n.info))
      p2[1].strVal = toFilename(gConfig, n.info).extractFilename
      pragma.add(p2)
    if n.safeLen >= 3 and n[2].kind == nkProcTy:
      # Change types of formal parameters in proctypes
      var name: string
      if n[0].kind == nkPostfix:
        name = n[0][1].ident.s
      else:
        name = n[0].ident.s
      if name in params_declarations:
        let mappings = params_declarations[name]
        for i in 1 ..< n[2].sons[0].safeLen:
          let n = n[2].sons[0][i]
          let ident = n.sons[0].ident.s
          if ident in mappings:
            n.sons[1].ident = getIdent(mappings[ident])
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)
  of nkProcDef:
    # Change types of formal parameters in proc defs
    var name: string
    if n[0].kind == nkPostfix:
      name = n[0][1].ident.s
    else:
      name = n[0].ident.s
    if name in params_declarations:
      let mappings = params_declarations[name]
      for i in 1 ..< n[3].safeLen:
        let n = n[3][i]
        let ident = n.sons[0].ident.s
        if ident in mappings:
          n.sons[1].ident = getIdent(mappings[ident])
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)
  else:
    for i in 0 ..< n.safeLen: pp(n.sons[i], stmtList, idx, state)


proc esp8266_postprocess*(n: PNode): PNode =
  result = n
  var state: pp_state = {}
  if global_remove_pragma_header:
    state = state + {remove_pragma_header}
  pp(result, state = state)