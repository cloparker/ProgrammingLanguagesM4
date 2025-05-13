(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)


fun typeCheck( itree(inode("program",_), [ stmt_list ]), m) = typeCheck(stmt_list, m)
  | typeCheck( itree(inode("stmtList",_), [ epsilon ]), m) = m
  | typeCheck( itree(inode("stmtList",_), [ stmt , semiColon , stmtList ]), m) = typeCheck(stmtList, typeCheck(stmt, m))
  | typeCheck( itree(inode("declaration",_), [ typeName , id ]), m) = updateEnv(id, typeName, new(), m)
  | typeCheck( itree(inode("assign",_), [ id , equals , expression ]), m) =
    let
      val t_exp = typeOf(expression, m)
      val t_id = getType(accessEnv(id, m))
    in
      if t_exp = t_id then m else raise model_error
    end
  | typeCheck( itree(inode("if",_), [ inode("if",_), expression, inode("then",_), stmt, inode("else",_), stmt ]), m) =
    let
      val t_exp = typeOf(expression, m)
      val t_stmt = typeOf(stmt, m)
    in
      if t_exp = BOOL then m else raise model_error
    end
  | typeCheck( itree(inode("if",_), [ inode("if",_), expression, inode("then",_)]), m) = 
    let
      val t_exp = typeOf(expression, m)
      val t_stmt = typeOf(stmt, m)
    in
      if t_exp = BOOL then m else raise model_error
    end
  | typeCheck( itree(inode("decoratedID",_), [ id , inode("++",_) ]), m) =
    let
      val t = typeOf(id, m)
    in
      if t = INT then m else raise model_error
    end
  | typeCheck( itree(inode("decoratedID",_), [ id , inode("--",_) ]), m) =
    let
      val t = typeOf(id, m)
    in
      if t = INT then m else raise model_error
    end
  | typeCheck( itree(inode("decoratedID",_), [ inode("++",_), id ]), m) =
    let
      val t = typeOf(id, m)
    in
      if t = INT then m else raise model_error
    end
  | typeCheck( itree(inode("decoratedID",_), [ inode("--",_), id ]), m) =
    let
      val t = typeOf(id, m)
    in
      if t = INT then m else raise model_error
    end
  | typeCheck( itree(inode("iterative",_), [ inode("while",_), inode("(",_), expression, inode(")",_), block ]), m) =
    let
      val t = typeOf(expression, m)
      val m1 = typeOf(block, m)
    in
      if t = BOOL then m else raise model_error
    end
  | typeCheck( itree(inode("iterative",_), [ inode("for",_), inode("(",_), assign, semiColon, expression, semiColon, decoratedID, inode(")",_), block ]), m) =
    let
      val m1 = typeCheck(assign, m)
      val t = typeOf(expression, m)
      val m2 = typeCheck(decoratedID, m)
      val m3 = typeCheck(block, m)
    in
      if t = BOOL then m else raise model_error
    end
  | typeCheck( itree(inode("block",_), [ stmtList ]), m) = typeCheck(stmtList, m)
  | typeCheck( itree(inode("block",_), [ epsilon ]), m) = m
  | typeCheck( itree(inode("print",_), [ inode("print(",_), expression, inode(")",_) ]), m) =
    let
      val t = typeOf(expression, m)
    in
      if t = BOOL then m else raise model_error
    end
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")

fun typeOf( itree(inode("expression",_), [ expression, itree(inode("||",_), logicalOR) ]), m) =
  let
    val t1 = typeOf(expression, m)
    val t2 = typeOf(logicalOR, m)
  in
    if t1 = BOOL andalso t2 = BOOL then BOOL else raise model_error
  end
  | typeOf( itree(inode("expression",_), [ logicalOR, itree(inode("&&",_), logicalAND) ]), m) =
  let
    val t1 = typeOf(logicalOR, m)
    val t2 = typeOf(logicalAND, m)
  in
    if t1 = BOOL andalso t2 = BOOL then BOOL else raise model_error
  end
  | typeOf( itree(inode("logicalOR",_), [ logicalAND ]), m) = typeOf(logicalAND, m)
  | typeOf( itree(inode("logicalAND",_), [ logicalAND, itree(inode("==",_), equality) ]), m) =
  let
    val t1 = typeOf(logicalAND, m)
    val t2 = typeOf(equality, m)
  in
    if t1 = BOOL andalso t2 = BOOL then BOOL else raise model_error
  end
  | typeOf( itree(inode("logicalAND",_), [ equality ]), m) = typeOf(equality, m)
  | typeOf( itree(inode("equality",_), [ equality, itree(inode("<",_), additive) ]), m) =
  let
    val t1 = typeOf(equality, m)
    val t2 = typeOf(additive, m)
  in
    if t1 = INT andalso t2 = INT then BOOL else raise model_error
  end
  | typeOf( itree(inode("equality",_), [ equality, itree(inode(">",_), additive) ]), m) =
  let
    val t1 = typeOf(equality, m)
    val t2 = typeOf(additive, m)
  in
    if t1 = INT andalso t2 = INT then BOOL else raise model_error
  end
  | typeOf( itree(inode("equality",_), [ equality, itree(inode("<=",_), additive) ]), m) =
  let
    val t1 = typeOf(equality, m)
    val t2 = typeOf(additive, m)
  in
    if t1 = INT andalso t2 = INT then BOOL else raise model_error
  end
  | typeOf( itree(inode("equality",_), [ equality, itree(inode(">=",_), additive) ]), m) =
  let
    val t1 = typeOf(equality, m)
    val t2 = typeOf(additive, m)
  in
    if t1 = INT andalso t2 = INT then BOOL else raise model_error
  end
  | typeOf( itree(inode("equality",_), [ additive ]), m) = typeOf(additive, m)
  | typeOf( itree(inode("additive",_), [ additive, itree(inode("+",_), multiplicative) ]), m) =
  let
    val t1 = typeOf(additive, m)
    val t2 = typeOf(multiplicative, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("additive",_), [ additive, itree(inode("-",_), multiplicative) ]), m) =
  let
    val t1 = typeOf(additive, m)
    val t2 = typeOf(multiplicative, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("additive",_), [ multiplicative ]), m) = typeOf(multiplicative, m)
  | typeOf( itree(inode("multiplicative",_), [ multiplicative, itree(inode("*",_), unary) ]), m) =
  let
    val t1 = typeOf(multiplicative, m)
    val t2 = typeOf(unary, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("multiplicative",_), [ multiplicative, itree(inode("div",_), unary) ]), m) =
  let
    val t1 = typeOf(multiplicative, m)
    val t2 = typeOf(unary, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("multiplicative",_), [ multiplicative, itree(inode("mod",_), unary) ]), m) =
  let
    val t1 = typeOf(multiplicative, m)
    val t2 = typeOf(unary, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("multiplicative",_), [ unary ]), m) = typeOf(unary, m)
  | typeOf( itree(inode("unary",_), [ itree(inode("-",_), unary) ]), m) =
  let
    val t = typeOf(unary, m)
  in
    if t = INT then INT else raise model_error
  end
  | typeOf( itree(inode("unary",_), [ itree(inode("!",_), unary) ]), m) =
  let
    val t = typeOf(unary, m)
  in
    if t = BOOL then BOOL else raise model_error
  end
  | typeOf( itree(inode("unary",_), [ exponent ]), m) = typeOf(exponent, m)
  | typeOf( itree(inode("exponent",_), [ factor, itree(inode("**",_), exponent) ]), m) =
  let
    val t1 = typeOf(factor, m)
    val t2 = typeOf(exponent, m)
  in
    if t1 = INT andalso t2 = INT then INT else raise model_error
  end
  | typeOf( itree(inode("exponent",_), [ factor ]), m) = typeOf(factor, m)
  | typeOf( itree(inode("factor",_), [ itree(inode("(",_), expression), inode(")",_) ]), m) = typeOf(expression, m)
  | typeOf( itree(inode("factor",_), [ id ]), m) = getType(accessEnv(id, m))
  | typeOf( itree(inode("factor",_), [ integer_value ]), m) = INT
  | typeOf( itree(inode("factor",_), [ boolean_value ]), m) = BOOL
  | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")
(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)




