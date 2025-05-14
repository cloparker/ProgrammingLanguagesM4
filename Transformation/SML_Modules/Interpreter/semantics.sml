(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun E(itree(inode("expression",_),
                [ 
                    expression,
                    itree(inode("||",_),[]),
                    logicalOr
                ] 
             ), 
        m
    ) =
    let
        val (value, m1) = E(expression, m)
        val value = toBool value
    in
        if value then (Boolean true, m1) else E(logicalOr, m1)
    end
    | E(itree(inode("expression",_),
                [ 
                    logicalOr
                ] 
             ), 
        m
    ) = E(logicalOr, m)
    | E(itree(inode("logicalOr",_),
                [ 
                    logicalAnd,
                    itree(inode("&&",_),[]),
                    logicalOr
                ] 
             ), 
        m
    ) = 
    let
        val (value, m1) = E(logicalAnd, m)
        val value = toBool value
    in
        if value then E(logicalOr, m1) else (Boolean false, m1)
    end
    | E(itree(inode("logicalOr",_),
                [ 
                    logicalAnd
                ] 
             ), 
        m
    ) = E(logicalAnd, m)
    | E(itree(inode("logicalAnd",_),
                [ 
                    logicalAnd,
                    itree(inode("==",_),[]),
                    notEquals
                ] 
             ), 
        m
    ) = 
    let
        val (value, m1) = E(logicalAnd, m)
        val value = toBool value
        val (value2, m2) = E(notEquals, m1)
        val value2 = toBool value2
    in
        if value = value2 then (Boolean true, m2) else (Boolean false, m2)
    end
    | E(itree(inode("logicalAnd",_),
                [ 
                    notEquals
                ]
             ), 
        m
    ) = E(notEquals, m)
    | E(itree(inode("notEquals",_),
                [ 
                    notEquals,
                    itree(inode("!=",_),[]),
                    equality
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(equality, m)
        val value = toBool value
        val (value2, m2) = E(notEquals, m1)
        val value2 = toBool value2
    in
        if value = value2 then (Boolean false, m2) else (Boolean true, m2)
    end
    | E(itree(inode("notEquals",_),
                [ 
                    equality
                ]
             ), 
        m
    ) = E(equality, m)
    | E(itree(inode("equality",_),
                [ 
                    equality,
                    itree(inode("<",_),[]),
                    additive
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(additive, m)
        val value = toInt value
        val (value2, m2) = E(equality, m1)
        val value2 = toInt value2
    in
        if value < value2 then (Boolean true, m2) else (Boolean false, m2)
    end
    | E(itree(inode("equality",_),
                [ 
                    equality,
                    itree(inode(">",_),[]),
                    additive
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(additive, m)
        val value = toInt value
        val (value2, m2) = E(equality, m1)
        val value2 = toInt value2
    in
        if value > value2 then (Boolean true, m2) else (Boolean false, m2)
    end
    | E(itree(inode("equality",_),
                [ 
                    equality,
                    itree(inode("<=",_),[]),
                    additive
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(additive, m)
        val value = toInt value
        val (value2, m2) = E(equality, m1)
        val value2 = toInt value2
    in
        if value <= value2 then (Boolean true, m2) else (Boolean false, m2)
    end
    | E(itree(inode("equality",_),
                [ 
                    equality,
                    itree(inode(">=",_),[]),
                    additive
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(additive, m)
        val value = toInt value
        val (value2, m2) = E(equality, m1)
        val value2 = toInt value2
    in
        if value >= value2 then (Boolean true, m2) else (Boolean false, m2)
    end
    | E(itree(inode("equality",_),
                [ 
                    additive
                ]
             ), 
        m
    ) = E(additive, m)
    | E(itree(inode("additive",_),
                [ 
                    additive,
                    itree(inode("+",_),[]),
                    multiplicative
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(multiplicative, m)
        val value = value
        val (value2, m2) = E(additive, m1)
        val value2 = value2
    in
        (value + value2, m2)
    end
    | E(itree(inode("additive",_),
                [ 
                    additive,
                    itree(inode("-",_),[]),
                    multiplicative
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(multiplicative, m)
        val value = toInt value
        val (value2, m2) = E(additive, m1)
        val value2 = toInt value2
    in
        (value - value2, m2)
    end
    | E(itree(inode("additive",_),
                [ 
                    multiplicative
                ]
             ), 
        m
    ) = E(multiplicative, m)
    | E(itree(inode("multiplicative",_),
                [ 
                    multiplicative,
                    itree(inode("*",_),[]),
                    unary
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(unary, m)
        val value = toInt value
        val (value2, m2) = E(multiplicative, m1)
        val value2 = toInt value2
    in
        (value * value2, m2)
    end
    | E(itree(inode("multiplicative",_),
                [ 
                    multiplicative,
                    itree(inode("div",_),[]),
                    unary
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(unary, m)
        val value = toInt value
        val (value2, m2) = E(multiplicative, m1)
        val value2 = toInt value2
    in
        (value div value2, m2)
    end
    | E(itree(inode("multiplicative",_),
                [ 
                    multiplicative,
                    itree(inode("mod",_),[]),
                    unary
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(unary, m)
        val value = toInt value
        val (value2, m2) = E(multiplicative, m1)
        val value2 = toInt value2
    in
        (value mod value2, m2)
    end
    | E(itree(inode("multiplicative",_),
                [ 
                    unary
                ]
             ), 
        m
    ) = E(unary, m)

    | E(itree(inode("unary",_),
                [ 
                    itree(inode("-",_),[]),
                    unary
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(unary, m)
        val value = toInt value
    in
        (~value, m1)
    end
    | E(itree(inode("unary",_),
                [ 
                    itree(inode("!",_),[]),
                    logicalOr
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(logicalOr, m)
        val value = toBool value
    in
        (not value, m1)
    end
    | E(itree(inode("unary",_),
                [ 
                    exponent
                ]
             ), 
        m
    ) = E(exponent, m)
    | E(itree(inode("exponent",_),
                [ 
                    factor,
                    itree(inode("^",_),[]),
                    exponent
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(factor, m)
        val value = toInt value
        val (value2, m2) = E(exponent, m1)
        val value2 = toInt value2
        fun exponent(base, power) = 
            if power = 0 then 1
            else base * exponent(base, power - 1)
    in
        (exponent(value, value2), m2)
    end
    | E(itree(inode("exponent",_),
                [ 
                    factor
                ]
             ), 
        m
    ) = E(factor, m)
    | E(itree(inode("factor",_),
                [ 
                    itree(inode(integer_value,_),[])
                ]
             ), 
        m
    ) = (Int.fromString integer_value, m)
    | E(itree(inode("factor",_),
                [ 
                    itree(inode(boolean_value,_),[])
                ]
             ), 
        m
    ) = (Bool.fromString boolean_value, m)
    | E(itree(inode("factor",_),
                [ 
                    itree(inode(id,_),[])
                ]
             ), 
        m
    ) = 
    let
        val loc = getLoc(id, m)
        val value = accessStore(loc, m)
    in
        (value, m)
    end
    | E(itree(inode("factor",_),
                [ 
                    itree(inode("(",_),[]),
                    expression,
                    itree(inode(")",_),[])
                ]
             ), 
        m
    ) = E(expression, m)
    | E(itree(inode("factor",_),
                [ 
                    itree(inode("|",_),[]),
                    expression,
                    itree(inode("|",_),[])
                ]
             ), 
        m
    ) = 
    let
        val (value, m1) = E(expression, m)
        val value = toInt value
    in
        (Int.abs value, m1)
    end

fun M(itree(inode("program",_), 
                [ 
                    stmtList
                ] 
             ), 
        m
    ) = M(stmtList, m)
    | M(itree(inode("stmtList",_), 
                [ 
                    stmt,
                    semiColon,
                    stmtList
                ] 
             ), 
        m
    ) = M(stmtList, M(stmt, m))
    | M(itree(inode("stmtList",_), 
                [ 
                    epsilon
                ] 
             ), 
        m
    ) = m
    | M(itree(inode("stmt",_),
                [ 
                    declaration
                ] 
             ), 
        m
    ) = M(declaration, m)
    | M(itree(inode("stmt",_),
                [ 
                    assignment
                ] 
             ), 
        m
    ) = M(assignment, m)
    | M(itree(inode("stmt",_),
                [ 
                    conditional
                ] 
             ), 
        m
    ) = M(conditional, m)
    | M(itree(inode("stmt",_),
                [ 
                    decoratedID
                ] 
             ), 
        m
    ) = M(decoratedID, m)
    | M(itree(inode("stmt",_),
                [ 
                    iterative
                ] 
             ), 
        m
    ) = M(iterative, m)
    | M(itree(inode("stmt",_),
                [ 
                    output
                ] 
             ), 
        m
    ) = M(output, m)
    | M(itree(inode("stmt",_),
                [ 
                    block
                ] 
             ), 
        m
    ) = M(block, m)
    | M(itree(inode("declaration",_),
                [ 
                    typeName,
                    id
                ] 
             ), 
        m
    ) = updateEnv(id, typeName, new(m))
    | M(itree(inode("assign",_),
                [ 
                    id,
                    equals,
                    expression
                ] 
             ), 
        m
    ) = 
    let
        val loc = getLoc(accessEnv(id, m))
        val (value, m1) = E(expression, m)
    in
        updateStore(loc, value, m1)
    end
    | M(itree(inode("conditional",_),
                [ 
                    itree(inode("if",_),[]),
                    expression,
                    itree(inode("then",_),[]),
                    block,
                    itree(inode("else",_),[]),
                    block
                ] 
             ), 
        m
    ) = 
    let
        val (value, m1) = E(expression, m)
        val value = toBool value
    in
        if value then M(block, m1) else M(block, m1)
    end
    | M(itree(inode("conditional",_),
                [ 
                    itree(inode("if",_),[]),
                    expression,
                    itree(inode("then",_),[]),
                    block
                ] 
             ), 
        m
    ) = 
    let
        val (value, m1) = E(expression, m)
        val value = toBool value
    in
        if value then M(block, m1) else m1
    end
    | M(itree(inode("decoratedID",_),
                [ 
                    itree(inode("++",_),[]),
                    id
                ] 
             ), 
        m
    ) = 
    let
        val loc = getLoc(accessEnv(id, m))
        val value = accessStore(loc, m)
    in
        updateStore(loc, value + 1, m)
    end
    | M(itree(inode("decoratedID",_),
                [ 
                    itree(inode("--",_),[]),
                    id
                ] 
             ), 
        m
    ) = 
    let
        val loc = getLoc(accessEnv(id, m))
        val value = accessStore(loc, m)
    in
        updateStore(loc, value - 1, m)
    end
    | M(itree(inode("decoratedID",_),
                [ 
                    id,
                    itree(inode("++",_),[])
                ] 
             ), 
        m
    ) = 
    let
        val loc = getLoc(accessEnv(id, m))
        val value = accessStore(loc, m)
    in
        updateStore(loc, value + 1, m)
    end
    | M(itree(inode("decoratedID",_),
                [ 
                    id,
                    itree(inode("--",_),[])
                ] 
             ), 
        m
    ) = 
    let
        val loc = getLoc(accessEnv(id, m))
        val value = accessStore(loc, m)
    in
        updateStore(loc, value - 1, m)
    end
    | M(itree(inode("iterative",_),
                [ 
                    whileLoop
                ] 
             ), 
        m
    ) = M(whileLoop, m)
    | M(itree(inode("iterative",_),
                [ 
                    forLoop
                ] 
             ), 
        m
    ) = M(forLoop, m)
    | M(itree(inode("whileLoop",_),
                [ 
                    itree(inode("while",_),[]),
                    itree(inode("(",_),[]),
                    expression,
                    itree(inode(")",_),[]),
                    block
                ] 
             ), 
        m
    ) = 
    let
        fun loop(m) = 
            let
                val (value, m1) = E(expression, m)
                val value = toBool value
            in
                if value then loop(M(block, m1)) else m1
            end
    in
        loop(m)
    end
    | M(itree(inode("forLoop",_),
                [ 
                    itree(inode("for",_),[]),
                    itree(inode("(",_),[]),
                    assign,
                    itree(inode(";",_),[]),
                    expression,
                    itree(inode(";",_),[]),
                    decoratedID,
                    itree(inode(")",_),[]),
                    block
                ] 
             ), 
        m
    ) = 
    let
        val m1 = M(assign, m)
        fun loop(m) =
            let
                val (value, m1) = E(expression, m)
                val value = toBool value
                val m2 = M(decoratedID, m1)
            in
                if value then loop(M(block, m2)) else m2
            end
    in
        loop(m1)
    end
    | M(itree(inode("block",_),
                [ 
                    itree(inode("{",_),[]),
                    stmtList,
                    itree(inode("}",_),[])
                ] 
             ), 
        m
    ) = M(stmtList, m)

    | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
    | M _ = raise Fail("error in Semantics.M - this should never occur")

    

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)


