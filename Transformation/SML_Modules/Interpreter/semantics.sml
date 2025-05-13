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
    ) = updateEnv(id, typeName, new(), m)
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
                if value then M(block, m1) else m1
            end
    in
        loop(m)
    end



    | M _ = raise Fail("error in Semantics.M - this should never occur")


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



(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








