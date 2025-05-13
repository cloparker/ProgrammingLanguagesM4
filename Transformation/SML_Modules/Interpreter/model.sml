(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;

fun toInt(Integer x) = x

fun toBool(Boolean x) = x

type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

fun accessEnv ([], _) = NONE
  | accessEnv ((id, t, loc)::rest, x) = 
      if id = x then
        SOME (t, loc)
      else
        accessEnv (rest, x)

fun accessStore ([], _) = NONE
  | accessStore ((loc, value)::rest, targetLocation) = 
      if loc = targetLocation then
        SOME value
      else
        accessStore (rest, targetLocation)

fun updateEnv (id, t, loc, (env, s)) = ((id, t, loc)::env, s)

fun updateStore (store, targetLocation, newValue) = 

fun getLoc (environment, variableName) = 

fun getType (t, loc) = t

fun showEnv (environment) = 
    

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)












