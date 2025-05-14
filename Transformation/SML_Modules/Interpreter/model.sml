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

exception runtime_error;
fun error msg = (print msg; raise runtime_error);

(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )
(* Allocate a new location (like malloc) *)
fun new (env, counter, store) = (counter, (env, counter + 1, store))

(* Add a new binding to the environment *)
fun updateEnv (id, t, loc) (env, c, store) = ((id, t, loc) :: env, c, store)
(* Get type and location from env *)
fun accessEnv (id1, (env, _ , _)) = 
  let
    fun aux [] = error ("Error: accessEnv: " ^ id1 ^ " not found.")
      | aux ((id,t,loc)::env) = 
          if id1 = id then (t, loc)
          else aux env
  in
    aux env
  end
(* Get location of a variable *)
fun getLoc id m = #2 (accessEnv (id, m))
(* Get type of a variable *)
fun getType id m = #1 (accessEnv (id, m))
(* Look up value in store *)
fun accessStore (loc, (_, _, store)) = 
  let
    fun aux [] = error ("Error: accessStore: location " ^ Int.toString loc ^ " not found.")
      | aux ((l, v)::rest) = if l = loc then v else aux rest
  in
    aux store
  end
(* Update store with a new value *)
fun updateStore (loc, v) (env, c, store) =
  let
    fun aux [] = error ("Error: updateStore: location " ^ Int.toString loc ^ " not found.")
      | aux ((l, old)::rest) =
          if l = loc then (l, v)::rest
          else (l, old)::(aux rest)
  in
    (env, c, aux store)
  end
(* Show environment *)
fun typeToString INT   = "int"
  | typeToString BOOL  = "bool"
  | typeToString ERROR = "error"
fun envEntryToString (id, t, loc) =
  "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")"
fun showEnv [] = print "\n"
  | showEnv (entry::env) = (
      print("\n" ^ envEntryToString entry);
      showEnv env
    )
  

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)












