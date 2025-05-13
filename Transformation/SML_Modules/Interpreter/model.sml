structure Model =
struct 
  exception runtime_error;
  fun error msg = (print msg; raise runtime_error);

  datatype types = INT | BOOL | ERROR;

  datatype denotable_value =
      Boolean of bool 
    | Integer of int;

  type loc   = int
  type env   = (string * types * loc) list
  type store = (loc * denotable_value) list

  (* The program state: environment, next free location, store *)
  val initialModel = ([]:env, 0:loc, []:store)

  (* Converts a leaf term to a string *)
  fun getLeaf(term) = CONCRETE.leavesToStringRaw term

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
end;











