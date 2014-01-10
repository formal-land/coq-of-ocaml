(** The initially opened module. *)
open Structure

module Helpers = struct
  let from_simple_form (name : string) (free_type_vars : string list)
    (args : (string * Type.t) list) (body : Exp.t * Type.t) (is_rec : bool)
    : Structure.t =
    Value {
      Value.name = Name.of_string name;
      free_type_vars = List.map Name.of_string free_type_vars;
      args = args |> List.map (fun (x, t) -> (Name.of_string x, t));
      body = body;
      is_rec = Recursivity.New is_rec }
  
  let ev (x : string) : Exp.t =
    Exp.Variable (PathName.of_name [] @@ Name.of_string x)

  let app (f : string) (xs : string list) : Exp.t =
    Exp.Apply (ev f, List.map ev xs)

  let tv (x : string) : Type.t =
    Type.Variable (Name.of_string x)
end

open Helpers

let pervasives : Structure.t =
  Module (Name.of_string "Pervasives", [
    from_simple_form "not" [] [("b", tv "bool")]
      (app "negb" ["b"], tv "bool") false;
    from_simple_form "&&" [] [("b1", tv "bool"); ("b2", tv "bool")]
      (app "andb" ["b1"; "b2"], tv "bool") false;
    from_simple_form "||" [] [("b1", tv "bool"); ("b2", tv "bool")]
      (app "orb" ["b1"; "b2"], tv "bool") false])