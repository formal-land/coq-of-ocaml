(** A monad to:
    * have a code without side-effects;
    * handle errors;
    * report as much errors as possible (many branches of the AST can be explored
      in parallel and errors of each branch are reported);
    * handle the current position in the source [Loc.t];
    * handle the current environment [Env.t]. *)

module Command = struct
  type 'a t =
    | GetEnv : Env.t t
    | GetLoc : Loc.t t
    | Raise : string -> 'a t
end

module Wrapper = struct
  type t =
    | Env of Env.t
    | Loc of Loc.t
end

type 'a t =
  | All : 'a t * 'b t -> ('a * 'b) t
  | Bind : 'b t * ('b -> 'a t) -> 'a t
  | Command of 'a Command.t
  | Return of 'a
  | Wrapper of Wrapper.t * 'a t

let all (x1 : 'a t) (x2 : 'b t) : ('a * 'b) t =
  All (x1, x2)

let return (x : 'a) : 'a t =
  Return x

let (>>=) (x : 'a t) (f : 'a -> 'b t) : 'b t =
  Bind (x, f)

let get_env : Env.t t =
  Command Command.GetEnv

let get_loc : Loc.t t =
  Command Command.GetLoc

let raise (message : string) : 'a t =
  Command (Command.Raise message)

let set_env (env : Env.t) (x : 'a t) : 'a t =
  Wrapper (Wrapper.Env env, x)

let set_loc (loc : Loc.t) (x : 'a t) : 'a t =
  Wrapper (Wrapper.Loc loc, x)
