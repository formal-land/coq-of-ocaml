(** A monad to:
    * have a code without side-effects;
    * handle errors;
    * report as much errors as possible (many branches of the AST can be explored
      in parallel and errors of each branch are reported);
    * handle the current position in the source [Loc.t];
    * handle the current environment [Env.t]. *)

type import = Require of string * string | RequireImport of string

module Command = struct
  type 'a t =
    | GetConfiguration : Configuration.t t
    | GetDocumentation : string option t
    | GetEnv : Env.t t
    | GetEnvStack : Env.t list t
    | Raise : 'a * Error.Category.t * string -> 'a t
    | Use : import -> unit t
    | UseUnsafeFixpoint : unit t
end

module Wrapper = struct
  type t = EnvSet of Env.t | EnvStackPush | LocSet of Location.t
end

type 'a t =
  | Bind : 'b t * ('b -> 'a t) -> 'a t
  | Command of 'a Command.t
  | RetrieveUnsafeFixpoints : 'a t -> (bool * 'a) t
  | Return of 'a
  | Wrapper of Wrapper.t * 'a t

module Notations = struct
  let return (x : 'a) : 'a t = Return x
  let ( let* ) (x : 'a t) (f : 'a -> 'b t) : 'b t = Bind (x, f)
  let ( >>= ) (x : 'a t) (f : 'a -> 'b t) : 'b t = Bind (x, f)
  let ( >> ) (x : 'a t) (y : 'b t) : 'b t = Bind (x, fun () -> y)
  let get_configuration : Configuration.t t = Command Command.GetConfiguration
  let get_documentation : string option t = Command Command.GetDocumentation
  let get_env : Env.t t = Command Command.GetEnv
  let get_env_stack : Env.t list t = Command Command.GetEnvStack
  let set_env (env : Env.t) (x : 'a t) : 'a t = Wrapper (Wrapper.EnvSet env, x)

  let set_loc (loc : Location.t) (x : 'a t) : 'a t =
    Wrapper (Wrapper.LocSet loc, x)

  let push_env (x : 'a t) : 'a t = Wrapper (Wrapper.EnvStackPush, x)

  let raise (value : 'a) (category : Error.Category.t) (message : string) : 'a t
      =
    Command (Command.Raise (value, category, message))

  let use (import : import) : unit t = Command (Command.Use import)
  let use_unsafe_fixpoint : unit t = Command Command.UseUnsafeFixpoint

  let retrieve_unsafe_fixpoints (x : 'a t) : (bool * 'a) t =
    RetrieveUnsafeFixpoints x
end

module List = struct
  open Notations

  let rec concat_map (f : 'a -> 'b list t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun x ->
        concat_map f l >>= fun l -> return (x @ l)

  let rec filter (f : 'a -> bool t) (l : 'a list) : 'a list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun is_valid ->
        filter f l >>= fun l -> if is_valid then return (x :: l) else return l

  let rec filter_map (f : 'a -> 'b option t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l -> (
        f x >>= fun x ->
        filter_map f l >>= fun l ->
        match x with None -> return l | Some x -> return (x :: l))

  let rec fold_left (f : 'a -> 'b -> 'a t) (accumulator : 'a) (l : 'b list) :
      'a t =
    match l with
    | [] -> return accumulator
    | x :: l -> f accumulator x >>= fun accumulator -> fold_left f accumulator l

  let rec fold_right (f : 'b -> 'a -> 'a t) (l : 'b list) (accumulator : 'a) :
      'a t =
    match l with
    | [] -> return accumulator
    | x :: l ->
        fold_right f l accumulator >>= fun accumulator -> f x accumulator

  let rec iter (f : 'a -> unit t) (l : 'a list) : unit t =
    match l with [] -> return () | x :: l -> f x >> iter f l

  let rec map (f : 'a -> 'b t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
        f x >>= fun x ->
        map f l >>= fun l -> return (x :: l)

  let rec lesser_and_greater (compare : 'a -> 'a -> int t) (x : 'a)
      (l : 'a list) : ('a list * 'a list) t =
    match l with
    | [] -> return ([], [])
    | y :: l ->
        compare y x >>= fun comparison ->
        lesser_and_greater compare x l >>= fun (lesser, greater) ->
        if comparison < 0 then return (y :: lesser, greater)
        else if comparison > 0 then return (lesser, y :: greater)
        else return (lesser, greater)

  let rec sort_uniq (compare : 'a -> 'a -> int t) (l : 'a list) : 'a list t =
    match l with
    | [] -> return []
    | head :: tail ->
        lesser_and_greater compare head tail >>= fun (lesser, greater) ->
        sort_uniq compare lesser >>= fun lesser ->
        sort_uniq compare greater >>= fun greater ->
        return (lesser @ [ head ] @ greater)
end
