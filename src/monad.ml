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
    | Raise : 'a * Error.Category.t * string -> 'a t
    | Warn : string -> unit t
end

module Wrapper = struct
  type t =
    | Env of Env.t
    | Loc of Loc.t
end

type 'a t =
  | Bind : 'b t * ('b -> 'a t) -> 'a t
  | Command of 'a Command.t
  | Return of 'a
  | Wrapper of Wrapper.t * 'a t

module Notations = struct
  let return (x : 'a) : 'a t =
    Return x

  let (>>=) (x : 'a t) (f : 'a -> 'b t) : 'b t =
    Bind (x, f)

  let (>>) (x : 'a t) (y : 'b t) : 'b t =
    Bind (x, fun () -> y)

  let get_env : Env.t t =
    Command Command.GetEnv

  let get_loc : Loc.t t =
    Command Command.GetLoc

  let set_env (env : Env.t) (x : 'a t) : 'a t =
    Wrapper (Wrapper.Env env, x)

  let set_loc (loc : Loc.t) (x : 'a t) : 'a t =
    Wrapper (Wrapper.Loc loc, x)

  let raise (value : 'a) (category : Error.Category.t) (message : string) : 'a t =
    Command (Command.Raise (value, category, message))

  let warn (message : string) : 'a t =
    Command (Command.Warn message)
end

module List = struct
  open Notations

  let rec filter_map (f : 'a -> 'b option t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
      f x >>= fun x ->
      filter_map f l >>= fun l ->
      begin match x with
      | None -> return l
      | Some x -> return (x :: l)
      end

  let rec fold_left (f : 'a -> 'b -> 'a t) (accumulator : 'a) (l : 'b list) : 'a t =
    match l with
    | [] -> return accumulator
    | x :: l ->
      f accumulator x >>= fun accumulator ->
      fold_left f accumulator l

  let rec iter (f : 'a -> unit t) (l :'a list) : unit t =
    match l with
    | [] -> return ()
    | x :: l -> f x >> iter f l

  let rec map (f : 'a -> 'b t) (l :'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: l ->
      f x >>= fun x ->
      map f l >>= fun l ->
      return (x :: l)
end
