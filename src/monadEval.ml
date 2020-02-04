module Result = struct
  type 'a t = {
    errors: Error.t list;
    value: 'a;
  }
end

module LocalEnv = struct
  type t = {
    inner : Env.t option;
    outer : Env.t option;
  }

  let init : t = {
    inner = None;
    outer = None;
  }
end

module Interpret = struct
  type 'a t = Env.t -> Loc.t -> LocalEnv.t -> 'a Result.t
end

module Command = struct
  open Monad.Command

  let eval (type a) (file_name : string) (command : a t) : a Interpret.t =
    fun env loc scoping_env ->
      match command with
      | GetEnv -> { Result.errors = []; value = env }
      | GetLoc -> { errors = []; value = loc }
      | GetScopingEnv is_inner ->
        {
          errors = [];
          value = if is_inner then scoping_env.inner else scoping_env.outer;
        }
      | Raise (value, category, message) ->
        { errors = [{ category; loc; message }]; value }
      | Warn message ->
        { errors = []; value = Error.warn file_name loc message }
end

module Wrapper = struct
  let eval
    (wrapper : Monad.Wrapper.t)
    (interpret : 'a Interpret.t)
    : 'a Interpret.t =
    fun env loc scoping_env ->
      match wrapper with
      | Env env -> interpret env loc scoping_env
      | Loc loc -> interpret env loc scoping_env
      | ScopingEnv is_inner ->
        let scoping_env =
          if is_inner then
            { scoping_env with inner = Some env }
          else
            { scoping_env with outer = Some env } in
        interpret env loc scoping_env
end

let rec eval : type a. string -> a Monad.t -> a Interpret.t =
  fun file_name x env loc scoping_env ->
    match x with
    | Monad.Bind (x, f) ->
      let { Result.errors = errors_x; value = value_x } =
        eval file_name x env loc scoping_env in
      let { Result.errors = errors_y; value = value_y } =
        eval file_name (f value_x) env loc scoping_env in
      { errors = errors_y @ errors_x; value = value_y }
    | Monad.Command command ->
      Command.eval file_name command env loc scoping_env
    | Monad.Return value -> { errors = []; value }
    | Monad.Wrapper (wrapper, x) ->
      Wrapper.eval wrapper (eval file_name x) env loc scoping_env
