module Result = struct
  type 'a t = {
    errors: Error.t list;
    value: 'a;
  }
end

module Interpret = struct
  type 'a t = Env.t -> Loc.t -> 'a Result.t
end

module Command = struct
  let eval (type a) (command : a Monad.Command.t) : a Interpret.t =
    fun env loc ->
      match command with
      | GetEnv -> { errors = []; value = env }
      | GetLoc -> { errors = []; value = loc }
      | Raise (value, category, message) -> { errors = [{ category; loc; message }]; value }
      | Warn message -> { errors = []; value = Error.warn loc message }
end

module Wrapper = struct
  let eval (wrapper : Monad.Wrapper.t) (interpret : 'a Interpret.t) : 'a Interpret.t =
    fun env loc ->
      match wrapper with
      | Env env ->
        let env = Envaux.env_of_only_summary env in
        interpret env loc
      | Loc loc -> interpret env loc
end

let rec eval : type a. a Monad.t -> a Interpret.t =
  fun x env loc ->
    match x with
    | Bind (x, f) ->
      let { Result.errors = errors_x; value = value_x } = eval x env loc in
      let { Result.errors = errors_y; value = value_y } = eval (f value_x) env loc in
      { errors = errors_y @ errors_x; value = value_y }
    | Command command -> Command.eval command env loc
    | Return value -> { errors = []; value }
    | Wrapper (wrapper, x) -> Wrapper.eval wrapper (eval x) env loc
