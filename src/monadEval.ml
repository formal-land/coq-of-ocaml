module Result = struct
  type 'a t =
    | Error of (Loc.t * string) list
    | Success of 'a
end

module Interpret = struct
  type 'a t = Env.t -> Loc.t -> 'a Result.t
end

module Command = struct
  let eval (type a) (command : a Monad.Command.t) : a Interpret.t =
    fun env loc ->
      match command with
      | GetEnv -> Success env
      | GetLoc -> Success loc
      | Raise message -> Error [(loc, message)]
      | Warn message -> Success (Error.warn loc message)
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
    | Monad.All (x1, x2) ->
      begin match (eval x1 env loc, eval x2 env loc) with
      | Error errors1, Error errors2 -> Error (errors1 @ errors2)
      | (Error _ as result1), Success _ -> result1
      | Success _, (Error _ as result2) -> result2
      | Success success1, Success success2 -> Success (success1, success2)
      end
    | Bind (x, f) ->
      begin match eval x env loc with
      | Error _ as result -> result
      | Success success -> eval (f success) env loc
      end
    | Command command -> Command.eval command env loc
    | Return value -> Success value
    | Wrapper (wrapper, x) -> Wrapper.eval wrapper (eval x) env loc
