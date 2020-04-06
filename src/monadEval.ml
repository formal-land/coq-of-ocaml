module Result = struct
  type 'a t = {
    errors: Error.t list;
    value: 'a;
  }
end

module EnvStack = struct
  type t = Env.t list

  let init : t = []
end

module Context = struct
  type t = {
    configuration : Configuration.t;
    env : Env.t;
    env_stack : EnvStack.t;
    loc : Loc.t;
  }

  let init
    (configuration : Configuration.t)
    (initial_env : Env.t)
    (initial_loc : Loc.t)
    : t = {
    configuration;
    env = initial_env;
    env_stack = [];
    loc = initial_loc
  }
end

module Interpret = struct
  type 'a t = Context.t -> 'a Result.t
end

module Command = struct
  open Monad.Command

  let eval (type a) (file_name : string) (command : a t) : a Interpret.t =
    fun context ->
      match command with
      | GetConfiguration -> { errors = []; value = context.configuration }
      | GetEnv -> { errors = []; value = context.env }
      | GetEnvStack -> { errors = []; value = context.env_stack }
      | GetLoc -> { errors = []; value = context.loc }
      | Raise (value, category, message) ->
        { errors = [{ category; loc = context.loc; message }]; value }
      | Warn message ->
        { errors = []; value = Error.warn file_name context.loc message }
end

module Wrapper = struct
  let eval
    (wrapper : Monad.Wrapper.t)
    (interpret : 'a Interpret.t)
    : 'a Interpret.t =
    fun context ->
      match wrapper with
      | EnvSet env -> interpret {context with env}
      | EnvStackPush ->
        interpret {context with env_stack = context.env :: context.env_stack}
      | LocSet loc -> interpret {context with loc}
end

let rec eval : type a. string -> a Monad.t -> a Interpret.t =
  fun file_name x context ->
    match x with
    | Monad.Bind (x, f) ->
      let { Result.errors = errors_x; value = value_x } =
        eval file_name x context in
      let { Result.errors = errors_y; value = value_y } =
        eval file_name (f value_x) context in
      { errors = errors_y @ errors_x; value = value_y }
    | Monad.Command command ->
      Command.eval file_name command context
    | Monad.Return value -> { errors = []; value }
    | Monad.Wrapper (wrapper, x) ->
      Wrapper.eval wrapper (eval file_name x) context
