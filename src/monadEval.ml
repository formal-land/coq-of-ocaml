type comments = (string * Location.t) list

module Import = struct
  type t = {
    base : string;
    import : bool;
    mli : bool;
    name : string;
  }

  let merge (imports1 : t list) (imports2 : t list) : t list =
    List.sort_uniq
      (fun
        { base = base1; import = import1; mli = mli1; name = name1 }
        { base = base2; import = import2; mli = mli2; name = name2 } ->
        compare
          (not import1, base1, name1, mli1)
          (not import2, base2, name2, mli2)
      )
      (imports1 @ imports2)
end

module Result = struct
  type 'a t = {
    errors : Error.t list;
    imports : Import.t list;
    value : 'a;
  }

  let success (value : 'a) : 'a t = {
    errors = [];
    imports = [];
    value;
  }
end

module EnvStack = struct
  type t = Env.t list

  let init : t = []
end

module Context = struct
  type t = {
    comments : comments;
    configuration : Configuration.t;
    env : Env.t;
    env_stack : EnvStack.t;
    loc : Location.t;
  }

  let init
    (comments : comments)
    (configuration : Configuration.t)
    (initial_env : Env.t)
    (initial_loc : Location.t)
    : t = {
    comments;
    configuration;
    env = initial_env;
    env_stack = [];
    loc = initial_loc;
  }
end

module Interpret = struct
  type 'a t = Context.t -> 'a Result.t
end

module Command = struct
  open Monad.Command

  let eval (type a) (command : a t) : a Interpret.t =
    fun context ->
      match command with
      | GetConfiguration -> Result.success context.configuration
      | GetDocumentation ->
        let (documentation, _) =
          Ocamldoc.associate_comment context.comments context.loc context.loc in
        Result.success documentation
      | GetEnv -> Result.success context.env
      | GetEnvStack -> Result.success context.env_stack
      | Raise (value, category, message) ->
        let result = Result.success value in
        let errors =
          let error_id = Error.Category.to_id category in
          let is_valid_error =
            not (
              Configuration.is_category_in_error_blacklist
                context.configuration error_id
            ) &&
            not (
              Configuration.is_message_in_error_blacklist
                context.configuration message
            ) in
          if is_valid_error then
            [{ Error.category; loc = Loc.of_location context.loc; message }]
          else
            [] in
        { result with errors }
      | Use (import, base, name) ->
        let result = Result.success () in
        let mli = Configuration.is_require_mli context.configuration name in
        { result with imports = [{ Import.base; import; mli; name }] }
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

let rec eval : type a. a Monad.t -> a Interpret.t =
  fun x context ->
    match x with
    | Monad.Bind (x, f) ->
      let { Result.errors = errors_x; imports = imports_x; value = value_x } =
        eval x context in
      let { Result.errors = errors_y; imports = imports_y; value = value_y } =
        eval (f value_x) context in
      {
        errors = errors_y @ errors_x;
        imports = Import.merge imports_x imports_y;
        value = value_y
      }
    | Monad.Command command -> Command.eval command context
    | Monad.Return value -> Result.success value
    | Monad.Wrapper (wrapper, x) ->
      Wrapper.eval wrapper (eval x) context
