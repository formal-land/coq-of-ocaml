module Result = struct
  type 'a t = {
    errors: Error.t list;
    value: 'a;
  }
end

module Interpret = struct
  type 'a t =
    Env.t -> Loc.t -> Monad.LocalModules.t -> 'a Result.t * Monad.LocalModules.t
end

module Command = struct
  open Monad.Command

  let eval (type a) (file_name : string) (command : a t) : a Interpret.t =
    fun env loc local_modules ->
      match command with
      | AddLocalModule module_typ ->
        let local_modules =
          match Mtype.scrape env module_typ with
          | Mty_alias _ | Mty_ident _ | Mty_functor _ -> local_modules
          | Mty_signature signature -> signature :: local_modules in
        ({ errors = []; value = () }, local_modules)
      | GetEnv -> ({ Result.errors = []; value = env }, local_modules)
      | GetLoc -> ({ errors = []; value = loc }, local_modules)
      | GetLocalModules ->
        ({ errors = []; value = local_modules }, local_modules)
      | Raise (value, category, message) ->
        ({ errors = [{ category; loc; message }]; value }, local_modules)
      | Warn message ->
        (
          { errors = []; value = Error.warn file_name loc message },
          local_modules
        )
end

module Wrapper = struct
  let eval
    (wrapper : Monad.Wrapper.t)
    (interpret : 'a Interpret.t)
    : 'a Interpret.t =
    fun env loc local_modules ->
      match wrapper with
      | Env env -> interpret env loc local_modules
      | Loc loc -> interpret env loc local_modules
      | LocalModulesOpenScope ->
        let (result, _) = interpret env loc [] in
        (result, [])
end

let rec eval : type a. string -> a Monad.t -> a Interpret.t =
  fun file_name x env loc local_modules ->
    match x with
    | Monad.Bind (x, f) ->
      let ({ Result.errors = errors_x; value = value_x }, local_modules) =
        eval file_name x env loc local_modules in
      let ({ Result.errors = errors_y; value = value_y }, local_modules) =
        eval file_name (f value_x) env loc local_modules in
      ({ errors = errors_y @ errors_x; value = value_y }, local_modules)
    | Monad.Command command ->
      Command.eval file_name command env loc local_modules
    | Monad.Return value -> ({ errors = []; value }, local_modules)
    | Monad.Wrapper (wrapper, x) ->
      Wrapper.eval wrapper (eval file_name x) env loc local_modules
