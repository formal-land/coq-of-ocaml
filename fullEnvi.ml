open SmartPrint

type ('a, 's) t = {
  vars : 'a Envi.t;
  leave_prefix_vars : Name.t -> 'a -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t;
  signatures : 's list Envi.t;
  leave_prefix_signatures : Name.t -> 's list -> 's list
}

let pp (env : ('a, 's) t) : SmartPrint.t =
  group (
    !^ "vars:" ^^ nest (Envi.pp env.vars) ^^ newline ^^
    !^ "typs:" ^^ nest (Envi.pp env.typs) ^^ newline ^^
    !^ "descriptors:" ^^ nest (Envi.pp env.descriptors) ^^ newline ^^
    !^ "constructors:" ^^ nest (Envi.pp env.constructors) ^^ newline ^^
    !^ "fields:" ^^ nest (Envi.pp env.fields) ^^ newline ^^
    !^ "signatures:" ^^ nest (Envi.pp env.signatures))

let empty (leave_prefix_vars : Name.t -> 'a -> 'a)
  (leave_prefix_signatures : Name.t -> 's list -> 's list): ('a, 's) t = {
  vars = Envi.empty;
  leave_prefix_vars = leave_prefix_vars;
  typs = Envi.empty;
  descriptors = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty;
  signatures = Envi.empty;
  leave_prefix_signatures = leave_prefix_signatures
}

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : ('a, 's) t)
  : ('a, 's) t =
  { env with vars = Envi.add (PathName.of_name path base) v env.vars }

let add_typ (path : Name.t list) (base : Name.t) (env : ('a, 's) t)
  : ('a, 's) t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_descriptor (path : Name.t list) (base : Name.t) (env : ('a, 's) t)
  : ('a, 's) t =
  { env with descriptors =
    Envi.add (PathName.of_name path base) () env.descriptors }

let add_exception (path : Name.t list) (base : Name.t) (env : (unit, 's) t) : (unit, 's) t =
  env
  |> add_descriptor path base
  |> add_var path ("raise_" ^ base) ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (env : (Effect.Type.t, 's) t)
  : (Effect.Type.t, 's) t =
  let env = add_descriptor path base env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        id
        (Envi.bound_name Loc.Unknown (PathName.of_name path base) env.descriptors),
      Effect.Type.Pure) in
  add_var path ("raise_" ^ base) effect_typ env

let add_constructor (path : Name.t list) (base : Name.t) (env : ('a, 's) t)
  : ('a, 's) t =
  { env with constructors =
    Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : ('a, 's) t)
  : ('a, 's) t =
  { env with fields =
    Envi.add (PathName.of_name path base) () env.fields }

let add_signature (path : Name.t list) (base : Name.t) (decls : 's list)
  (env : ('a, 's) t) : ('a, 's) t =
  { env with signatures =
    Envi.add (PathName.of_name path base) decls env.signatures }

let enter_module (env : ('a, 's) t) : ('a, 's) t =
  { vars = Envi.enter_module env.vars;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.enter_module env.typs;
    descriptors = Envi.enter_module env.descriptors;
    constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields;
    signatures = Envi.enter_module env.signatures;
    leave_prefix_signatures = env.leave_prefix_signatures }

let leave_module (module_name : Name.t) (env : ('a, 's) t) : ('a, 's) t = 
  let leave_prefix_unit = fun _ () -> () in
  { vars = Envi.leave_module env.vars env.leave_prefix_vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.leave_module env.typs leave_prefix_unit module_name;
    descriptors =
      Envi.leave_module env.descriptors leave_prefix_unit module_name;
    constructors =
      Envi.leave_module env.constructors leave_prefix_unit module_name;
    fields = Envi.leave_module env.fields leave_prefix_unit module_name;
    signatures =
      Envi.leave_module env.signatures env.leave_prefix_signatures module_name;
    leave_prefix_signatures = env.leave_prefix_signatures }

let open_module (module_name : Name.t list) (env : ('a, 's) t) : ('a, 's) t =
  { vars = Envi.open_module env.vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.open_module env.typs module_name;
    descriptors = Envi.open_module env.descriptors module_name;
    constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name;
    signatures = Envi.open_module env.signatures module_name;
    leave_prefix_signatures = env.leave_prefix_signatures }