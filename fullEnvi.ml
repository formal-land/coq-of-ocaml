open SmartPrint

type 'a t = {
  vars : 'a Envi.t;
  leave_prefix_vars : Name.t -> 'a -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t
}

let pp (env : 'a t) : SmartPrint.t =
  !^ "vars:" ^^ nest (Envi.pp env.vars) ^^ newline ^^
  !^ "typs:" ^^ nest (Envi.pp env.typs) ^^ newline ^^
  !^ "descriptors:" ^^ nest (Envi.pp env.descriptors) ^^ newline ^^
  !^ "constructors:" ^^ nest (Envi.pp env.constructors) ^^ newline ^^
  !^ "fields:" ^^ nest (Envi.pp env.fields)

let empty (leave_prefix_vars : Name.t -> 'a -> 'a) : 'a t = {
  vars = Envi.empty;
  leave_prefix_vars = leave_prefix_vars;
  typs = Envi.empty;
  descriptors = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty
}

let add_var (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (v : 'a) (env : 'a t) : 'a t =
  { env with vars =
    Envi.add (PathName.of_name path base) visibility v env.vars }

let add_typ (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (env : 'a t) : 'a t =
  { env with typs =
    Envi.add (PathName.of_name path base) visibility () env.typs }

let add_descriptor (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (env : 'a t) : 'a t =
  { env with descriptors =
    Envi.add (PathName.of_name path base) visibility () env.descriptors }

let add_exception (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (env : unit t) : unit t =
  env
  |> add_descriptor path base visibility
  |> add_var path ("raise_" ^ base) visibility ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (visibility : Envi.Visibility.t)
  (env : Effect.Type.t t) : Effect.Type.t t =
  let env = add_descriptor path base visibility env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        id
        (Envi.bound_name Loc.Unknown (PathName.of_name path base) env.descriptors),
      Effect.Type.Pure) in
  add_var path ("raise_" ^ base) visibility effect_typ env

let add_constructor (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (env : 'a t) : 'a t =
  { env with constructors =
    Envi.add (PathName.of_name path base) visibility () env.constructors }

let add_field (path : Name.t list) (base : Name.t)
  (visibility : Envi.Visibility.t) (env : 'a t) : 'a t =
  { env with fields =
    Envi.add (PathName.of_name path base) visibility () env.fields }

let enter_module (env : 'a t) : 'a t =
  { vars = Envi.enter_module env.vars;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.enter_module env.typs;
    descriptors = Envi.enter_module env.descriptors;
    constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields }

let leave_module (module_name : Name.t) (env : 'a t) : 'a t = 
  let leave_prefix_unit = fun _ () -> () in
  { vars = Envi.leave_module env.vars env.leave_prefix_vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.leave_module env.typs leave_prefix_unit module_name;
    descriptors =
      Envi.leave_module env.descriptors leave_prefix_unit module_name;
    constructors =
      Envi.leave_module env.constructors leave_prefix_unit module_name;
    fields = Envi.leave_module env.fields leave_prefix_unit module_name }

let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
  { vars = Envi.open_module env.vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.open_module env.typs module_name;
    descriptors = Envi.open_module env.descriptors module_name;
    constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name }