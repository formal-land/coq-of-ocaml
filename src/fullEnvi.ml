open SmartPrint

type 'a t = {
  vars : 'a Envi.t;
  leave_prefix_vars : Name.t -> 'a -> 'a;
  typs : unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t }

let pp (env : 'a t) : SmartPrint.t =
  group (
    !^ "vars:" ^^ nest (Envi.pp env.vars) ^^ newline ^^
    !^ "typs:" ^^ nest (Envi.pp env.typs) ^^ newline ^^
    !^ "constructors:" ^^ nest (Envi.pp env.constructors) ^^ newline ^^
    !^ "fields:" ^^ nest (Envi.pp env.fields))

let empty (leave_prefix_vars : Name.t -> 'a -> 'a) : 'a t = {
  vars = Envi.empty;
  leave_prefix_vars = leave_prefix_vars;
  typs = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty }

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
  : 'a t =
  { env with vars = Envi.add (PathName.of_name path base) v env.vars }

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with constructors =
    Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with fields =
    Envi.add (PathName.of_name path base) () env.fields }

let enter_module (env : 'a t) : 'a t =
  { vars = Envi.enter_module env.vars;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.enter_module env.typs;
    constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields }

let leave_module (module_name : Name.t) (env : 'a t) : 'a t =
  let leave_prefix_unit = fun _ () -> () in
  { vars = Envi.leave_module env.vars env.leave_prefix_vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.leave_module env.typs leave_prefix_unit module_name;
    constructors =
      Envi.leave_module env.constructors leave_prefix_unit module_name;
    fields = Envi.leave_module env.fields leave_prefix_unit module_name }

let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
  { vars = Envi.open_module env.vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.open_module env.typs module_name;
    constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name }
