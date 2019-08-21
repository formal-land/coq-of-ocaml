open SmartPrint

type t = {
  constructors : unit Envi.t;
  fields : unit Envi.t;
  signatures : Name.t list Envi.t;
  typs : unit Envi.t;
  vars : unit Envi.t }

let empty : t = {
  constructors = Envi.empty;
  fields = Envi.empty;
  signatures = Envi.empty;
  typs = Envi.empty;
  vars = Envi.empty }

let add_constructor (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with constructors =
    Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with fields =
    Envi.add (PathName.of_name path base) () env.fields }

let add_signature (path : Name.t list) (base : Name.t) (typ_params : Name.t list) (env : t) : t =
  { env with signatures = Envi.add (PathName.of_name path base) typ_params env.signatures }

let add_typ (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_var (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with vars = Envi.add (PathName.of_name path base) () env.vars }

let enter_module (env : t) : t =
  { constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields;
    signatures = Envi.enter_module env.signatures;
    typs = Envi.enter_module env.typs;
    vars = Envi.enter_module env.vars }

let leave_module (module_name : Name.t) (env : t) : t =
  { constructors = Envi.leave_module env.constructors module_name;
    fields = Envi.leave_module env.fields module_name;
    signatures = Envi.leave_module env.signatures module_name;
    typs = Envi.leave_module env.typs module_name;
    vars = Envi.leave_module env.vars module_name }

let open_module (module_name : Name.t list) (env : t) : t =
  { constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name;
    signatures = Envi.open_module env.signatures module_name;
    typs = Envi.open_module env.typs module_name;
    vars = Envi.open_module env.vars module_name }
