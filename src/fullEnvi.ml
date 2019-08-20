open SmartPrint

type t = {
  vars : unit Envi.t;
  typs : unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t }

let empty : t = {
  vars = Envi.empty;
  typs = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty }

let add_var (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with vars = Envi.add (PathName.of_name path base) () env.vars }

let add_typ (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_constructor (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with constructors =
    Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : t) : t =
  { env with fields =
    Envi.add (PathName.of_name path base) () env.fields }

let enter_module (env : t) : t =
  { vars = Envi.enter_module env.vars;
    typs = Envi.enter_module env.typs;
    constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields }

let leave_module (module_name : Name.t) (env : t) : t =
  { vars = Envi.leave_module env.vars module_name;
    typs = Envi.leave_module env.typs module_name;
    constructors = Envi.leave_module env.constructors module_name;
    fields = Envi.leave_module env.fields module_name }

let open_module (module_name : Name.t list) (env : t) : t =
  { vars = Envi.open_module env.vars module_name;
    typs = Envi.open_module env.typs module_name;
    constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name }
