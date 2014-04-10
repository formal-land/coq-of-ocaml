type 'a t = {
  vars : 'a Envi.t;
  close_lift_vars : 'a -> Name.t -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t
}

let empty (close_lift_vars : 'a -> Name.t -> 'a) : 'a t = {
  vars = Envi.empty;
  close_lift_vars = close_lift_vars;
  typs = Envi.empty;
  descriptors = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty;
}

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t) : 'a t =
  { env with vars = Envi.add (PathName.of_name path base) v env.vars }

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
  { env with descriptors = Envi.add (PathName.of_name path base) () env.descriptors }

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  env
  |> add_descriptor path base
  |> add_var path ("raise_" ^ base) ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (loc : Loc.t) (env : Effect.Type.t t) : Effect.Type.t t =
  let env = add_descriptor path base env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        loc
        (Envi.bound_name (PathName.of_name path base) env.descriptors),
      Effect.Type.Pure) in
  add_var path ("raise_" ^ base) effect_typ env

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
  { env with constructors = Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
  { env with fields = Envi.add (PathName.of_name path base) () env.fields }

let open_module (env : 'a t) : 'a t = {
  vars = Envi.open_module env.vars;
  close_lift_vars = env.close_lift_vars;
  typs = Envi.open_module env.typs;
  descriptors = Envi.open_module env.descriptors;
  constructors = Envi.open_module env.constructors;
  fields = Envi.open_module env.fields
}

let close_module (env : 'a t) (name : Name.t) : 'a t = 
  let close_lift_unit = fun _ _ -> () in
  {
    vars = Envi.close_module env.vars env.close_lift_vars name;
    close_lift_vars = env.close_lift_vars;
    typs = Envi.close_module env.typs close_lift_unit name;
    descriptors = Envi.close_module env.descriptors close_lift_unit name;
    constructors = Envi.close_module env.constructors close_lift_unit name;
    fields = Envi.close_module env.fields close_lift_unit name
  }