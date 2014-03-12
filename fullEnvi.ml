type 'a t = {
  vars : 'a Envi.t;
  lift_vars : 'a -> Name.t -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t
}

let open_module (env : 'a t) : 'a t = {
  vars = Envi.open_module env.vars;
  lift_vars = env.lift_vars;
  typs = Envi.open_module env.typs;
  descriptors = Envi.open_module env.descriptors;
  constructors = Envi.open_module env.constructors;
  fields = Envi.open_module env.fields
}

let close_module (env : 'a t) (name : Name.t) : 'a t = 
  let lift_unit = fun _ _ -> () in
  {
    vars = Envi.close_module env.vars env.lift_vars name;
    lift_vars = env.lift_vars;
    typs = Envi.close_module env.typs lift_unit name;
    descriptors = Envi.close_module env.descriptors lift_unit name;
    constructors = Envi.close_module env.constructors lift_unit name;
    fields = Envi.close_module env.fields lift_unit name
  }