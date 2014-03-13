type 'a t = {
  vars : 'a Envi.t;
  close_lift_vars : 'a -> Name.t -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t
}

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