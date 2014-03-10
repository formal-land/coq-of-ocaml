type 'a t = {
  vars : 'a Envi.t;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t
}

let open_module (env : 'a t) : 'a t = {
  vars = Envi.open_module env.vars;
  typs = Envi.open_module env.typs;
  descriptors = Envi.open_module env.descriptors;
  constructors = Envi.open_module env.constructors;
}

let close_module (env : 'a t) (lift : 'a -> Name.t -> 'a) (name : Name.t)
  : 'a t = 
  let lift_unit = fun _ _ -> () in
  {
    vars = Envi.close_module env.vars lift name;
    typs = Envi.close_module env.typs lift_unit name;
    descriptors = Envi.close_module env.descriptors lift_unit name;
    constructors = Envi.close_module env.constructors lift_unit name;
  }