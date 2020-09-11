module type Sig = sig
  type 'a t = {
    x : int;
    y : int;
    label : 'a;
  }

  val v : string t
end

module M : Sig = struct
  type 'a t = {
    x : int;
    y : int;
    label : 'a;
  }

  let v = { x = 0; y = 1; label = "hi" }
end

let v = M.v

let s = M.v.label
