(** Open *)

module M = struct
  let f _ = failwith "failure"
end

module N = struct
  let f _ = assert false
  let x = try f () with Assert_failure _ -> ()
  open M
  let y = try f () with Failure _ -> ()
end

let b = try N.f () with Assert_failure _ -> ()
open N
let b' = try N.f () with Assert_failure _ -> ()