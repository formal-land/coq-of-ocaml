let n1 =
  let m = 12 in
  let n1 = m[@coq_type_annotation] in
  n1

let n2 =
  let p1 c = c (fun x y -> x) in
  let c = (fun f -> f 12 23) in
  p1 c
