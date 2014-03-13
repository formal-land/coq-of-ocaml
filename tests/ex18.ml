let r = ref 12

let plus_one _ =
  !r + 1

let s = ref "Hi"

let fail _ = failwith !s

let reset _ =
  r := 0

let incr _ =
  r := !r + 1