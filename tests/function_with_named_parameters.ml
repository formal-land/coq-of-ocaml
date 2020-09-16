let option_value (x : 'a option) ~(default : 'a) : 'a =
  match x with
  | Some x -> x
  | None -> default

let option_zero = option_value ~default:0

let option_value_bis = option_value
