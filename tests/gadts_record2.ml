type _ exp =
  | E_Int : int -> int exp
[@@coq_tag_gadt]

type 'a my_record = {
  x : 'a exp;
  y : int
}
[@@coq_tag_gadt]

let get_x : type a. a my_record -> a exp =
  function r ->
    let { x; y } = r in
    x
