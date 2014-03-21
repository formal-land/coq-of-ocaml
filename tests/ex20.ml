(** Let-rec in another let-rec *)

let rec sums ls =
  let rec sum xs =
    match xs with
    | [] -> 0
    | x :: xs ->
      if x = 12 then
        match sums [[13]] with
        | x :: _ -> x - 1
        | _ -> 0
      else
        x + sum xs in
  match ls with
  | [] -> []
  | xs :: ls -> sum xs :: sums ls