module List = struct
  let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
    match l with
    | [] -> []
    | x :: l ->
      begin match f x with
      | None -> filter_map f l
      | Some x -> x :: filter_map f l
      end
end
