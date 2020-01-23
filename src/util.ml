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

module Option = struct
  let bind (x : 'a option) (f : 'a -> 'b option) : 'b option =
    match x with
    | None -> None
    | Some x -> f x

  let map (x : 'a option) (f : 'a -> 'b) : 'b option =
    match x with
    | None -> None
    | Some x -> Some (f x)

  let rec all (l : 'a option list) : 'a list option =
    match l with
    | [] -> Some []
    | x :: xs ->
      bind x (fun x ->
        bind (all xs) (fun xs ->
          Some (x :: xs)
        )
      )
end
