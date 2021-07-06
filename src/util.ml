module File = struct
  let write (file_name : string) (file_content : string) : unit =
    let output_channel = open_out file_name in
    output_string output_channel file_content;
    close_out output_channel
end

module List = struct
  let concat_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
    List.concat (List.map f l)

  let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
    match l with
    | [] -> []
    | x :: l ->
      begin match f x with
      | None -> filter_map f l
      | Some x -> x :: filter_map f l
      end

  let rec find_map (f : 'a -> 'b option) (l : 'a list) : 'b option =
    match l with
    | [] -> None
    | x :: l ->
      begin match f x with
      | None -> find_map f l
      | Some _ as y -> y
      end

  let rec split3 = function
      [] -> ([], [], [])
    | (x,y, z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)

  let rec last (l : 'a list) : 'a =
    match l with
    | [] -> failwith "Empty List"
    | [x] -> x
    | x :: xs -> last xs

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
