module File = struct
  let write (file_name : string) (file_content : string) : unit =
    let output_channel = open_out file_name in
    output_string output_channel file_content;
    close_out output_channel
end

module List = struct
  let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z) :: l ->
        let rx, ry, rz = split3 l in
        (x :: rx, y :: ry, z :: rz)

  let rec last (l : 'a list) : 'a =
    match l with [] -> failwith "Empty List" | [ x ] -> x | _ :: xs -> last xs
end

module Option = struct
  let merge (o1 : 'a option) (o2 : 'a option) (merge : 'a -> 'a -> 'a) :
      'a option =
    match (o1, o2) with
    | None, _ -> o2
    | _, None -> o1
    | Some v1, Some v2 -> Some (merge v1 v2)

  let rec all (l : 'a option list) : 'a list option =
    match l with
    | [] -> Some []
    | x :: xs ->
        Option.bind x (fun x -> Option.bind (all xs) (fun xs -> Some (x :: xs)))
end

module String = struct
  let starts_with prefix s =
    String.length prefix <= String.length s
    && String.sub s 0 (String.length prefix) = prefix
end
