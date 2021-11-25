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
  let rec all (l : 'a option list) : 'a list option =
    match l with
    | [] -> Some []
    | x :: xs ->
        Option.bind x (fun x -> Option.bind (all xs) (fun xs -> Some (x :: xs)))
end
