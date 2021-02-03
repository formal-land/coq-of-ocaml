module File = struct
  let write (file_name : string) (file_content : string) : unit =
    let output_channel = open_out file_name in
    output_string output_channel file_content;
    close_out output_channel
end

module List = struct
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

(* Copied from https://gist.github.com/NicolasT/65dad40b203da7c65b4c *)
module Either = struct
    type ('a, 'b) t = Left of 'a | Right of 'b

    (** Constructor functions *)
    let left a = Left a
    let right b = Right b

    let either l r = function
      | Left v -> l v
      | Right v -> r v

    (** Bifunctor interface *)
    let bimap l r = either (fun v -> left (l v)) (fun v -> right (r v))

    external id : 'a -> 'a = "%identity"
    let const v = fun _ -> v

    (** Functor interface *)
    let map f = bimap id f
    let (<$>) = map
    let map_left f = bimap f id

    (** Monadic interface *)
    let bind m k = either left k m

    let return = right
    let (>>=) = bind
    let throw = left

    (** Applicative interface *)
    let pure = return
    let apply f v = f >>= fun f' -> v >>= fun v' -> pure (f' v')
    let (<*>) = apply

    (** Turn a function result in a value or an error *)
    let try_ f = try pure (f ()) with exn -> throw exn

    (** Predicates *)
    let is_left v = either (const true) (const false) v
    let is_right v = either (const false) (const true) v

    let to_string l r = either
                            (fun v -> Printf.sprintf "Left (%s)" (l v))
                            (fun v -> Printf.sprintf "Right (%s)" (r v))

    (** Extract a value of raise an exception *)
    let error v = either (fun e -> raise e) id v

    (** Silence into an option *)
    let hush v = either (const None) (fun v' -> Some v') v

    (** Expand from an option *)
    let note e = function
      | None -> Left e
      | Some v -> Right v

    (** Catamorphism *)
    let fold f z = either (const z) (fun v -> f v z)

end
