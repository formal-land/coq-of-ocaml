(*external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply";;
external ( @@ ) : ('a -> 'b) -> 'a -> 'b = "%apply"*)

(* Separators. *)
module Break = struct
  (* A break can be a whitespace or a newline if the text has to be splited. *)
  type t =
    | Space
    | Newline
end

(* The internal representation of a document and the engine. *)
module Atom = struct
  (* An atom is the low-level tree describing a document. *)
  type t =
    | String of string * int * int
      (* A non-breaking string. It should be newlines free. Represented as a
          sub-string of an other string, with an offset and a length. *)
    | Break of Break.t (* A separator. *)
    | GroupOne of bool * t list
      (* A list of atoms. Only the necessary number of breaks are splited.
         The boolean is true if nesting is activated. *)
    | GroupAll of bool * t list
      (* A list of atoms. No or all the breaks are splited.
         The boolean is true if nesting is activated. *)
    | Indent of int * t (* Indents by [n] tabulations the atom. Can be negative. *)

  (* If we overflow a line. *)
  exception Overflow
  
  (* Print "at best" an atom [a] for a line width [width] and tabulation width [tab].
     [i] is the indentation level, [p] the current column position (in number
     of spaces), [last_break] the last break printed if any (so we can collapse
     spaces). It returns the same atom where spaces have been evaluated to
     newlines, the new current column position and the last break printed if any.
     Must succeed (no uncaught [Overflow] exception). *)
  let rec eval (width : int) (tab : int) (i : int) (a : t) (p : int) (last_break : Break.t option)
    : t * int * Break.t option =
    (* Eval "at best" a list of atoms splitting all the spaces. The flag [can_nest]
       sets if we indent when we break lines. *)
    let rec eval_list_all (width : int) (tab : int) (i : int) (_as : t list) (p : int)
      (last_break : Break.t option) (can_nest : bool)
      : t list * int * Break.t option =
      match _as with
      | [] -> (_as, p, last_break)
      | Break Break.Space :: _as ->
        (match last_break with
        | None ->
          let (_as, p, last_break) =
            eval_list_all width tab (if can_nest then i + tab else i) _as 0 (Some Break.Newline) false in
          if can_nest then
            ([Break Break.Newline; Indent (1, GroupAll (false, _as))], p, last_break)
          else
            (Break Break.Newline :: _as, p, last_break)
        | _ -> eval_list_all width tab i _as p last_break can_nest)
      | a :: _as ->
        let (a, p, last_break) = eval width tab i a p last_break in
        let (_as, p, last_break) = eval_list_all width tab i _as p last_break can_nest in
        (a :: _as, p, last_break) in

    (* Like [try_eval_flat] but for a list of atoms. *)
    let rec try_eval_list_flat (width : int) (tab : int) (i : int) (_as : t list) (p : int) (last_break : Break.t option)
      : int * Break.t option =
      (* Try to print an atom without evaluating the spaces. May raise [Overflow] if we
        overflow the line [width]. *)
      let rec try_eval_flat (width : int) (tab : int) (i : int) (a : t) (p : int) (last_break : Break.t option)
        : int * Break.t option =
        let try_return (p, last_break) =
          if p > width then
            raise Overflow
          else
            (p, last_break) in
        match a with
        | String (_, _, l) ->
          let p = match last_break with
            | Some Break.Newline -> p + i + l
            | _ -> p + l in
          try_return (p, None)
        | Break Break.Space ->
          (match last_break with
          | None -> try_return (p + 1, Some Break.Space)
          | _ -> try_return (p, last_break))
        | Break Break.Newline -> raise Overflow
        | GroupOne (can_nest, _as) ->
          let (p, last_break) = try_eval_list_flat width tab (i + tab) _as p last_break in
          (p, last_break)
        | GroupAll (can_nest, _as) ->
          let (p, last_break) = try_eval_list_flat width tab (i + tab) _as p last_break in
          (p, last_break)
        | Indent (_, a) -> try_eval_flat width tab i a p last_break in
      match _as with
      | [] -> (p, last_break)
      | a :: _as ->
        let (p, last_break) = try_eval_flat width tab i a p last_break in
        let (p, last_break) = try_eval_list_flat width tab i _as p last_break in
        (p, last_break) in

    (* Eval "at best" a list of atoms using the "split only when necessary" policy. The [can_fail]
       flag controls if we can raise an [Overflow], the [can_nest] if we can nest when we break,
       [in_nest] if we have already nested. *)
    let rec try_eval_list_one (width : int) (tab : int) (i : int) (_as : t list) (p : int)
      (last_break : Break.t option) (can_fail : bool) (can_nest : bool) (in_nest : bool)
      : t list * int * Break.t option =
      match _as with
      | [] -> (_as, p, last_break)
      | Break Break.Space :: _as ->
        (match last_break with
        | None ->
          (* If it is not possible in flat mode, switch back to "at best". *)
          (try let (_as, p, last_break) = try_eval_list_one width tab i _as (p + 1) (Some Break.Space) true can_nest in_nest in
            (Break Break.Space :: _as, p, last_break) with
          | Overflow ->
            let do_indent = can_nest && not in_nest in
            let (_as, p, last_break) = try_eval_list_one width tab (if do_indent then i + tab else i)
              _as 0 (Some Break.Newline) false can_nest can_nest in
            if do_indent then
              ([Break Break.Newline; Indent (1, GroupOne (false, _as))], p, last_break)
            else
              (Break Break.Newline :: _as, p, last_break))
        | _ -> try_eval_list_one width tab i _as p last_break can_fail can_nest in_nest)
      | Break Break.Newline :: _as ->
        let (_as, p, last_break) =
          (* If there is an explicit newline we always undo the nesting. *)
          if in_nest then
            try_eval_list_one width tab (i - tab) _as 0 (Some Break.Newline) false can_nest false
          else
            try_eval_list_one width tab i _as 0 (Some Break.Newline) false can_nest false in
        if in_nest then
          ([Break Break.Newline; Indent (- 1, GroupOne (false, _as))], p, last_break)
        else
          (Break Break.Newline :: _as, p, last_break)
      | a :: _as ->
        let (a, p, last_break) =
          (* If [Overflow] is possible we try in flat mode, else "at best". *)
          if can_fail then
            let (p, last_break) = try_eval_list_flat width tab i [a] p last_break in
            (a, p, last_break)
          else
            eval width tab i a p last_break in
        let (_as, p, last_break) = try_eval_list_one width tab i _as p last_break can_fail can_nest in_nest in
        (a :: _as, p, last_break) in

    match a with
    | String (_, _, l) ->
      let p = match last_break with
        | Some Break.Newline -> p + i + l
        | _ -> p + l in
      (a, p, None)
    | Break Break.Space ->
      (match last_break with
      | None -> (a, p + 1, Some Break.Space)
      | _ -> (a, p, last_break))
    | Break Break.Newline -> (a, 0, Some Break.Newline)
    | GroupOne (can_nest, _as) ->
      let (_as, p, last_break) = try_eval_list_one width tab i _as p last_break false can_nest false in
      (GroupOne (can_nest, _as), p, last_break)
    | GroupAll (can_nest, _as) ->
      let (_as, p, last_break) =
        try let (p, last_break) = try_eval_list_flat width tab (i + tab) _as p last_break in
          (_as, p, last_break) with
        | Overflow -> eval_list_all width i tab _as p last_break can_nest in
      (GroupAll (can_nest, _as), p, last_break)
    | Indent (n, a) ->
      let (a, p, last_break) = eval width tab (i + n * tab) a p last_break in
      (Indent (n, a), p, last_break)

  (* Evaluate the breaks with a maximal [width] per line and a tabulation width [tab]. *)
  let render (width : int) (tab : int) (_as : t list) : t =
    let (a, _, _) = eval width tab 0 (GroupOne (false, _as)) 0 (Some Break.Newline) in
    a
  
  (* A buffer eating trailing spaces. *)
  module NonTrailingBuffer = struct
    type t = {
      add_char : char -> unit;
      add_string : string -> unit;
      add_sub_string : string -> int -> int -> unit;
      nb_spaces : int }

    (* A new buffer. *)
    let make (add_char : char -> unit) (add_string : string -> unit)
      (add_sub_string : string -> int -> int -> unit) : t =
      {
        add_char = add_char;
        add_string = add_string;
        add_sub_string = add_sub_string;
        nb_spaces = 0 (* A number of spaces we may print if they are not trailing. *) }

    (* Forget previous spaces which appear to be trailing. *)
    let forget_spaces (b : t) : t =
      { b with nb_spaces = 0 }

    (* Spaces are not trailing: print all of them. *)
    let flush_spaces (b : t) : t =
      b.add_string (String.make b.nb_spaces ' ');
      forget_spaces b

    (* Indent by [i] spaces. By convention, indentation spaces are always
        printed, even one an empty line, to mark the indentation level. *)
    let indent (b : t) (i : int) : t =
      b.add_string (String.make i ' ');
      forget_spaces b

    (* Print a sub-string. *)
    let sub_string (b : t) (s : string) (o : int) (l : int) : t =
      b.add_sub_string s o l;
      flush_spaces b

    (* Add one space in the buffer. *)
    let space (b : t) : t =
      { b with nb_spaces = b.nb_spaces + 1 }

    (* Print a newline, with no trailing space before it. *)
    let newline (b : t) : t =
      b.add_char '\n';
      forget_spaces b
  end

  (* Write to something, given the [add_char] and [add_string] functions. *)
  let to_something (tab : int) (add_char : char -> unit) (add_string : string -> unit)
    (add_sub_string : string -> int -> int -> unit) (a : t) : unit =
    failwith "TODO"
    (* TODO: rewrite from the initial file *)
    (*let open NonTrailingBuffer in
    let rec aux b a i (last_break : Break.t option) : t * Break.t option =
      match a with
      | String (s, o, l) ->
        (*Printf.printf "<%d, %b>" i (last_break = Some Break.Newline);*)
        let b =
          if last_break = Some Break.Newline then
            indent b i
          else
            b in
        (sub_string b s o l, None)
      | Break Break.Space ->
        if last_break = None then
          (space b, Some Break.Space)
        else
          (b, last_break)
      | Break Break.Newline ->
        let b =
          if last_break = Some Break.Newline then
            indent b i
          else
            b in
        (newline b, Some Break.Newline)
      | GroupOne (_, _as) | GroupAll (_, _as) ->
        (*let last_break = ref last_break in
        _as |> List.iter (fun a ->
          last_break := aux a i !last_break);
        !last_break*)
      | Indent (n, a) -> aux a (i + n * tab) last_break in
    let b = make add_char add_string add_sub_string in
    ignore (aux b a 0 (Some Break.Newline))*)
end

(*
(* A document is a binary tree of atoms so that concatenation happens in O(1). *)
type t =
  | Empty
  | Leaf of Atom.t
  | Node of t * t

let empty : t = Empty

let string (s : string) : t =
  if s = "" then
    empty
  else
    Leaf (Atom.String (s, 0, String.length s))

let (!^) = string

let sub_string (s : string) (o : int) (l : int) : t =
  if l = 0 then
    empty
  else
    Leaf (Atom.String (s, o, l))

let space : t = Leaf (Atom.Break Break.Space)

let newline : t = Leaf (Atom.Break Break.Newline)

let append (d1 : t) (d2 : t) : t =
  Node (d1, d2)

let (^-^) = append

let concat_with_space (d1 : t) (d2 : t) : t =
  d1 ^-^ space ^-^ d2

let (^^) = concat_with_space

(* Convert a document, which is a tree of atoms, to a list of atoms. In O(n). *)
let to_atoms (d : t) : Atom.t list =
  let rec aux (d : t) (l : Atom.t list) : Atom.t list =
    match d with
    | Empty -> l
    | Leaf a -> a :: l
    | Node (d1, d2) -> aux d1 (aux d2 l) in
  aux d []

let rec indent (d : t) : t =
  match d with
  | Empty -> Empty
  | Leaf a -> Leaf (Atom.Indent (1, a))
  | Node (d1, d2) -> Node (indent d1, indent d2)

let nest (d : t) : t =
  Leaf (Atom.GroupOne (true, to_atoms d))

let nest_all (d : t) : t =
  Leaf (Atom.GroupAll (true, to_atoms d))

let group (d : t) : t =
  Leaf (Atom.GroupOne (false, to_atoms d))

let group_all (d : t) : t =
  Leaf (Atom.GroupAll (false, to_atoms d))

let parens (d : t) : t =
  !^ "(" ^-^ d ^-^ !^ ")"

let braces (d : t) : t =
  !^ "{" ^-^ d ^-^ !^ "}"

let brakets (d : t) : t =
  !^ "[" ^-^ d ^-^ !^ "]"

let angle_brakets (d : t) : t =
  !^ "<" ^-^ d ^-^ !^ ">"

let single_quotes (d : t) : t =
  !^ "'" ^-^ d ^-^ !^ "'"

let double_quotes (d : t) : t =
  !^ "\"" ^-^ d ^-^ !^ "\""

let concat (ds : t list) : t =
  List.fold_left append empty ds

let separate (separator : t) (ds : t list) : t =
  let rec aux ds =
    match ds with
    | [] -> empty
    | d :: ds -> separator ^-^ d ^-^ aux ds in
  match ds with
  | [] -> empty
  | d :: ds -> d ^-^ aux ds

(* Split a non-unicode string in a list of offsets / lengths according to a predicate [f]. *)
let rec split (s : string) (f : char -> bool) (o : int) (l : int)
  : (int * int) list =
  if o + l = String.length s then
    [(o, l)]
  else if f s.[o + l] then
    (o, l) :: split s f (o + l + 1) 0
  else
    split s f o (l + 1)

let words (s : string) : t =
  group @@ separate space @@ List.map (fun (o, l) -> sub_string s o l)
    (split s (fun c -> c = ' ' || c = '\n' || c = '\t') 0 0)

let lines (s : string) : t =
  separate newline @@ List.map (fun (o, l) -> sub_string s o l)
    (split s (fun c -> c = '\n') 0 0)

module OCaml = struct
  let unit (_ : unit) : t =
    !^ "()"

  let bool (b : bool) : t =
    !^ (string_of_bool b)

  let int (i : int) : t =
    !^ (string_of_int i)

  let float (f : float) : t =
    !^ (string_of_float f)

  let string (s : string) : t =
    double_quotes (!^ (String.escaped s))

  let option (d : 'a -> t) (o : 'a option) : t =
    match o with
    | None -> !^ "None"
    | Some x -> nest (!^ "Some" ^^ d x)

  let list (d : 'a -> t) (l : 'a list) : t =
    brakets @@ nest_all (space ^^ separate (!^ ";" ^^ space) (List.map d l) ^^ space)

  let tuple (ds : t list) : t =
    parens @@ nest @@ separate (!^ "," ^^ space) ds
end

module Debug = struct
  (* Pretty-print an atom. *)
  let rec pp_atom (a : Atom.t) : t =
    match a with
    | Atom.String (s, o, l) -> OCaml.string (String.sub s o l)
    | Atom.Break Break.Space -> !^ "Space"
    | Atom.Break Break.Newline -> !^ "Newline"
    | Atom.GroupOne (can_nest, _as) -> nest (!^ "GroupOne" ^^ parens (OCaml.bool can_nest ^-^ !^ "," ^^ pp_atoms _as))
    | Atom.GroupAll (can_nest, _as) -> nest (!^ "GroupAll" ^^ parens (OCaml.bool can_nest ^-^ !^ "," ^^ pp_atoms _as))
    | Atom.Indent (n, a) -> nest (!^ "Indent" ^^ parens (OCaml.int n ^-^ !^ "," ^^ pp_atom a))

  (* Pretty-print a list of atoms. *)
  and pp_atoms (_as : Atom.t list) : t =
    group_all (separate (!^ "," ^^ space) (List.map pp_atom _as))

  let pp_document (d : t) : t =
    OCaml.list pp_atom (to_atoms d)

  let pp_document_after_rendering (width : int) (tab : int) (d : t) : t =
    pp_atom @@ Atom.render width tab @@ to_atoms d
end

let to_something (width : int) (tab : int)
  (add_char : char -> unit) (add_string : string -> unit)
  (add_sub_string : string -> int -> int -> unit)
  (d : t) : unit =
  Atom.to_something tab add_char add_string add_sub_string @@
    Atom.render width tab @@ to_atoms d

let to_buffer (width : int) (tab : int) (b : Buffer.t) (d : t) : unit =
  to_something width tab
    (Buffer.add_char b) (Buffer.add_string b) (Buffer.add_substring b) d

let to_string (width : int) (tab : int) (d : t) : string =
  let b = Buffer.create 10 in
  to_buffer width tab b d;
  Buffer.contents b

let to_out_channel (width : int) (tab : int) (c : out_channel) (d : t) : unit =
  let output_sub_string (s : string) (o : int) (l : int) : unit =
    output_string c (String.sub s o l) in
  to_something width tab
    (output_char c) (output_string c) output_sub_string d

let to_stdout (width : int) (tab : int) (d : t) : unit =
  to_out_channel width tab stdout d*)