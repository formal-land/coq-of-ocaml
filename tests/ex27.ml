(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* List operations *)

let rec length_aux len = function
    [] -> len
  | a::l -> length_aux (len + 1) l
[@@coq_rec]

let length l = length_aux 0 l

let hd = function
    [] -> failwith "hd"
  | a::l -> a

let tl = function
    [] -> failwith "tl"
  | a::l -> l

let nth l n =
  if n < 0 then invalid_arg "List.nth" else
  let rec nth_aux l n =
    match l with
    | [] -> failwith "nth"
    | a::l -> if n = 0 then a else nth_aux l (n-1)
  [@@coq_rec]
  in nth_aux l n

let append = (@)

let rec rev_append l1 l2 =
  match l1 with
    [] -> l2
  | a :: l -> rev_append l (a :: l2)
[@@coq_rec]

let rev l = rev_append l []

let rec flatten = function
    [] -> []
  | l::r -> l @ flatten r
[@@coq_rec]

let concat = flatten

let rec map f = function
    [] -> []
  | a::l -> let r = f a in r :: map f l
[@@coq_rec]

let rec mapi_aux i f = function
    [] -> []
  | a::l -> let r = f i a in r :: mapi_aux (i + 1) f l
[@@coq_rec]

let mapi f l = mapi_aux 0 f l

let rev_map f l =
  let rec rmap_f accu = function
    | [] -> accu
    | a::l -> rmap_f (f a :: accu) l
  [@@coq_rec] in
  rmap_f [] l

let rec iter f = function
    [] -> ()
  | a::l -> f a; iter f l
[@@coq_rec]

let rec iteri_aux i f = function
    [] -> ()
  | a::l -> f i a; iteri_aux (i + 1) f l
[@@coq_rec]

let iteri f l = iteri_aux 0 f l

let rec fold_left f accu l =
  match l with
    [] -> accu
  | a::l -> fold_left f (f accu a) l
[@@coq_rec]

let rec fold_right f l accu =
  match l with
    [] -> accu
  | a::l -> f a (fold_right f l accu)
[@@coq_rec]

let rec map2 f l1 l2 =
  match (l1, l2) with
    ([], []) -> []
  | (a1::l1, a2::l2) -> let r = f a1 a2 in r :: map2 f l1 l2
  | (_, _) -> invalid_arg "List.map2"
[@@coq_rec]

let rev_map2 f l1 l2 =
  let rec rmap2_f accu l1 l2 =
    match (l1, l2) with
    | ([], []) -> accu
    | (a1::l1, a2::l2) -> rmap2_f (f a1 a2 :: accu) l1 l2
    | (_, _) -> invalid_arg "List.rev_map2"
  [@@coq_rec] in
  rmap2_f [] l1 l2

let rec iter2 f l1 l2 =
  match (l1, l2) with
    ([], []) -> ()
  | (a1::l1, a2::l2) -> f a1 a2; iter2 f l1 l2
  | (_, _) -> invalid_arg "List.iter2"
[@@coq_rec]

let rec fold_left2 f accu l1 l2 =
  match (l1, l2) with
    ([], []) -> accu
  | (a1::l1, a2::l2) -> fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) -> invalid_arg "List.fold_left2"
[@@coq_rec]

let rec fold_right2 f l1 l2 accu =
  match (l1, l2) with
    ([], []) -> accu
  | (a1::l1, a2::l2) -> f a1 a2 (fold_right2 f l1 l2 accu)
  | (_, _) -> invalid_arg "List.fold_right2"
[@@coq_rec]

let rec for_all p = function
    [] -> true
  | a::l -> p a && for_all p l
[@@coq_rec]

let rec _exists p = function
    [] -> false
  | a::l -> p a || _exists p l
[@@coq_rec]

let rec for_all2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> true
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> invalid_arg "List.for_all2"
[@@coq_rec]

let rec _exists2 p l1 l2 =
  match (l1, l2) with
    ([], []) -> false
  | (a1::l1, a2::l2) -> p a1 a2 || _exists2 p l1 l2
  | (_, _) -> invalid_arg "List.exists2"
[@@coq_rec]

(*let rec mem x = function
    [] -> false
  | a::l -> compare a x = 0 || mem x l

let rec memq x = function
    [] -> false
  | a::l -> a == x || memq x l

let rec assoc x = function
    [] -> raise Not_found
  | (a,b)::l -> if compare a x = 0 then b else assoc x l

let rec assq x = function
    [] -> raise Not_found
  | (a,b)::l -> if a == x then b else assq x l

let rec mem_assoc x = function
  | [] -> false
  | (a, b) :: l -> compare a x = 0 || mem_assoc x l

let rec mem_assq x = function
  | [] -> false
  | (a, b) :: l -> a == x || mem_assq x l

let rec remove_assoc x = function
  | [] -> []
  | (a, b as pair) :: l ->
      if compare a x = 0 then l else pair :: remove_assoc x l

let rec remove_assq x = function
  | [] -> []
  | (a, b as pair) :: l -> if a == x then l else pair :: remove_assq x l*)

let rec find p = function
  | [] -> raise Not_found
  | x :: l -> if p x then x else find p l
[@@coq_rec]

let find_all p =
  let rec find accu = function
  | [] -> rev accu
  | x :: l -> if p x then find (x :: accu) l else find accu l
  [@@coq_rec] in
  find []

let filter = find_all

let partition p l =
  let rec part yes no = function
  | [] -> (rev yes, rev no)
  | x :: l -> if p x then part (x :: yes) no l else part yes (x :: no) l
  [@@coq_rec] in
  part [] [] l

let rec split = function
    [] -> ([], [])
  | (x,y)::l ->
      let (rx, ry) = split l in (x::rx, y::ry)
[@@coq_rec]

let rec combine l1 l2 =
  match (l1, l2) with
    ([], []) -> []
  | (a1::l1, a2::l2) -> (a1, a2) :: combine l1 l2
  | (_, _) -> invalid_arg "List.combine"
[@@coq_rec]

(** sorting *)
let rec merge cmp l1 l2 =
  let rec merge_aux l2 =
    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: t2 ->
        if cmp h1 h2 <= 0
        then h1 :: merge cmp t1 l2
        else h2 :: merge_aux t2
  [@@coq_rec] in
  merge_aux l2
[@@coq_rec]

let rec chop k l =
  if k = 0 then l else begin
    match l with
    | x::t -> chop (k-1) t
    | _ -> assert false
  end
[@@coq_rec]

module StableSort = struct
  let rec rev_merge cmp l1 l2 accu =
    let rec rev_merge_aux l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          if cmp h1 h2 <= 0
          then rev_merge cmp t1 l2 (h1::accu)
          else rev_merge_aux t2 (h2::accu)
    [@@coq_rec] in
    rev_merge_aux l2 accu
  [@@coq_rec]

  let rec rev_merge_rev cmp l1 l2 accu =
    let rec rev_merge_rev_aux l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          if cmp h1 h2 > 0
          then rev_merge_rev cmp t1 l2 (h1::accu)
          else rev_merge_rev_aux t2 (h2::accu)
    [@@coq_rec] in
    rev_merge_rev_aux l2 accu
  [@@coq_rec]

  let rec sort cmp n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       if cmp x1 x2 <= 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       if cmp x1 x2 <= 0 then begin
         if cmp x2 x3 <= 0 then [x1; x2; x3]
         else if cmp x1 x3 <= 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         if cmp x1 x3 <= 0 then [x2; x1; x3]
         else if cmp x2 x3 <= 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n / 2 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = rev_sort cmp n1 l in
       let s2 = rev_sort cmp n2 l2 in
       rev_merge_rev cmp s1 s2 []

  and rev_sort cmp n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       if cmp x1 x2 > 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       if cmp x1 x2 > 0 then begin
         if cmp x2 x3 > 0 then [x1; x2; x3]
         else if cmp x1 x3 > 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         if cmp x1 x3 > 0 then [x2; x1; x3]
         else if cmp x2 x3 > 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n / 2 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = sort cmp n1 l in
       let s2 = sort cmp n2 l2 in
       rev_merge cmp s1 s2 []
end

let stable_sort cmp l =
  let len = length l in
  if len < 2 then l else StableSort.sort cmp len l

let sort = stable_sort
let fast_sort = stable_sort

module SortUniq = struct
  (** sorting + removing duplicates *)
  let rec rev_merge cmp l1 l2 accu =
    let rec rev_merge_aux l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          let c = cmp h1 h2 in
          if c = 0 then rev_merge cmp t1 t2 (h1::accu)
          else if c < 0
          then rev_merge cmp t1 l2 (h1::accu)
          else rev_merge_aux t2 (h2::accu)
    [@@coq_rec] in
    rev_merge_aux l2 accu
  [@@coq_rec]

  let rec rev_merge_rev cmp l1 l2 accu =
    let rec rev_merge_rev_aux l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          let c = cmp h1 h2 in
          if c = 0 then rev_merge_rev cmp t1 t2 (h1::accu)
          else if c > 0
          then rev_merge_rev cmp t1 l2 (h1::accu)
          else rev_merge_rev_aux t2 (h2::accu)
    [@@coq_rec] in
    rev_merge_rev_aux l2 accu
  [@@coq_rec]

  let rec sort cmp n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then [x1]
       else if c < 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x2]
         else if c < 0 then [x2; x3] else [x3; x2]
       end else if c < 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x1; x2]
         else if c < 0 then [x1; x2; x3]
         else let c = cmp x1 x3 in
         if c = 0 then [x1; x2]
         else if c < 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         let c = cmp x1 x3 in
         if c = 0 then [x2; x1]
         else if c < 0 then [x2; x1; x3]
         else let c = cmp x2 x3 in
         if c = 0 then [x2; x1]
         else if c < 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n / 2 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = rev_sort cmp n1 l in
       let s2 = rev_sort cmp n2 l2 in
       rev_merge_rev cmp s1 s2 []

  and rev_sort cmp n l =
    match n, l with
    | 2, x1 :: x2 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then [x1]
       else if c > 0 then [x1; x2] else [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       let c = cmp x1 x2 in
       if c = 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x2]
         else if c > 0 then [x2; x3] else [x3; x2]
       end else if c > 0 then begin
         let c = cmp x2 x3 in
         if c = 0 then [x1; x2]
         else if c > 0 then [x1; x2; x3]
         else let c = cmp x1 x3 in
         if c = 0 then [x1; x2]
         else if c > 0 then [x1; x3; x2]
         else [x3; x1; x2]
       end else begin
         let c = cmp x1 x3 in
         if c = 0 then [x2; x1]
         else if c > 0 then [x2; x1; x3]
         else let c = cmp x2 x3 in
         if c = 0 then [x2; x1]
         else if c > 0 then [x2; x3; x1]
         else [x3; x2; x1]
       end
    | n, l ->
       let n1 = n / 2 in
       let n2 = n - n1 in
       let l2 = chop n1 l in
       let s1 = sort cmp n1 l in
       let s2 = sort cmp n2 l2 in
       rev_merge cmp s1 s2 []
end

let sort_uniq cmp l =
  let len = length l in
  if len < 2 then l else SortUniq.sort cmp len l