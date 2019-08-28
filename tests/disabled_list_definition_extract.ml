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

let length l = length_aux 0 l

let append = (@)

let rec rev_append l1 l2 =
  match l1 with
    [] -> l2
  | a :: l -> rev_append l (a :: l2)

let rev l = rev_append l []

let rec flatten = function
    [] -> []
  | l::r -> l @ flatten r

let concat = flatten

let rec map f = function
    [] -> []
  | a::l -> let r = f a in r :: map f l

let rec mapi_aux i f = function
    [] -> []
  | a::l -> let r = f i a in r :: mapi_aux (i + 1) f l

let mapi f l = mapi_aux 0 f l

let rev_map f l =
  let rec rmap_f_coq_rec accu = function
    | [] -> accu
    | a::l -> rmap_f_coq_rec (f a :: accu) l in
  rmap_f_coq_rec [] l

let rec fold_left f accu l =
  match l with
    [] -> accu
  | a::l -> fold_left f (f accu a) l

let rec fold_right f l accu =
  match l with
    [] -> accu
  | a::l -> f a (fold_right f l accu)

let rec for_all p = function
    [] -> true
  | a::l -> p a && for_all p l

let rec _exists p = function
    [] -> false
  | a::l -> p a || _exists p l

let find_all p =
  let rec find_coq_rec accu = function
  | [] -> rev accu
  | x :: l -> if p x then find_coq_rec (x :: accu) l else find_coq_rec accu l in
  find_coq_rec []

let filter = find_all

let partition p l =
  let rec part_coq_rec yes no = function
  | [] -> (rev yes, rev no)
  | x :: l ->
    if p x then
      part_coq_rec (x :: yes) no l
    else
      part_coq_rec yes (x :: no) l in
  part_coq_rec [] [] l

let rec split = function
    [] -> ([], [])
  | (x,y)::l ->
      let (rx, ry) = split l in (x::rx, y::ry)

(** sorting *)
let rec merge cmp l1 l2 =
  let rec rev_merge_aux_coq_rec l2 =
    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: t2 ->
        if cmp h1 h2 <= 0
        then h1 :: merge cmp t1 l2
        else h2 :: rev_merge_aux_coq_rec t2 in
  rev_merge_aux_coq_rec l2

let rec chop k l =
  if k = 0 then l else begin
    match l with
    | x::t -> chop (k-1) t
    | _ -> assert false
  end

module StableSort = struct
  let rec rev_merge cmp l1 l2 accu =
    let rec rev_merge_aux_coq_rec l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          if cmp h1 h2 <= 0
          then rev_merge cmp t1 l2 (h1::accu)
          else rev_merge_aux_coq_rec t2 (h2::accu) in
    rev_merge_aux_coq_rec l2 accu


  let rec rev_merge_rev cmp l1 l2 accu =
    let rec rev_merge_rev_aux_coq_rec l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          if cmp h1 h2 > 0
          then rev_merge_rev cmp t1 l2 (h1::accu)
          else rev_merge_rev_aux_coq_rec t2 (h2::accu) in
    rev_merge_rev_aux_coq_rec l2 accu


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
    let rec rev_merge_aux_coq_rec l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          let c = cmp h1 h2 in
          if c = 0 then rev_merge cmp t1 t2 (h1::accu)
          else if c < 0
          then rev_merge cmp t1 l2 (h1::accu)
          else rev_merge_aux_coq_rec t2 (h2::accu) in
    rev_merge_aux_coq_rec l2 accu


  let rec rev_merge_rev cmp l1 l2 accu =
    let rec rev_merge_rev_aux_coq_rec l2 accu =
      match l1, l2 with
      | [], l2 -> rev_append l2 accu
      | l1, [] -> rev_append l1 accu
      | h1::t1, h2::t2 ->
          let c = cmp h1 h2 in
          if c = 0 then rev_merge_rev cmp t1 t2 (h1::accu)
          else if c > 0
          then rev_merge_rev cmp t1 l2 (h1::accu)
          else rev_merge_rev_aux_coq_rec t2 (h2::accu) in
    rev_merge_rev_aux_coq_rec l2 accu


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
