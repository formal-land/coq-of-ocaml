(** Module List *)

let l1 : int list = []
let l2 = [1; 2; 3; 4]
let l3 = [1, "one"; 2, "two"]

let s1 = List.length l1
let s2 = List.length l2
let h _ = List.hd l2
let t _ = List.tl l2
let x _ = List.nth l2 1
let rl = List.rev l2
let ll = List.append l2 l2
let rll = List.rev_append l2 l2
let lc = List.concat [l1; l2; l1; l2]
let lf = List.flatten [l1; l2; l1; l2]

(* Iterators *)
(*let it _ = List.iter (fun x -> print_string x) ["Hello"; " "; "world"]
let iti _ = List.iteri (fun i x -> print_int i; print_string x) ["Hello"; " "; "world"]*)
let m = List.map (fun x -> x + 1) l2
let mi = List.mapi (fun i x -> x + i) l2
let rm = List.rev_map (fun x -> x + 1) l2
let fl = List.fold_left (fun s x -> s + x) 0 l2
let fr = List.fold_right (fun x s -> s + x) l2 0

(* Iterators on two lists *)
(* let it2 _ = List.iter2 (fun x y -> print_int x; print_newline (); print_int y) l2 l2 *)
let m2 _ = List.map2 (fun x y -> x + y) l2 l2
let rm2 _ = List.rev_map2 (fun x y -> x + y) l2 l2
let fl2 _ = List.fold_left2 (fun s x y -> s + x + y) 0 l2 l2
let fr2 _ = List.fold_right2 (fun s x y -> s + x + y) l2 l2 0

(* List scanning *)
let all = List.for_all (fun x -> x = 2) l2
let ex = List.exists (fun x -> x = 2) l2
let all2 _ = List.for_all2 (fun x y -> x = y) l2 l2
let ex2 _ = List.exists2 (fun x y -> x = y) l2 l2
(* let me = List.mem 2 l2 *)
(* let meq = List.memq l2 [l2] *)

(* List searching *)
let fin _ = List.find (fun x -> x = 1) l2
let fil = List.filter (fun x -> x >= 2) l2
let fina = List.find_all (fun x -> x >= 2) l2
let par = List.partition (fun x -> x > 2) l2

(* Association lists *)
(*let asso _ = List.assoc 2 l3
let assoq _ = List.assq 2 l3
let masso _ = List.mem_assoc 2 l3
let massoq _ = List.mem_assq 2 l3
let rasso _ = List.remove_assoc 2 l3
let rassoq _ = List.remove_assq 2 l3*)

(* Lists of pairs *)
let sp = List.split l3
let com _ = List.combine l2 l2

(* Sorting *)
(*let so = List.sort (fun x y -> y - x) l2
let sso = List.stable_sort (fun x y -> y - x) l2
let fso = List.fast_sort (fun x y -> y - x) l2
let me = List.merge (fun x y -> y - x) l2 [2; -1; 5]*)