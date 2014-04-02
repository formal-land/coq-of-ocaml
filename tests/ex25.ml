(** Module List *)

let l1 : int list = []
let l2 = [1; 2; 3]

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
let iti _ = List.iteri (fun i x -> print_int i; print_string x) ["Hello"; " "; "world"]
let m = List.map (fun x -> x + 1) l2
let mi = List.mapi (fun i x -> x + i) l2
let rm = List.rev_map (fun x -> x + 1) l2
let fl = List.fold_left (fun s x -> s + x) 0 l2
let fr = List.fold_right (fun x s -> s + x) l2 0*)