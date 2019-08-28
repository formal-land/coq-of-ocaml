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
let m = List.map (fun x -> x + 1) l2
let mi = List.mapi (fun i x -> x + i) l2
let rm = List.rev_map (fun x -> x + 1) l2
let fl = List.fold_left (fun s x -> s + x) 0 l2
let fr = List.fold_right (fun x s -> s + x) l2 0

(* List scanning *)
let all = List.for_all (fun x -> x = 2) l2
let ex = List.exists (fun x -> x = 2) l2

(* List searching *)
let fin _ = List.find (fun x -> x = 1) l2
let fil = List.filter (fun x -> x >= 2) l2
let fina = List.find_all (fun x -> x >= 2) l2
let par = List.partition (fun x -> x > 2) l2

(* Association lists *)
let asso _ = List.assoc 2 l3
let masso _ = List.mem_assoc 2 l3
let rasso _ = List.remove_assoc 2 l3

(* Lists of pairs *)
let sp = List.split l3
let com _ = List.combine l2 l2

(* Sorting *)
let so _ = List.sort (fun x y -> y - x) l2
let sso _ = List.stable_sort (fun x y -> y - x) l2
let fso _ = List.fast_sort (fun x y -> y - x) l2
let mer = List.merge (fun x y -> y - x) l2 [2; -1; 5]
