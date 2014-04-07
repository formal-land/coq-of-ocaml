Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition n : Z := 12.

Definition c1 : ascii := "a" % char.

Definition c2 : ascii := "010" % char.

Definition c3 : ascii := "009" % char.

Definition c4 : ascii := """" % char.

Definition s : string := "hi
	:)""" % string.

Definition b1 : bool := false.

Definition b2 : bool := true.

Definition u : unit := tt.

Definition l1 {A702 : Type} : list A702 := [].

Definition l2 : list Z := cons 0 (cons 1 (cons 2 (cons 3 []))).

Definition o : option Z :=
  if b1 then
    None
  else
    Some n.

Definition e_match {A732 A735 : Type} (x : A735) :
  M [ OCaml.Match_failure ] A732 :=
  match x with
  | _ => OCaml.raise_Match_failure (("error" % string, 1, 2))
  end.

Definition e_assert {A758 A761 : Type} (x : A761) :
  M [ OCaml.Assert_failure ] A758 :=
  match x with
  | _ => OCaml.raise_Assert_failure (("error" % string, 1, 2))
  end.

Definition e_invalid {A784 A787 : Type} (x : A787) :
  M [ OCaml.Invalid_argument ] A784 :=
  match x with
  | _ => OCaml.raise_Invalid_argument ("error" % string)
  end.

Definition e_failure {A801 A804 : Type} (x : A804) : M [ OCaml.Failure ] A801 :=
  match x with
  | _ => OCaml.raise_Failure ("error" % string)
  end.

Definition e_not_found {A818 A821 : Type} (x : A821) :
  M [ OCaml.Not_found ] A818 :=
  match x with
  | _ => OCaml.raise_Not_found tt
  end.

Definition e_out_of_mem {A833 A836 : Type} (x : A836) :
  M [ OCaml.Out_of_memory ] A833 :=
  match x with
  | _ => OCaml.raise_Out_of_memory tt
  end.

Definition e_overflow {A848 A851 : Type} (x : A851) :
  M [ OCaml.Stack_overflow ] A848 :=
  match x with
  | _ => OCaml.raise_Stack_overflow tt
  end.

Definition e_sys_err {A863 A866 : Type} (x : A866) : M [ OCaml.Sys_error ] A863
  :=
  match x with
  | _ => OCaml.raise_Sys_error ("error" % string)
  end.

Definition e_EOF {A880 A883 : Type} (x : A883) : M [ OCaml.End_of_file ] A880 :=
  match x with
  | _ => OCaml.raise_End_of_file tt
  end.

Definition e_div {A895 A898 : Type} (x : A898) :
  M [ OCaml.Division_by_zero ] A895 :=
  match x with
  | _ => OCaml.raise_Division_by_zero tt
  end.

Definition e_sys_blocked {A910 A913 : Type} (x : A913) :
  M [ OCaml.Sys_blocked_io ] A910 :=
  match x with
  | _ => OCaml.raise_Sys_blocked_io tt
  end.

Definition e_rec_module {A925 A928 : Type} (x : A928) :
  M [ OCaml.Undefined_recursive_module ] A925 :=
  match x with
  | _ => OCaml.raise_Undefined_recursive_module (("error" % string, 1, 2))
  end.
