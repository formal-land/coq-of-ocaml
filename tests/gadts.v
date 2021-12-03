Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive gre (a : Set) : Set :=
| Arg : a -> gre a.

Arguments Arg {_}.

Inductive foo : Set :=
| Bar : forall {a b c : Set}, a -> int -> b -> c -> foo
| Other : int -> foo.

Inductive expr : Set :=
| Int : int -> expr
| String : string -> expr
| Sum : expr -> expr -> expr
| Pair : expr -> expr -> expr.

Fixpoint proj_int (e_value : expr) : int :=
  match e_value with
  | Int n_value => n_value
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => unreachable_gadt_branch
  end.

Inductive term : vtag -> Set :=
| T_Int : int -> term int_tag
| T_String : string -> term string_tag
| T_Sum : term int_tag -> term int_tag -> term int_tag.

Fixpoint get_int (e_value : term int_tag) : int :=
  match e_value in term t0 return t0 = int_tag -> int with
  | T_Int n_value => fun eq0 => ltac:(subst; exact n_value)
  | T_Sum e1 e2 =>
    fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2)))
  | _ => ltac:(discriminate)
  end eq_refl.

Fixpoint interp {a : vtag} (function_parameter : term a) : decode_vtag a :=
  match function_parameter with
  | T_Int n_value => n_value
  | T_String s_value => s_value
  | T_Sum s1 s2 => Z.add (interp s1) (interp s2)
  end.

Inductive one_case : Set :=
| SingleCase : one_case
| Impossible : one_case.

Definition x_value : int :=
  match SingleCase with
  | SingleCase => 0
  | _ => unreachable_gadt_branch
  end.

Inductive gadt_list : Set :=
| GNil : gadt_list
| GCons : forall {a : Set}, a -> gadt_list -> gadt_list.

Definition gadt_empty_list : gadt_list := GNil.

Module With_cast.
  Inductive int_or_bool : Set :=
  | Int : int_or_bool
  | Bool : int_or_bool.
  
  Definition to_int {a : Set} (kind : int_or_bool) (x_value : a) : int :=
    match (kind, x_value) with
    | (Int, x_value) =>
      let x_value := cast int x_value in
      x_value
    | (Bool, x_value) =>
      let x_value := cast bool x_value in
      if x_value then
        1
      else
        0
    end.
End With_cast.
