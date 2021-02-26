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

Fixpoint proj_int (e : expr) : int :=
  match e with
  | Int n => n
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => unreachable_gadt_branch
  end.

Inductive term : vtag -> Set :=
| Int : int -> term int_tag
| String : string -> term string_tag
| Sum : term int_tag -> term int_tag -> term int_tag
| Pair : forall {a b : vtag}, term a -> term b -> term (tuple_tag a b).

Fixpoint get_int (e : term int_tag) : int :=
  match e in term t0 return t0 = int_tag -> int with
  | Int n => fun eq0 => ltac:(subst; exact n)
  | Sum e1 e2 =>
    fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2)))
  | _ => ltac:(discriminate)
  end eq_refl.

Inductive one_case : Set :=
| SingleCase : one_case
| Impossible : one_case.

Definition x : int :=
  match SingleCase with
  | SingleCase => 0
  | _ => unreachable_gadt_branch
  end.

Inductive gadt_list : Set :=
| GNil : gadt_list
| GCons : forall {a : Set}, a -> gadt_list -> gadt_list.

Definition gadt_empty_list : gadt_list := GNil.
