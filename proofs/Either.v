Inductive t (a b : Set) : Set :=
| Left : a -> t a b
| Right : b -> t a b.

Arguments Left {_ _}.
Arguments Right {_ _}.
