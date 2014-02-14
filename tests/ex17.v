Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Module Break.
  Inductive t : Type :=
  | Space : t
  | Newline : t .
  Arguments Space .
  Arguments Newline .
End Break.

Module Atom.
  Inductive t : Type :=
  | String : string -> Z -> Z -> t
  | Break : Break.t -> t
  | GroupOne : bool -> (list t) -> t
  | GroupAll : bool -> (list t) -> t
  | Indent : Z -> t -> t .
  Arguments String _ _ _.
  Arguments Break _.
  Arguments GroupOne _ _.
  Arguments GroupAll _ _.
  Arguments Indent _ _.
  
  (* *)
End Atom.
