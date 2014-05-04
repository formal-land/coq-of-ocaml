(** Declarations which could go in a module type. *)
open Typedtree
open SmartPrint

(** The declaration of a value. *)
module Value = struct
  type 'a t = {
    annotation : 'a;
    name : Name.t;
    typ_args : Name.t list;
    typ : Type.t }

  let pp (pp_a : 'a -> SmartPrint.t) (declaration : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ OCaml.tuple [
      pp_a declaration.annotation; Name.pp declaration.name;
      OCaml.list Name.pp declaration.typ_args; Type.pp declaration.typ])

  let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
    (declaration : value_description) : Loc.t t =
    let name = Name.of_ident declaration.val_id in
    let typ = declaration.val_desc.ctyp_type in
    let (typ, _, typ_args) =
      Type.of_type_expr_new_typ_vars env loc Name.Map.empty typ in
    { annotation = loc;
      name = name;
      typ_args = Name.Set.elements typ_args;
      typ = typ }

  let update_env (f : 'a -> 'b) (declaration : 'a t) (env : 'b FullEnvi.t)
    : 'b FullEnvi.t =
    FullEnvi.add_var [] declaration.name (f declaration.annotation) env
end