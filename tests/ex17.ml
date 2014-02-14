(* Separators. *)
module Break = struct
  (* A break can be a whitespace or a newline if the text has to be splited. *)
  type t =
    | Space
    | Newline
end

(* The internal representation of a document and the engine. *)
module Atom = struct
  (* An atom is the low-level tree describing a document. *)
  type t =
    | String of string * int * int
      (* A non-breaking string. It should be newlines free. Represented as a
          sub-string of an other string, with an offset and a length. *)
    | Break of Break.t (* A separator. *)
    | GroupOne of bool * t list
      (* A list of atoms. Only the necessary number of breaks are splited.
         The boolean is true if nesting is activated. *)
    | GroupAll of bool * t list
      (* A list of atoms. No or all the breaks are splited.
         The boolean is true if nesting is activated. *)
    | Indent of int * t (* Indents by [n] tabulations the atom. Can be negative. *)

  (* If we overflow a line. *)
  exception Overflow
end