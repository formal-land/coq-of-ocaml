(** Char library *)

let code = int_of_char

let chr n =
  try char_of_int n with
  | Invalid_argument _ -> invalid_arg "Char.chr"

let is_printable n =
  32 <= n && n <> 127

let escaped = function
  | '\'' -> "\\'"
  | '\\' -> "\\\\"
  | '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\r' -> "\\r"
  | '\b' -> "\\b"
  | c ->
    if is_printable (code c) then begin
      let s = string_create 1 in
      string_unsafe_set s 0 c;
      s
    end else begin
      let n = code c in
      let s = string_create 4 in
      string_unsafe_set s 0 '\\';
      string_unsafe_set s 1 (unsafe_chr (48 + n / 100));
      string_unsafe_set s 2 (unsafe_chr (48 + (n / 10) mod 10));
      string_unsafe_set s 3 (unsafe_chr (48 + n mod 10));
      s
    end

let lowercase c =
  if (c >= 'A' && c <= 'Z')
  || (c >= '\192' && c <= '\214')
  || (c >= '\216' && c <= '\222')
  then unsafe_chr(code c + 32)
  else c

let uppercase c =
  if (c >= 'a' && c <= 'z')
  || (c >= '\224' && c <= '\246')
  || (c >= '\248' && c <= '\254')
  then unsafe_chr(code c - 32)
  else c

type t = char

let compare c1 c2 = code c1 - code c2
