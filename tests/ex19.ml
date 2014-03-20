exception Error

let x =
  try raise Error with
  | Error -> 12