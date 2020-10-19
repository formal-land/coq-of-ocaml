let [@coq_axiom_with_reason "for testing"] show (x : 'a) : string =
  failwith "I would like to have type-classes too"

let [@coq_axiom_with_reason "for testing"] rec recursive (x : 'a) : string =
  "A definition is not recursive anymore when axiom"
