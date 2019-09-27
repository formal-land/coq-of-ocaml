type foo = string

type 'a tree = Tree of 'a node list

and 'a node =
  | Leaf of string
  | Node of 'a tree

and 'b simple = 'b
  
and 'b double = 'b * 'b simple

and 'a unrelated = Unrelated of ('a simple) double
