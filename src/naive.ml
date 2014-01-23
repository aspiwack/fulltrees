type 'a tree =
| Leaf
| Node of 'a tree * 'a * 'a tree

type 'a tree_or_elt =
| Elt of 'a
| Tree of 'a tree

let join left node right = Tree (Node (left, node, right))

let rec pass list = match  list with
  | Tree left :: Elt root :: Tree right :: Elt e :: others -> join left root right :: Elt e :: pass others
  | [Tree left; Elt root; Tree right] -> [join left root right]
  | _ -> assert false

let rec loop list = match list with
  | [] -> Leaf
  | [Tree t] -> t
  | list -> loop (pass list)

let complete list =
  let n = List.length list in
  let rec pow2 i = if i <= n then pow2 (2*i) else i in 
  let missing = (pow2 1) - n - 1 in
  let rec pad missing = function
    | head::tail when missing <> 0 -> Tree Leaf :: Elt head :: pad (missing - 1) tail
    | one::two::others -> join Leaf one Leaf :: Elt two :: pad 0 others
    | [single] -> [join Leaf single Leaf]
    | [] -> []
  in
  pad missing list

let balance list = loop (complete  list)
