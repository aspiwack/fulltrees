(** This file contains the simple implementation of the tree balancing
    algorithm from Section 1. *)
type 'a tree =
| Leaf
| Node of 'a tree * 'a * 'a tree

(** The algorithm works on a list alternating labels of the form [Elt
    x] and trees of the form [Tree t]. *)
type 'a tree_or_elt =
| Elt of 'a
| Tree of 'a tree

(** [join] wraps the [Tree] and [Node] constructors together. *)
let join left node right = Tree (Node (left, node, right))

(** [pass list] requires [list] to be of size [2^(k+2)-1] and to
    alternate elements of the shape [Tree t], where [t] is a full tree of
    some fixed height [h], (in odd positions) and [Elt x] (in even
    positions). It returns a list of size [2^(k+1)-1] alternating elements
    of the form [Tree t], where [t] is full and has height [h+1], and [Elt
    x]. *)
let rec pass = function
  | Tree left :: Elt root :: Tree right :: Elt e :: others ->
      join left root right :: Elt e :: pass others
  | [Tree left; Elt root; Tree right] ->
      [join left root right]
  | _ -> assert false

(** The main loop of the algorithm iterates [pass] until it contains a
    single element, necessarily a full tree. *)
let rec loop = function
  | [] -> Leaf
  | [Tree t] -> t
  | list -> loop (pass list)

(** The next two functions are used to compute the power of 2, that is
    closest and superior to [n] *)
let rec repeat ~until:predicate ~f value =
  if predicate value then value
  else repeat ~until:predicate ~f (f value)

let closest_power n =
  repeat ~until:((<) n) ~f:(( * ) 2) 1 

(** A list of arbitrary length [n] is completed to length [2^k-1 >= n
    > 2^(k-1)-1] by inserting the appropriate number of leaves. The
    appropriate [2^k-1] is computed, and the appropriate number of [Leaf]
    are inserted in the first odd positions. *)
let complete list =
  let n = List.length list in
  let missing = closest_power n - n - 1 in
  let rec pad missing = function
    | head::tail when missing <> 0 ->
        Tree Leaf :: Elt head :: pad (missing - 1) tail
    | odd::even::others ->
        join Leaf odd Leaf :: Elt even :: pad 0 others
    | [single] ->
        [join Leaf single Leaf]
    | [] ->
        []
  in
  pad missing list

(** [balance list] turns [list] into a full tree, preserving the order
    of the elements. *)
let balance list = loop (complete  list)
