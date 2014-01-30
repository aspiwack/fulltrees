(** This file contains the implementation of the balancing algorithm
    without partial functions presented in Section 2. *)
type 'a tree =
  | Node of 'a tree * 'a * 'a tree
  | Leaf

module PowerList = struct

  (** To enforce that a structure has [2^n-1] elements in ocaml's type
      system, we can use non-uniform inductive datatypes.

      To read the ['a t] type, notice that if not [Zero], there is always an
      element available. It is the first (possibly unique) element of the
      list. If there are other elements, then the next head is a pair
      [(b,c)]: the second and third elements. If there are still more
      elements, then the next head of head is a pair of pairs
      [((d,e),(f,g))]: [d] is the fourth element, [e] the fifth, [f] the
      sixth, and [g] the seventh. And so on. *)
  type 'a t =
    | Zero
    | TwicePlusOne of 'a * ('a*'a) t

  (** [map] is the equivalent of [List.map]. *)
  let rec map : 'a 'b. ('a->'b) -> 'a t -> 'b t = fun f -> function
    | Zero -> Zero
    | TwicePlusOne (elt,lst) ->
        let f' (x,y) = f x , f y in
        TwicePlusOne (f elt , map f' lst)

  (** [pair_up lst] splits [lst] according to whether it is empty, it
      has non-zero even length, or it has odd length. Lists of even
      length are represented as lists of pairs. *)
  type 'a parity =
    | Empty
    | Odd of 'a * ('a*'a) list
    | Even of ('a*'a) * ('a*'a) list
  let pair_up l =
    let succ elt = function
      | Empty -> Odd (elt , [])
      | Odd (b,l') -> Even ((elt,b) , l')
      | Even (bc,l') -> Odd (elt , bc::l')
    in
    List.fold_right succ l Empty

  (** [of_list lst] completes [lst] into a power list since we want
      the elements of the powerlist to have a different type from those of
      the list, we need coerctions [pad:'a->'b] and [coerce:'a*'a->'b],
      corresponding to the cases [Odd] and [Even] of the [parity]
      view. *)
  let rec of_list : 'a 'b. ('a->'b) -> ('a*'a->'b) -> 'a list -> 'b t =
    fun pad coerce bits ->
      let pad' (x,y) = (pad x , pad y) in
      let coerce' (x,y) = (coerce x , coerce y) in
      match pair_up bits with
      | Empty -> Zero
      | Odd  (a ,pures) -> TwicePlusOne (pad a, of_list pad' coerce' pures)
      | Even (ab,pures) -> TwicePlusOne (coerce ab, of_list pad' coerce' pures)

end

(** The [PowerList] module shows how to encode the length invariant,
    and how to complete a list with a default value spliced between the
    appropriate initial segment. However, for our algorithm, we also need
    to encode the invariant that even positions have a different type than
    odd position. *)

module AlternatingPowerList = struct

  (** In an [('odd,'even) t], the first head has type ['odd], the
      second head is the pair of the the second and third element,
      hence has type [('even,'odd)]. The third head has the elements
      number four to seven: its type is
      [(('even,'odd),('even,'odd))]. Indeed, once the first element
      has been selected, even and odd elements pair up, and there is
      no distinction between odd and even position pairs any
      more. So we reuse the type {!PowerList.t}. *)
  type ('odd,'even) t =
    | Zero
    | TwicePlusOne of 'odd * ('even*'odd) PowerList.t


  (** We build an [('odd,'even) t] from an ['a list] using a default
      ['odd] value for padding, a function [f:'a -> 'odd] for odd
      positions, and [g:'a -> 'even] for even positions. *)
  let of_list leaf up id = function
    | [] -> Zero
    | a::l ->
        let pad x = id x , leaf in
        let coerce (x,y) = id x , up y in
        TwicePlusOne (up a , PowerList.of_list pad coerce l)

end

module PL = PowerList
module APL = AlternatingPowerList


(** [pass left pair apl] takes a tree [left], a pair [pair] of an
    element and a tree, and an alternating power list [apl],
    (i.e. essentially, an alternating power list with at least 3
    elements), and groups the consecutive triplets using [Node]: the
    three first elements (of respective types ['o], ['e] and ['o]) are
    joined, then for each group of four elements (of type
    [('e,'o),('e,'o)]) the first one is kept as such, and the three
    others can be joined. *)
let pass left (root,right) apl =
  let join_up ((single,left),(root,right)) =
    single, Node (left,root,right)
  in
  APL.TwicePlusOne ( Node (left,root,right) , PL.map join_up apl)

(** The main loop of the algorithm iterates [pass] until it contains a
    single element, necessarily a full tree. *)
let rec loop : 'e. ('e tree,'e) APL.t -> 'e tree = function
  | APL.Zero -> Leaf
  | APL.TwicePlusOne (tree,PL.Zero) -> tree
  | APL.TwicePlusOne (tree,PL.TwicePlusOne (pair,apl)) ->
      loop (pass tree pair apl)

(** [balance list] turns [list] into a full tree, preserving the order
    of the elements. *)
let singleton x = Node(Leaf,x,Leaf)
let balance l =
  loop (APL.of_list Leaf singleton (fun e->e) l)
