(** The goal is to write a function [f:'a list -> 'a tree] which runs
    in linear time, such that [f l] is the is full ({i i.e.} only the last
    level may be incomplete) and that [l] contains the elements of [f l]
    in infix order. In particular, if [l] is sorted, then [f l] is a
    well-balance binary search tree.

    The idea is to pair up values in the list, then pair up the values
    in the paired-up list, and so on until there is a single
    element. Since we are building a tree with internal nodes, though,
    this requires a bit of tweaking: instead of pairing up, we have to
    groupe three elements, the middle one being and ['a] and the other
    two an ['a tree]. Also, this algorithm leads to a full tree only
    when the length of the input list is of size [2^n-1] for some [n].

    One way to implement this algorithm is to use a list of length
    [2^h-1], with the invariant that every element at an even position
    is a one-element tree. But I'll encode the invariants using
    datatypes. *)
type 'a tree =
  | Node of 'a tree * 'a * 'a tree
  | Leaf

module PowerList = struct

  (** To enforce that a structure has [2^n-1] elements in ocaml's type
      system, we can use non-uniform inductive datatypes. Using the
      recursion that [2^(n+1)-1 = 2*(2^n-1)+1].

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

  (** [map f l] is the functorial action of [f] on the powerlist [l]. *)
  let rec map : 'a 'b. ('a->'b) -> 'a t -> 'b t = fun f -> function
    | Zero -> Zero
    | TwicePlusOne (x,lst) ->
        let f' (x,y) = f x , f y in
        TwicePlusOne ( f x , map f' lst)

  (** [pair_up l] takes the non-empty list [l] and returns, if [l] has
      even length [Even a b,l'] where [(a,b)::l'] has consecutive
      elements of [l] paired up, otherwise [Odd a,l'] where [l'] is
      the (possibly empty) list of consecutive elements of [l.tl]
      paired up. *)
  type 'a parity =
    | Empty
    | Odd of 'a * ('a*'a) list
    | Even of ('a*'a) * ('a*'a) list
  let rec pair_up = function
    | [] -> Empty
    | a::l ->
        begin match pair_up l with
        | Empty -> Odd (a , [])
        | Odd (b,l') -> Even ((a,b) , l')
        | Even (bc,l') -> Odd (a , bc::l')
        end


  (** Given a casting function ['a->'b], we can construct an ['a t]
      from a non-empty ['a list] of any size (here represented as an
      ['a eo] together with an [('a*'a) list], but it requires
      padding. The idea is to insert a default value [d0:'b] when
      needed to complete the list to an appropriate length. However,
      because the recursive step does not allow it, we cannot use a
      [d0] as the argument for padding, instead, we use a function
      [d:'a->'b]. At the first step of the recursion, [d] is expected
      to be of the form [fun a -> (g x,d0)], effectively inserting
      [d0] after the current value. *)
  let rec of_list : 'a 'b. ('a->'b) -> ('a*'a->'b) -> 'a list -> 'b t =
    fun d f l ->
      let d' (x,y) = (d x , d y) in
      let f' (x,y) = (f x , f y) in
      match pair_up l with
      | Empty -> Zero
      | Odd  (a ,l') -> TwicePlusOne ( d a  , of_list d' f' l' )
      | Even (ab,l') -> TwicePlusOne ( f ab , of_list d' f' l' )

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
  let of_list d f g = function
    | [] -> Zero
    | a::l ->
        let d' x = g x , d in
        let fg (x,y) = g x , f y in
        TwicePlusOne (f a , PowerList.of_list d' fg l)

end

module PL = PowerList
module APL = AlternatingPowerList


(** [pass left pair apl] takes a tree, a pair of an element and a tree, 
    and an alternating power list, (i.e. an alternating power list with
    at least 3 elements), and groups the consecutive triplets using [Node]:
    the three first elements (of respective types ['o], ['e] and ['o])
    are joined, then for each group of four elements (of type
    [('e,'o),('e,'o)]) the first one is kept as such, and the three
    others can be joined. *)
let pass : 'a. 'a tree -> ('a*'a tree) -> (('a*'a tree)*('a*'a tree)) PL.t -> ('a tree,'a) APL.t =
  fun left (root,right) apl ->
    APL.TwicePlusOne ( Node (left,root,right) , 
		       PL.map (fun ((single,left),(root,right)) -> single , Node(left,root,right) ) apl )

let rec loop : 'e. ('e tree,'e) APL.t -> 'e tree = function
  | APL.Zero -> Leaf
  | APL.TwicePlusOne (tree,PL.Zero) -> tree
  | APL.TwicePlusOne (tree,PL.TwicePlusOne (pair,apl)) ->
      loop (pass tree pair apl)

let singleton x = Node(Leaf,x,Leaf)
let balance l =
  loop (APL.of_list Leaf singleton (fun e->e) l)
