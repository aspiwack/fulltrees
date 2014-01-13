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

      To read the ['a t] type, notice that there is always an element
      available. It is the first (possibly unique) element of the
      list. If there are other elements, then the next head is a pair
      [(b,c)]: the second and third elements. If there are still more
      elements, then the next head of head is a pair of pairs
      [((d,e),(f,g))]: [d] is the fourth element, [e] the fifth, [f]
      the sixth, and [g] the seventh. And so on. *)
  type 'a t =
    | One of 'a
    | TwicePlusOne of 'a * ('a*'a) t

  (** [map f l] is the functorial action of [f] on the powerlist [l]. *)
  let rec map : 'a 'b. ('a->'b) -> 'a t -> 'b t = fun f l ->
    match l with
    | One x -> One (f x)
    | TwicePlusOne (x,l) ->
        let f' (x,y) = f x , f y in
        TwicePlusOne ( f x , map f' l)

  (** [pair_up l] takes the non-empty list [l] and returns, if [l] has
      even length [Even a b,l'] where [(a,b)::l'] has consecutive
      elements of [l] paired up, otherwise [Odd a,l'] where [l'] is
      the (possibly empty) list of consecutive elements of [l.tl]
      paired up. *)
  type 'a eo =
    | Odd of 'a
    | Even of ('a*'a)
  let rec pair_up hd = function
    | [] -> Odd hd , []
    | b::l ->
        begin match pair_up b l with
        | Even bc,l' -> Odd hd , bc::l'
        | Odd b,l' -> Even (hd,b) , l'
        end


  (** Given a casting function ['a->'b], we can construct an ['a t]
      from a non-empty ['a list] of any size, but it requires padding. The
      idea is to insert a default value [d0:'b] when needed to complete
      the list to an appropriate length. However, because the recursive
      step does not allow it, we cannot use a [d0] as the argument for
      padding, instead, we use a function [d:'a->'b*'b]. At the first step
      of the recursion, [d] is expected to be of the form [fun a -> (d0,f
      x)], effectively inserting [d0] in front of the current value. *)
  let rec of_ne_list : 'a 'b. ('a->'b*'b) -> ('a->'b) -> 'b -> 'a list -> 'b t =
    fun d f b l ->
    let cast = function
      | Odd a -> d a
      | Even (a,b) -> (f a, f b)
    in
    match l with
    | [] -> One b
    | a::l ->
        let d' (x,y) = (d x , d y) in
        let f' (x,y) = (f x , f y) in
        let (a',l') = pair_up a l in
        TwicePlusOne ( b , of_ne_list d' f' (cast a') l' )

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
    | One of 'odd
    | TwicePlusOne of 'odd * ('even*'odd) PowerList.t


  (** We build an [('odd,'even) t] from an ['a list] using a default
      ['odd] value for padding, a function [f:'a -> 'odd] for odd
      positions, and [g:'a -> 'even] for even positions. *)
  let of_list d f g = function
    | [] -> One d
    | [a] -> One (f a)
    | a::b::l ->
        let d' x = g x , d in
        let fg (x,y) = g x , f y in
        let dd (x,y) = d' x , d' y in
        let (b',l') = PowerList.pair_up b l in
        let b'' =
          match b' with
          | PowerList.Odd b -> d' b
          | PowerList.Even bc -> fg bc
        in
        TwicePlusOne ( f a , PowerList.of_ne_list dd fg b'' l')

end

module PL = PowerList
module APL = AlternatingPowerList


(** [pass join t l] takes a non-empty alternating power list
    [APL.TwicePlusOne(t,l)], and groups the consecutive triplets using
    [Node]: the three first elements (of respective types ['o],
    ['e] and ['o]) are joined, then for each group of four elements
    (of type [('e,'o),('e,'o)]) the first one is kept as such, and the
    three others can be joined. *)
let pass : 'a. 'a tree -> ('a*'a tree) PL.t -> ('a tree,'a) APL.t =
  fun t l ->
    match l with
    | PL.One (a,s) -> APL.One (Node(t,a,s))
    | PL.TwicePlusOne((a,s),l) ->
        APL.TwicePlusOne ( Node(t,a,s) ,
                           PL.map (fun ((a,t),(b,s)) -> a , Node(t,b,s) ) l )

let rec balance_powerlist : 'e. ('e tree,'e) APL.t -> 'e tree = function
  | APL.One t -> t
  | APL.TwicePlusOne (t,l) ->
      balance_powerlist (pass t l)

let singleton x = Node(Leaf,x,Leaf)
let balance l =
  balance_powerlist (APL.of_list Leaf singleton (fun e->e) l)
