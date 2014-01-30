(** This file contains the implementation of the Coq version of the
    algorithm presented in Section 4. *)

Require Import Coq.Lists.List.
Import ListNotations.

Notation "⟨ x , y ⟩" := (existT _ x y).
Notation "f × g" := (fun xy => let '(x,y) := xy in (f x,g y))
                      (at level 40, left associativity).

(** Full trees have two constructor for leaves, as they can appear
    either at the lower level or at the level just above. The former
    builds a full tree of height 0, and the latter of height
    1. Alternatively, we could replace the lower leaf by a singleton
    constructor. *)
Inductive FullTree (A:Type) : nat -> Type :=
  | Leaf₀ : FullTree A 0
  | Leaf₁ : FullTree A 1
  | Node {k:nat} : FullTree A k -> A -> FullTree A k -> FullTree A (S k)
.
Arguments Leaf₀ {A}.
Arguments Leaf₁ {A}.
Arguments Node {A k} _ _ _.

Module BinaryList.

  (** [T A] is a variant of Okasaki's binary list where the first
      element is always accessible. It is used to make the completion
      to power lists procedure structurally recursive. From a
      numerical representation point of view, [T A] is a decorated
      version of the positive natural numbers written in binary base
      with digits [1] and [2]. *)
  Inductive T (A:Type) : Type :=
  | zero
  | tpo (a:A) (l:T (A*A))
  | tpt (a b: A) (l:T (A*A))
  .
  Arguments zero {A}.
  Arguments tpo {A} a l.
  Arguments tpt {A} a b l.

  (** [cons a l] adds an element [a] in front of the binary list
  [l]. It mimicks the successor operation in binary numbers (written
  with [1] and [2]). *)
  Fixpoint cons {A} (a:A) (l:T A) : T A :=
    match l with
    | zero => tpo a zero
    | tpo b l => tpt a b l
    | tpt b c l => tpo a (cons (b,c) l)
    end
  .

  (** Flattens a binary list of pairs of [A] into a binary list of
      [A]. It is analogue to multiplication by [2] in binary numbers
      written with [1] and [2]. *)
  Fixpoint twice {A} (l:T (A*A)) : T A :=
    match l with
    | zero => zero
    | tpo (a,b) l => tpt a b (twice l)
    | tpt (a,b) cd l => tpt a b (tpo cd l)
    end
  .

  (** Lists can be converted in linear time into binary lists by
      mapping [List.cons] to [cons] and [List.nil] to [zero]. *)
  Definition of_list {A} (l:list A) : T A :=
    List.fold_right cons zero l.

End BinaryList.

Module PowerList.

  (** The type of power lists is enriched compared to the Ocaml
      version: we keep the height as an argument. For the sake of
      simplicity, power lists are defined recursively rather than
      inductively. *)
  Fixpoint T (A:Type) (k:nat) :=
    match k with
    | 0 => unit:Type
    | S k' => (A * T (A*A) k')%type
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U (A:Type) := { k:nat & T A k }.
  Definition zero {A:Type} : U A := ⟨ 0 , tt ⟩.
  Definition tpo {A:Type} (a:A) (l:U (A*A)) : U A :=
    let '⟨k,l⟩ := l in
    ⟨ S k , (a,l) ⟩.

  (** [map] is the equivalent of [List.map]. *)
  Fixpoint map {A B k} (f:A->B) : T A k -> T B k :=
    match k with
    | 0 => fun t => tt
    | S k => fun t =>
      let '(x,l) := t in
      ( f x , map (f×f) l )
    end
  .

  Module BL := BinaryList.

  (** Instead of using [pair_up] at each recursive step as in the
      Ocaml version, we complete binary lists into power lists. In a
      sense, a binary list is the precomputation of all the necessary
      call to [pair_up]. *)
  Fixpoint of_binary_list {A X} (d:A->X) (f:A*A->X) (l:BL.T A) : U X :=
    match l with
    | BL.zero => zero
    | BL.tpo a l =>
      tpo (d a) (of_binary_list (d×d) (f×f) l)
    | BL.tpt a b l =>
      tpo (f (a,b)) (of_binary_list (d×d) (f×f) l)
    end
  .


End PowerList.

Module AlternatingPowerList.

  Module PL := PowerList.
  Module BL := BinaryList.

  (** Like [PowerList.T], [T] differs from the Ocaml version in that
      it is indexed by [k] and is defined recusively rather than
      inductively. *)
  Definition T (Odd Even:Type) (k:nat) : Type :=
    match k with
    | 0 => unit%type
    | S k => (Odd * PL.T (Even*Odd) k)%type
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U (Odd Even:Type) := { k:nat & T Odd Even k }.
  Definition zero {Odd Even:Type} : U Odd Even := ⟨ 0 , tt ⟩.
  Definition tpo {Odd Even:Type} (a:Odd) (l:PL.U (Even*Odd)) : U Odd Even :=
    let '⟨k,l⟩ := l in
    ⟨ S k , (a,l) ⟩.

  (** Lifts [PowerList.of_binary_list] two [T]. *)
  Definition of_binary_list {A Odd Even} (d:Odd) (f:A->Odd) (g:A->Even) (l:BL.T A) : U Odd Even :=
    match l with
    | BL.zero => zero
    | BL.tpo a l =>
      let d' x := ( g x , d ) in
      tpo (f a) (PL.of_binary_list d' (g×f) (BL.twice l))
    | BL.tpt a b l  =>
      let d' x := ( g x , d ) in
      tpo (f a) (PL.of_binary_list d' (g×f) (BL.tpo b l))
    end
  .

  (** Completes a list into an alternating power list. *)
  Definition of_list {A Odd Even} (d:Odd) (f:A->Odd) (g:A->Even) (l:list A) : U Odd Even :=
    of_binary_list d f g (BL.of_list l)
  .

End AlternatingPowerList.

Module BL := BinaryList.
Module PL := PowerList.
Module APL := AlternatingPowerList.

(** [pass] works just like the Ocaml version except that we can
    explicitely require an alternating power list of size [2^(k+2)-1]
    in the type (wereas in the Ocaml version we need to unfold it
    manually), and trees are now full by construction. The input trees
    have height [S p] and the output ones [S (S p)].  *)
Definition pass {A k p} (l:APL.T (FullTree A (S p)) A (S (S k))) : APL.T (FullTree A (S (S p))) A (S k) :=
  let '(t,((a,s),l')) := l in
  ( Node t a s , PL.map (fun q => let '((a,t),(b,s)) := q in ( a , Node t b s ) ) l' )
.

(** Alternative definition of [plus] on natural number which follows
    our recursion: S k + p = k + S p instead of S k + p = S(k+p). *)
Fixpoint plus (k p:nat) : nat :=
  match k with
  | 0 => p
  | S k => plus k (S p)
  end
.

(** [loop] iterates pass until there is a single full tree left.
    Contrary to the Ocaml version [loop] requires non empty
    alternating power lists (the empty case has been moved to
    [balance] below). This is due to a technicality in Coq's
    structural recursion checker. *)
Fixpoint loop {A k p} : APL.T (FullTree A (S p)) A (S k) -> FullTree A (plus k (S p)) :=
  match k with
  | 0 => fun t => let '(t,tt) := t in t
  | S k => fun l => loop (pass l)
  end
.


(** [balance l] turns [l] into a full tree. The height of the output
    tree is not specified in the type, as it is computed by
    [APL.of_list]. As mentionned in [loop] function, balance has to
    treat the empty case separately. *)
Definition singleton {A:Type} (x:A) : FullTree A 1 :=
  Node Leaf₀ x Leaf₀
.

Definition balance {A:Type} (l:list A) : { k:nat & FullTree A k } :=
  let '⟨k,l⟩ := APL.of_list Leaf₁ singleton (fun x=>x) l in
  match k with
  | 0 => fun _ => ⟨ 0 , Leaf₀ ⟩
  | S k => fun (l:APL.T _ _ (S k)) => ⟨ plus k 1 , loop l ⟩
  end l
.
