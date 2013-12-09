Require Import Coq.Lists.List.
Import ListNotations.

Notation "⟨ T , x , y ⟩" := (existT T x y).

(** Full trees have two constructor for leaves, as they can appear
    either at the lower level or at the level just above. The former
    builds a full tree of height 0, and the latter of height
    1. Alternatively, we could replace the lower leaf by a singleton
    constructor. *)

Inductive FullTree (A:Type) : nat -> Type :=
  | Leaf₀ : FullTree A 0
  | Leaf₁ : FullTree A 1
  | Node {n:nat} : FullTree A n -> A -> FullTree A n -> FullTree A (S n)
.
Arguments Leaf₀ {A}.
Arguments Leaf₁ {A}.
Arguments Node {A n} _ _ _.

Module BinaryList.

  (** [T A] is a variant of Okasaki's binary list where the first
  element is always explicit. The reason for this type is that the
  tail of [l] or the tail of its tail is structurally smaller than
  [l]. Which we will make use of to reconstruct power-lists. From a
  number system point of view, [T A] is an decorated version of the
  positive natural numbers written in binary base with digits [1] and
  [2]. *)
  Inductive T (A:Type) : Type :=
  | one (a:A)
  | two (a b:A)
  | tpo (a:A) (l:T (A*A))
  | tpt (a b: A) (l:T (A*A))
  .
  Arguments one {A} a.
  Arguments two {A} a b.
  Arguments tpo {A} a l.
  Arguments tpt {A} a b l.

  Fixpoint cons {A} (a:A) (l:T A) : T A :=
    match l with
    | one b => two a b
    | two b c => tpo a (one (b,c))
    | tpo b l => tpt a b l
    | tpt b c l => tpo a (cons (b,c) l)
    end
  .

  Fixpoint twice {A} (l:T (A*A)) : T A :=
    match l with
    | one (a,b) => two a b
    | two (a,b) cd => tpt a b (one cd)
    | tpo (a,b) l => tpt a b (twice l)
    | tpt (a,b) cd l => tpt a b (tpo cd l)
    end
  .

  Fixpoint of_ne_list {A} (a:A) (l:list A) : T A :=
    match l with
    | [] => one a
    | b::l => cons a (of_ne_list b l)
    end
  .

End BinaryList.

Module PowerList.

  (** The type of power lists is enriched compared to the Ocaml
      version: we keep the height as an argument. For the sake of
      simplicity, power lists are defined recursively rather than
      inductively. *)
  Fixpoint T (A:Type) (n:nat) :=
    match n with
    | 0 => A
    | S n' => (A * T (A*A) n')%type
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U (A:Type) := { n:nat & T A n }.
  Definition one {A:Type} (a:A) : U A := ⟨ T A , 0 , a ⟩.
  Definition tpo {A:Type} (a:A) (l:U (A*A)) : U A :=
    let '(existT n  l) := l in
    ⟨ T A , S n , (a,l) ⟩.

  Fixpoint map {A B n} (f:A->B) : T A n -> T B n :=
    match n with
    | 0 => fun t => f t
    | S n => fun t =>
      let f' xy := let '(x,y) := xy in (f x,f y) in
      let '(x,l) := t in
      ( f x , map f' l )
    end
  .

  Module BL := BinaryList.

  Fixpoint of_blist_pairing_with_cast {A O E} (d:A->E*O) (f:A->O) (g:A->E) (l:BL.T A) : U (E*O) :=
    match l with
    | BL.one a => one (d a)
    | BL.two a b => one (g a , f b)
    | BL.tpo a l =>
      let d' xy := let '(x,y) := xy in (d x , d y) in
      let f' xy := let '(x,y) := xy in (g x , f y) in
      tpo (d a) (of_blist_pairing_with_cast d' f' f' l)
    | BL.tpt a b l =>
      let d' xy := let '(x,y) := xy in (d x , d y) in
      let f' xy := let '(x,y) := xy in (g x , f y) in
      tpo (g a,f b) (of_blist_pairing_with_cast d' f' f' l)
    end
  .

End PowerList.

Module AlternatingPowerList.

  Module PL := PowerList.
  Module BL := BinaryList.

  Definition T (Odd Even:Type) (n:nat) : Type :=
    match n with
    | 0 => Odd
    | S n => (Odd * PL.T (Even*Odd) n)%type
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U (Odd Even:Type) := { n:nat & T Odd Even n }.
  Definition one {Odd Even:Type} (a:Odd) : U Odd Even := ⟨ T Odd Even , 0 , a ⟩.
  Definition tpo {Odd Even:Type} (a:Odd) (l:PL.U (Even*Odd)) : U Odd Even :=
    let '(existT n  l) := l in
    ⟨ T Odd Even , S n , (a,l) ⟩.

  Definition of_binary_list {A Odd Even} (d:Odd) (f:A->Odd) (g:A->Even) (l:BL.T A) : U Odd Even :=
    match l with
    | BL.one a => one (f a)
    | BL.two a b => tpo (f a) (PL.one (g b , d))
    | BL.tpo a l =>
      let d' x := ( g x , d ) in
      tpo (f a) (PL.of_blist_pairing_with_cast d' f g (BL.twice l))
    | BL.tpt a b l  =>
      let d' x := ( g x , d ) in
      tpo (f a) (PL.of_blist_pairing_with_cast d' f g (BL.tpo b l))
    end
  .

  Definition of_list {A Odd Even} (d:Odd) (f:A->Odd) (g:A->Even) (l:list A) : U Odd Even :=
    match l with
    | [] => one d
    | a::l =>
      of_binary_list d f g (BL.of_ne_list a l)
    end
  .

End AlternatingPowerList.

Module BL := BinaryList.
Module PL := PowerList.
Module APL := AlternatingPowerList.

Definition pass {A n p} : APL.T (FullTree A (S p)) A (S n) -> APL.T (FullTree A (S (S p))) A n :=
  match n with
  | 0 =>    fun l =>
              let '(t,(a,s)) := l in
              Node t a s
  | S n' => fun l =>
              let '(t,((a,s),l)) := l in
              ( Node t a s ,
                PL.map (fun q => let '((a,t),(b,s)) := q in ( a , Node t b s ) ) l )
  end
.

(** Alternative definition of [plus] which follows our recursion. *)
Fixpoint plus (n p:nat) : nat :=
  match n with
  | 0 => p
  | S n => plus n (S p)
  end
.

Fixpoint balance_powerlist {A n p} : APL.T (FullTree A (S p)) A n -> FullTree A (plus n (S p)) :=
  match n with
  | 0 => fun t => t
  | S n => fun l => balance_powerlist (pass l)
  end
.

Definition singleton {A:Type} (x:A) : FullTree A 1 :=
  Node Leaf₀ x Leaf₀
.

Definition balance {A:Type} (l:list A) : { n:nat & FullTree A n } :=
  let '(existT n l') := APL.of_list Leaf₁ singleton (fun x=>x) l in
  ⟨ _ , plus n 1 , balance_powerlist l' ⟩
.