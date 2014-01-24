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
  element is always explicit. The reason for this type is that the
  tail of [l] or the tail of its tail is structurally smaller than
  [l]. Which we will make use of to reconstruct power-lists. From a
  number system point of view, [T A] is an decorated version of the
  positive natural numbers written in binary base with digits [1] and
  [2]. *)
  Inductive T (A:Type) : Type :=
  | zero
  | tpo (a:A) (l:T (A*A))
  | tpt (a b: A) (l:T (A*A))
  .
  Arguments zero {A}.
  Arguments tpo {A} a l.
  Arguments tpt {A} a b l.

  Fixpoint cons {A} (a:A) (l:T A) : T A :=
    match l with
    | zero => tpo a zero
    | tpo b l => tpt a b l
    | tpt b c l => tpo a (cons (b,c) l)
    end
  .

  Fixpoint twice {A} (l:T (A*A)) : T A :=
    match l with
    | zero => zero
    | tpo (a,b) l => tpt a b (twice l)
    | tpt (a,b) cd l => tpt a b (tpo cd l)
    end
  .

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

  Fixpoint map {A B k} (f:A->B) : T A k -> T B k :=
    match k with
    | 0 => fun t => tt
    | S k => fun t =>
      let '(x,l) := t in
      ( f x , map (f×f) l )
    end
  .

  Module BL := BinaryList.

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

  Definition of_list {A Odd Even} (d:Odd) (f:A->Odd) (g:A->Even) (l:list A) : U Odd Even :=
    of_binary_list d f g (BL.of_list l)
  .

End AlternatingPowerList.

Module BL := BinaryList.
Module PL := PowerList.
Module APL := AlternatingPowerList.

Definition pass {A k p} (l:APL.T (FullTree A (S p)) A (S (S k))) : APL.T (FullTree A (S (S p))) A (S k) :=
  let '(t,((a,s),l')) := l in
  ( Node t a s , PL.map (fun q => let '((a,t),(b,s)) := q in ( a , Node t b s ) ) l' )
.

(** Alternative definition of [plus] which follows our recursion. *)
Fixpoint plus (k p:nat) : nat :=
  match k with
  | 0 => p
  | S k => plus k (S p)
  end
.

Fixpoint loop {A k p} : APL.T (FullTree A (S p)) A (S k) -> FullTree A (plus k (S p)) :=
  match k with
  | 0 => fun t => let '(t,tt) := t in t
  | S k => fun l => loop (pass l)
  end
.


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
