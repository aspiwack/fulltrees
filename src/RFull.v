(** This file contains a variant of the [Full.v] implementation using
    graphs instead of types to make order-preservation obvious.

    Only compile with Coq v8.5 (and maybe more recent versions). *)


(** A graph on type [A] is a function [A->A->Type], i.e. a proof
    relevant relation on [A]. They will play, in the file, the role of
    types of elements of the various containers. *)
Notation Graph A := (A -> A -> Type).

(** Paths of size two in a graph. Defined in a heterogeneous manner
    for clarity. They will replace pairs. *)
Inductive Pair {A B C} (G₁:A->B->Type) (G₂:B->C->Type) (a:A) (c:C) : Type :=
  comp : forall b, G₁ a b -> G₂ b c -> Pair G₁ G₂ a c.

Notation "G₁ * G₂" := (Pair G₁ G₂).
Notation "( x , y )" := (comp _ _ _ _ _ x y).

Definition times {A G₁ G₂ G₃ G₄}
           (f:forall a b:A, G₁ a b -> G₃ a b)
           (g:forall a b:A, G₂ a b -> G₄ a b)
        : forall a b:A, Pair G₁ G₂ a b -> Pair G₃ G₄ a b :=
  fun a b xy => let '(x,y) := xy in (f _ _ x,g _ _ y).
Notation "f × g" := (times f g) (at level 40, left associativity).


Notation "⟨ x , y ⟩" := (existT _ x y).

(** Paths in a graph generalize lists. *)
Inductive Path {A} (G:Graph A) (a:A) : A -> Type :=
| nil : Path G a a
| cons : forall b c, G a b -> Path G b c -> Path G a c
.
Arguments cons {A G a} b c x p.

Notation "[ ]" := (nil _ _).
Notation "x :: p" := (cons _ _ x p).

Section FoldRight.

  Context {A} {G₁ G₂:Graph A}.
  Context (f:forall a b c, G₁ a b -> G₂ b c -> G₂ a c).

  Fixpoint path_fold_right {a b c:A} (s:G₂ b c) (p:Path G₁ a b) : G₂ a c :=
    match p in Path _ _ b return G₂ b c -> G₂ a c with
    | [] => fun s => s
    | x::q => fun s => f _ _ _ x (path_fold_right s q)
    end s
  .

End FoldRight.

Definition append {A G} {a b c:A} (p₁:Path G a b) (p₂:Path G b c) : Path G a c :=
  path_fold_right (@cons _ _) p₂ p₁.

(** Full trees have two constructor for leaves, as they can appear
    either at the lower level or at the level just above. The former
    builds a full tree of height 0, and the latter of height
    1. Alternatively, we could replace the lower leaf by a singleton
    constructor. *)
Inductive FullTree {A} (G:Graph A) : nat -> Graph A :=
  | Leaf₀ {a:A} : FullTree G 0 a a
  | Leaf₁ {a:A} : FullTree G 1 a a
  | Node {k:nat} {a b c d:A} : FullTree G k a b -> G b c -> FullTree G k c d -> FullTree G (S k) a d
.
Arguments Leaf₀ {A G a}.
Arguments Leaf₁ {A G a}.
Arguments Node {A G k a b c d} _ _ _.

Module BinaryList.

  (** [T A] is a variant of Okasaki's binary list where the first
      element is always accessible. It is used to make the completion
      to power lists procedure structurally recursive. From a
      numerical representation point of view, [T A] is a decorated
      version of the positive natural numbers written in binary base
      with digits [1] and [2]. *)
  Inductive T {A} (G:Graph A) (a:A) : A -> Type :=
  | zero : T G a a
  | tpo (b c:A) (x:G a b) (l:T (G*G) b c) : T G a c
  | tpt (b c d:A) (x:G a b) (y:G b c) (l:T (G*G) c d) : T G a d
  .
  Arguments zero {A G a}.
  Arguments tpo {A G a b c} x l.
  Arguments tpt {A G a b c d} x y l.

  (** [cons a l] adds an element [a] in front of the binary list
  [l]. It mimicks the successor operation in binary numbers (written
  with [1] and [2]). *)
  Fixpoint cons {A G} {a b c:A} (x:G a b) (l:T G b c) : T G a c :=
    match l with
    | zero => tpo x zero
    | tpo y l => tpt x y l
    | tpt y z l => tpo x (cons (y,z) l)
    end
  .

  (** Flattens a binary list of pairs of [A] into a binary list of
      [A]. It is analogue to multiplication by [2] in binary numbers
      written with [1] and [2]. *)
  Fixpoint twice {A G} {a b:A} (l:T (G*G) a b) : T G a b:=
    match l with
    | zero => zero
    | tpo (a,b) l => tpt a b (twice l)
    | tpt (a,b) cd l => tpt a b (tpo cd l)
    end
  .

  (** Lists can be converted in linear time into binary lists by
      mapping [List.cons] to [cons] and [List.nil] to [zero]. *)
  Definition of_list {A G} {a b:A} (p:Path G a b) : T G a b :=
    path_fold_right (@cons A G) zero p.

End BinaryList.

Module PowerList.

  (** The type of power lists is enriched compared to the Ocaml
      version: we keep the height as an argument. For the sake of
      simplicity, power lists are defined recursively rather than
      inductively. *)
  Fixpoint T {A} (G:Graph A) (k:nat) : Graph A :=
    match k with
    | 0 => eq
    | S k' => G * T (G*G) k'
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U {A} (G:Graph A) : Graph A := fun a b => { k:nat & T G k a b}.
  Definition zero {A G} {a:A} : U G a a := ⟨ 0 , eq_refl ⟩.
  Definition tpo {A G} {a b c:A} (x:G a b) (l:U (G*G) b c) : U G a c :=
    let '⟨k,l⟩ := l in
    ⟨ S k , (x,l) ⟩.

  (** [map] is the equivalent of [List.map]. *)
  Fixpoint map {A G₁ G₂ k} (f:forall a b, G₁ a b -> G₂ a b) {a b:A}
     : T G₁ k a b-> T G₂ k a b :=
    match k with
    | 0 => fun e:a=b => e
    | S k => fun t =>
      let '(x,l) := t in
      ( f _ _ x , map (f×f) l )
    end
  .

  Module BL := BinaryList.

  (** Instead of using [pair_up] at each recursive step as in the
      Ocaml version, we complete binary lists into power lists. In a
      sense, a binary list is the precomputation of all the necessary
      call to [pair_up]. *)
  Fixpoint of_binary_list {A G X}
           (d:forall a b, G a b -> X a b)
           (f:forall a b, Pair G G a b -> X a b)
           {a b:A} (l:BL.T G a b) : U X a b :=
    match l with
    | BL.zero => zero
    | BL.tpo x l =>
      tpo (d _ _ x) (of_binary_list (d×d) (f×f) l)
    | BL.tpt x y l =>
      tpo (f _ _ (x,y)) (of_binary_list (d×d) (f×f) l)
    end
  .


End PowerList.

Module AlternatingPowerList.

  Module PL := PowerList.
  Module BL := BinaryList.

  (** Like [PowerList.T], [T] differs from the Ocaml version in that
      it is indexed by [k] and is defined recusively rather than
      inductively. *)
  Definition T {A} (Odd Even:Graph A) (k:nat) : Graph A :=
    match k with
    | 0 => eq
    | S k => Odd * PL.T (Even*Odd) k
    end
  .

  (** Variant of [T] with implicit height. *)
  Definition U {A} (Odd Even:Graph A) (a b:A) := { k:nat & T Odd Even k a b}.
  Definition zero {A} {Odd Even} {a:A} : U Odd Even a a := ⟨ 0 , eq_refl ⟩.
  Definition tpo {A} {Odd Even} {a b c:A}
             (x:Odd a b) (l:PL.U (Even*Odd) b c) : U Odd Even a c :=
    let '⟨k,l⟩ := l in
    ⟨ S k , (x,l) ⟩.

  (** Lifts [PowerList.of_binary_list] to [T]. *)
  Definition of_binary_list {A G Odd Even}
             (d:forall a, Odd a a)
             (f:forall a b, G a b -> Odd a b)
             (g:forall a b, G a b -> Even a b)
             {a b:A} (l:BL.T G a b) : U Odd Even a b:=
    match l with
    | BL.zero => zero
    | BL.tpo a l =>
      let d' _ _ x := ( g _ _ x , d _) in
      tpo (f _ _ a) (PL.of_binary_list d' (g×f) (BL.twice l))
    | BL.tpt a b l  =>
      let d' _ _ x := ( g _ _ x , d _ ) in
      tpo (f _ _ a) (PL.of_binary_list d' (g×f) (BL.tpo b l))
    end
  .

  (** Completes a list into an alternating power list. *)
  Definition of_path {A G Odd Even}
             (d:forall a, Odd a a)
             (f:forall a b, G a b -> Odd a b)
             (g:forall a b, G a b -> Even a b)
             {a b:A} (l:Path G a b) : U Odd Even a b :=
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
Definition pass {A G k p} {a b:A}
           (l:APL.T (FullTree G (S p)) G (S (S k)) a b)
       : APL.T (FullTree G (S (S p))) G (S k) a b :=
  let '(t,((x,s),l')) := l in
  ( Node t x s ,
    PL.map (fun a b q => let '((x,t),(y,s)) := q in ( x , Node t y s ) ) l' )
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

Fixpoint loop {A G k p} {a b:A}
    : APL.T (FullTree G (S p)) G (S k) a b -> FullTree G (plus k (S p)) a b :=
  match k with
  | 0 => fun t => let '(t,e) := t in let 'eq_refl := e in t
  | S k => fun l => loop (pass l)
  end
.


(** [balance l] turns [l] into a full tree. The height of the output
    tree is not specified in the type, as it is computed by
    [APL.of_list]. As mentionned in [loop] function, balance has to
    treat the empty case separately. *)
Definition singleton {A} {G:Graph A} {a b:A} (x:G a b) : FullTree G 1 a b:=
  Node Leaf₀ x Leaf₀
.

Definition balance {A} {G:Graph A} {a b:A} (p:Path G a b)
    : { k:nat & FullTree G k a b } :=
  let '⟨k,l⟩ := APL.of_path (@Leaf₁ _ _) (@singleton _ _) (fun _ _ x=>x) p in
  match k
  return (APL.T (FullTree G 1) G k a b -> {k : nat & FullTree G k a b})
  with
  | 0 => fun e => let 'eq_refl := e in ⟨ 0 , Leaf₀ ⟩
  | S k => fun q => ⟨ plus k 1 , loop q ⟩
  end l
.



(** In-order traversal of full trees *)

Fixpoint in_order {A} {G:Graph A} {k} {a b:A} (t:FullTree G k a b)
    : Path G a b :=
  match t with
  | Leaf₀ => []
  | Leaf₁ => []
  | Node t₁ x t₂ => append (in_order t₁) (x::(in_order t₂))
  end
.


Corollary order_preservation : forall A G (a b:A) (p:Path G a b),
   in_order (projT2 (balance p)) = p.
Proof.
Abort.