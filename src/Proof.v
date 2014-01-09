Require Import Coq.Lists.List.
Import ListNotations.
Require Import Full.

Module BL := BinaryList.
Module PL := PowerList.
Module APL := AlternatingPowerList.

Notation "f '+++' g" := (fun xy => let '(x,y) := xy in f x ++ g y)
                      (at level 60, right associativity).

(** In this file we show that the order of the element of the list is
    indeed preserved by the transformations. *)
Fixpoint list_of_full_tree_n {A n} (t:FullTree A n) : list A :=
  match t with
  | Leaf₀ => []
  | Leaf₁ => []
  | Node _ t₁ x t₂ => list_of_full_tree_n t₁ ++ [x] ++ list_of_full_tree_n t₂
  end
.

Definition list_of_full_tree {A} (t:{ n:nat & FullTree A n }) : list A :=
  list_of_full_tree_n (projT2 t)
.

Theorem balance_preserves_order A (l:list A) : list_of_full_tree (balance l) = l.



  Fixpoint list_of_binary_list {A B} (f:A->list B) (l:BL.T A) : list B :=
    match l with
    | BL.one x => f x
    | BL.two x y => f x ++ f y
    | BL.tpo x l =>
      f x ++ (list_of_binary_list (f+++f) l)
    | BL.tpt x y l =>
      f x ++ f y ++ (list_of_binary_list (f+++f) l)
    end
  .

  Lemma binary_list_cons_preserves_order A B (f:A->list B) (x:A) (l:BL.T A) :
    list_of_binary_list f (BL.cons x l) = f x ++ (list_of_binary_list f l).
  Proof.
    revert x; induction l as [ | | | A x y l hl ]; [ reflexivity .. | ].
    + intros z; simpl.
      rewrite hl; simpl.
      rewrite <- !app_assoc.
      reflexivity.
  Qed.

  Lemma binary_list_twice_preserves_order A B (f:A->list B) (l:BL.T (A*A)) :
    list_of_binary_list f (BL.twice l) = list_of_binary_list (f+++f) l.
  Proof.
    revert A B f l.
    (* because of typing issue, [induction] doesn't work. We use a fixpoint directly. *)
    fix 4.
    { intros A B f [ [? ?] | [? ?] [? ?] | [a b] l | [? ?] ? ? ];
        try solve [simpl;rewrite <-?app_assoc;reflexivity].
      simpl; rewrite <-?app_assoc.
      rewrite binary_list_twice_preserves_order.
      reflexivity. }
  Qed.

  Lemma binary_list_of_ne_list_preserves_order A B (f:A->list B) (x:A) (l:list A) :
    list_of_binary_list f (BL.of_ne_list x l) = f x ++ flat_map f l.
  Proof.
    revert x; induction l as [| x l hl ].
    + (* case l=[] *)
      intros **; simpl.
      rewrite app_nil_r.
      reflexivity.
    + (* case l=x::l *)
      intros y; simpl.
      rewrite binary_list_cons_preserves_order.
      rewrite hl.
      reflexivity.
  Qed.


  Fixpoint list_of_powerlist_n {A X n} (f:A->list X) : PL.T A n -> list X :=
    match n with
    | 0 => fun x => f x
    | S n => fun l => let '(x,l) := l in
      f x ++ list_of_powerlist_n (f+++f) l
    end
  .

  Fixpoint list_of_powerlist {A X} (f:A->list X) (l:PL.U A) : list X :=
    list_of_powerlist_n f (projT2 l)
  .

  Remark list_of_powerlist_tpo  {A X} (f:A->list X) (x:A) (l:PL.U (A*A)) :
    list_of_powerlist f (PL.tpo x l)
    = f x ++ list_of_powerlist (f+++f) l.
  Proof.
    destruct l as [ n l ]; simpl.
    reflexivity.
  Qed.

  Lemma power_list_of_binary_list_preserves_order A B X (d:A->B) (f:A*A->B) (r:B->list X) (h:A->list X) (l:BL.T A) :
    (forall a, r (d a) = h a) ->
    (forall a b, r (f (a,b)) = h a ++ h b) ->
  list_of_powerlist r (PL.of_blist_pairing_with_cast d f l) = list_of_binary_list h l.
  Proof.
    revert B X d f r h.
    induction l as [ | | A x l hl | A x y l hl ]; intros B X d f r h hd hf;
      [ simpl; rewrite ?hd,?hf; reflexivity .. | | ].
    + (* case l=tpo x l *)
      simpl.
      rewrite list_of_powerlist_tpo.
      rewrite hd.
      rewrite hl with (h:=h+++h);
        [ | intros [? ?]; try intros [? ?]; simpl; rewrite ?hd,?hf; reflexivity.. ].
      reflexivity.
    + (* case l=tpt x y l *)
      simpl.
      rewrite list_of_powerlist_tpo.
      rewrite ?hf,?hg,<-!app_assoc.
      rewrite hl with (h:=h+++h);
        [ | intros [? ?]; try intros [? ?]; simpl; rewrite ?hd,?hf; reflexivity ..].
      reflexivity.
  Qed.

  Definition list_of_alternating_powerlist_n {A B X n} (f:A->list X) (g:B->list X) : APL.T A B n -> list X :=
    match n with
    | 0 => fun (x:APL.T _ _ 0) => f x
    | S n => fun l => let '(x,l) := l in
      let f' xy := let '(x,y) := xy in g x ++ f y in
      f x ++ list_of_powerlist_n f' l
    end
  .

  Definition list_of_alternating_powerlist {A B X} (f:A->list X) (g:B->list X) (l:APL.U A B) : list X :=
    list_of_alternating_powerlist_n f g (projT2 l)
  .

  Remark list_of_alternating_powerlist_tpo  {A B X} (f:A->list X) (g:B->list X) (x:A) (l:PL.U (B*A)) :
    list_of_alternating_powerlist f g (APL.tpo x l) = f x ++ list_of_powerlist (g+++f) l.
  Proof.
    destruct l as [ n l ]; simpl.
    reflexivity.
  Qed.

  Lemma alternating_power_list_of_binary_list_preserves_order A B E O (d:O) (f:A->O) (g:A->E) (rf:O->list B) (rg:E->list B) (h:A->list B) (l:BL.T A) :
    rf d = [] ->
    (forall a, rf (f a) = h a) ->
    (forall a, rg (g a) = h a) ->
  list_of_alternating_powerlist rf rg (APL.of_binary_list d f g l) = list_of_binary_list h l.
  Proof.
    intros hd hf hg.
    destruct l as [ | | x l | x y l ];
      [ unfold list_of_alternating_powerlist; simpl; rewrite ?hd,?hf,?hg,?app_nil_r; reflexivity .. | | ].
    + (* case l=tpo x l *)
      simpl.
      rewrite list_of_alternating_powerlist_tpo, hf.
      rewrite power_list_of_binary_list_preserves_order with (h:=h);
        [ | intros **; rewrite ?hd,?hf,?hg,?app_nil_r; reflexivity .. ].
      simpl.
      rewrite binary_list_twice_preserves_order.
      reflexivity.
    + (* case l=tpt x y l *)
      simpl.
      rewrite list_of_alternating_powerlist_tpo, hf.
      rewrite list_of_powerlist_tpo, hg, hd, app_nil_r.
      rewrite power_list_of_binary_list_preserves_order with (h:=h+++h);
        [ | intros [? ?]; try intros [? ?]; rewrite ?hd,?hf,?hg,?app_nil_r; reflexivity .. ].
      reflexivity.
  Qed.

  Lemma alternating_power_list_of_list_preserves_order A B E O (d:O) (f:A->O) (g:A->E) (rf:O->list B) (rg:E->list B) (h:A->list B) (l:list A) :
    rf d = [] ->
    (forall a, rf (f a) = h a) ->
    (forall a, rg (g a) = h a) ->
  list_of_alternating_powerlist rf rg (APL.of_list d f g l) = flat_map h l.
  Proof.
    intros hd hf hg.
    destruct l as [ | x l ].
    + (* case l=[] *)
      unfold list_of_alternating_powerlist; simpl.
      rewrite hd.
      reflexivity.
    + (* case l=x::l *)
      simpl.
      rewrite <- binary_list_of_ne_list_preserves_order.
      apply alternating_power_list_of_binary_list_preserves_order;
        solve[intros **; rewrite ?hd,?hf,?hg; reflexivity].
  Qed.

  Lemma powerlist_map_preserves_order A B C n (f:A->B) (h₁:A->list C) (h₂:B->list C) (l:PL.T A n) :
    (forall x, h₂ (f x) = h₁ x) ->
    list_of_powerlist_n h₂ (PL.map f l) = list_of_powerlist_n h₁ l.
  Proof.
    revert A B C f h₁ h₂ l.
    induction n as [ | n' hn ]; intros A B C f h₁ h₂ l p.
    + (* case n=0 *)
      simpl.
      apply p.
    + (* case n=S n' *)
      simpl.
      destruct l as [ x l ].
      rewrite p.
      rewrite hn with  (h₁ := h₁+++h₁) (h₂ := (h₂+++h₂)).
      { reflexivity. }
      intros [ y z ]; simpl.
      rewrite !p.
      reflexivity.
  Qed.

  Definition unit {A} : A->list A := fun x => [x].

  Lemma pass_preserves_order A n p (l:APL.T (FullTree A (S p)) A (S n)) :
    list_of_alternating_powerlist_n list_of_full_tree_n unit (pass l) =
    list_of_alternating_powerlist_n list_of_full_tree_n unit l.
  Proof.
    destruct n as [ | n' ].
    + (* case n=0 *)
      destruct l as [ t [ a s ]]; simpl.
      reflexivity.
    + (* case n=S n' *)
      destruct l as [ t [ [ a s ] l ]]; simpl.
      rewrite <-!app_assoc, !app_comm_cons.
      rewrite powerlist_map_preserves_order with (h₂ := fun xy => let '(x, y) := xy in x :: list_of_full_tree_n y) (h₁ := fun xy => let '(x, y) := xy in (let '(x0, y0) := x in x0 :: list_of_full_tree_n y0) ++ (let '(x0, y0) := y in x0 :: list_of_full_tree_n y0)).
      { reflexivity. }
      intros [[x y][z w]]; reflexivity.
  Qed.

  Lemma balance_powerlist_preserves_order A n p (l:APL.T (FullTree A (S p)) A n) :
    list_of_full_tree_n (balance_powerlist l) =
    list_of_alternating_powerlist_n list_of_full_tree_n unit l.
  Proof.
    revert p l.
    induction n as [ | n' hn ]; intros p l.
    + (* case n=0 *)
      reflexivity.
    + (* case n=S n' *)
      simpl.
      rewrite hn.
      rewrite pass_preserves_order.
      destruct l as [ x l ].
      reflexivity.
  Qed.

Proof.
  (** Proof of the theorem *)
  unfold balance, list_of_full_tree.
  remember (Full.APL.of_list Leaf₁ singleton (fun x : A => x) l) as l' eqn:h.
  destruct l' as [ x l' ]; simpl.
  rewrite balance_powerlist_preserves_order.
  change (list_of_alternating_powerlist_n list_of_full_tree_n unit l')
     with (list_of_alternating_powerlist list_of_full_tree_n unit ⟨fun n : nat => Full.APL.T (FullTree A 1) A n, x, l' ⟩).
  rewrite h.
  rewrite alternating_power_list_of_list_preserves_order with (h:=unit);
    [ | reflexivity .. ].
  { clear.
    induction l as [ | x l hl ].
    + reflexivity.
    + simpl.
      now rewrite hl. }
Qed.