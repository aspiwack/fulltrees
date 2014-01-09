Require Import Coq.Lists.List.
Import ListNotations.
Require Import Full.

Module BL := BinaryList.
Module PL := PowerList.
Module APL := AlternatingPowerList.

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
      let f' xy := let '(x,y) := xy in f x ++ f y in
      f x ++ (list_of_binary_list f' l)
    | BL.tpt x y l =>
      let f' xy := let '(x,y) := xy in f x ++ f y in
      f x ++ f y ++ (list_of_binary_list f' l)
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
    list_of_binary_list f (BL.twice l) = list_of_binary_list (fun xy => let '(x,y) := xy in f x ++ f y) l.
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


  Fixpoint list_of_powerlist_n {A B X n} (f:A->list X) (g:B->list X) : PL.T (A * B) n -> list X :=
    match n with
    | 0 => fun (xt:PL.T _ 0) => let '(x,t) := xt in f x ++ g t
    | S n => fun l => let '((x,t),l) := l in
      let f' ab := let '(a,b) := ab in f a ++ g b in
      f x ++ g t ++ list_of_powerlist_n f' f' l
    end
  .

  Fixpoint list_of_powerlist {A B X} (f:A->list X) (g:B->list X) (l:PL.U (A*B)) : list X :=
    list_of_powerlist_n f g (projT2 l)
  .

  Remark list_of_powerlist_tpo  {A B X} (f:A->list X) (g:B->list X) (xy:A*B) (l:PL.U((A*B)*(A*B))) :
    list_of_powerlist f g (PL.tpo xy l) = (let '(x,y) := xy in f x ++ g y) ++ list_of_powerlist (fun ab => let '(a,b) := ab in f a ++ g b) (fun ab => let '(a,b) := ab in f a ++ g b) l.
  Proof.
    destruct xy as [x y]; destruct l as [ n l ]; simpl.
    rewrite <- !app_assoc.
    reflexivity.
  Qed.

  Lemma power_list_of_binary_list_preserves_order A B E O (d:A->E*O) (f:A->O) (g:A->E) (rf:O->list B) (rg:E->list B) (h:A->list B) (l:BL.T A) :
    (forall a, (let '(x,t):=d a in rg x ++ rf t) = h a) ->
    (forall a, rf (f a) = h a) ->
    (forall a, rg (g a) = h a) ->
  list_of_powerlist rg rf (PL.of_blist_pairing_with_cast d f g l) = list_of_binary_list h l.
  Proof.
    revert B E O d f g rf rg h.
    induction l as [ | | A x l hl | A x y l hl ]; intros B E O d f g rf rg h hd hf hg;
      [ simpl; rewrite ?hd,?hf,?hg; reflexivity .. | | ].
    + (* case l=tpo x l *)
      simpl.
      rewrite list_of_powerlist_tpo.
      rewrite hd.
      rewrite hl with (h:=(fun xy : A * A => let '(x0, y) := xy in h x0 ++ h y));
        [ | intros [? ?]; simpl; rewrite ?hd,?hf,?hg; reflexivity ..].
      reflexivity.
    + (* case l=tpt x y l *)
      simpl.
      rewrite list_of_powerlist_tpo.
      rewrite ?hf,?hg,<-!app_assoc.
      rewrite hl with (h:=(fun xy : A * A => let '(x0, y) := xy in h x0 ++ h y));
        [ | intros [? ?]; simpl; rewrite ?hd,?hf,?hg; reflexivity ..].
      reflexivity.
  Qed.

  Definition list_of_alternating_powerlist_n {A B X n} (f:A->list X) (g:B->list X) : APL.T A B n -> list X :=
    match n with
    | 0 => fun (x:APL.T _ _ 0) => f x
    | S n => fun l => let '(x,l) := l in
      f x ++ list_of_powerlist_n g f l
    end
  .

  Definition list_of_alternating_powerlist {A B X} (f:A->list X) (g:B->list X) (l:APL.U A B) : list X :=
    list_of_alternating_powerlist_n f g (projT2 l)
  .

  Remark list_of_alternating_powerlist_tpo  {A B X} (f:A->list X) (g:B->list X) (x:A) (l:PL.U (B*A)) :
    list_of_alternating_powerlist f g (APL.tpo x l) = f x ++ list_of_powerlist g f l.
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
      rewrite power_list_of_binary_list_preserves_order with (h:=(fun xy : A * A => let '(x0, y0) := xy in h x0 ++ h y0));
        [ | intros [? ?]; rewrite ?hd,?hf,?hg,?app_nil_r; reflexivity .. ].
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

  Lemma powerlist_map_preserves_order A₁ A₂ B₁ B₂ C n (f:A₁*A₂->B₁*B₂) (h₁:A₁->list C) (h₂:A₂->list C) (h₃:B₁->list C) (h₄:B₂->list C) (l:PL.T (A₁*A₂) n) :
    (forall x, h₃(fst (f x))++h₄(snd (f x)) = h₁ (fst x) ++ h₂ (snd x)) ->
    list_of_powerlist_n h₃ h₄ (PL.map f l) = list_of_powerlist_n h₁ h₂ l.
  Proof.
    revert A₁ A₂ B₁ B₂ C f h₁ h₂ h₃ h₄ l.
    induction n as [ | n' hn ]; intros A₁ A₂ B₁ B₂ C f h₁ h₂ h₃ h₄ l p.
    + (* case n=0 *)
      simpl.
      specialize (p l).
      destruct (f l); simpl in p|-.
      rewrite p.
      destruct l; reflexivity.
    + (* case n=S n' *)
      simpl.
      destruct l as [ [ x t ] l ].
      generalize (p (x,t)); intros p'; simpl in p'.
      destruct (f (x,t)); simpl in p'.
      rewrite !app_assoc.
      rewrite p'.
      rewrite hn with (h₁ := (fun ab : A₁ * A₂ => let '(a, b1) := ab in h₁ a ++ h₂ b1))
                      (h₂ := (fun ab : A₁ * A₂ => let '(a, b1) := ab in h₁ a ++ h₂ b1)).
      { reflexivity. }
      intros [[y z] [v w]]; simpl.
      clear p'.
      generalize (p (y,z)); intros p'; simpl in p'; rewrite <- p'; clear p'.
      generalize (p (v,w)); intros p'; simpl in p'; rewrite <- p'; clear p'.
      destruct (f(y,z)); destruct (f(v,w)).
      easy.
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
      rewrite powerlist_map_preserves_order with (h₁:=(fun ab => let '(a0, b) := ab in a0 :: list_of_full_tree_n b)) (h₂:=(fun ab => let '(a0, b) := ab in a0 :: list_of_full_tree_n b)).
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