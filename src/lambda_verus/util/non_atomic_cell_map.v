From iris.prelude Require Import options.
From lrust.lang Require Import lang.
Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
From lrust.util Require Import cellmap update.
Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes excl gmap_view.
From iris.base_logic.lib Require Export own iprop invariants.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics.

Local Open Scope nat_scope.

(** Non-atomic map. **)

Definition ReadWriteState := lock_state.

Definition naN : namespace := nroot .@ "leaf_lifetime_logic" .@ "guarding".

(* begin hide *)

Section NonAtomicInternals.

  Context `{!EqDecision L, !Countable L}.
  Context {V: Type}.
  
  Implicit Types (σ: gmap L (ReadWriteState * V)).

  Local Definition erase_count_map {L} {V} `{!EqDecision L, !Countable L} (σ: gmap L (ReadWriteState * V)) : gmap L V := snd <$> σ.
    
  Local Definition heap_count_r (σ: gmap L (ReadWriteState * V)) (l : L) : nat :=
      match σ !! l with
        | None => 0
        | Some (WSt, v) => 0
        | Some (RSt n, v) => n
      end.
      
  Local Definition heap_count_w (σ: gmap L (ReadWriteState * V)) (l : L) : nat :=
      match σ !! l with
        | None => 0
        | Some (WSt, v) => 1
        | Some (RSt n, v) => 0
      end.
  
  Local Definition m_count {B} (m : gmap (L * nat) B) (l : L) : nat :=
      length (filter (λ p , p.1.1 = l) (map_to_list m)).
      
  Local Definition counts_agree_r {B} (σ: gmap L (ReadWriteState * V)) (m : gmap (L * nat) B)
    : Prop := ∀ l, heap_count_r σ l = m_count m l.
    
  Local Definition counts_agree_w {B} (σ: gmap L (ReadWriteState * V)) (m : gmap (L * nat) B)
    : Prop := ∀ l, heap_count_w σ l = m_count m l.
    
  Local Lemma length_filter_ex {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A)
    : length (filter P l) ≠ 0%nat → ∃ a , P a ∧ a ∈ l.
  Proof.
    induction l as [|a l IHl].
    - intros lf. contradiction.
    - intros lf. rewrite filter_cons in lf.
      destruct (decide (P a)) as [h|h].
      + exists a. rewrite elem_of_cons. intuition.
      + destruct (IHl lf) as [a2 [pa al]]. exists a2. rewrite elem_of_cons. intuition.
  Qed.
  
  Local Lemma length_filter_ex_rev {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A) (a: A)
    : P a → a ∈ l → length (filter P l) ≠ 0%nat.
  Proof.
    intros pa a_in_l lzero.
    rewrite length_zero_iff_nil in lzero.
    assert (a ∈ filter P l) as H.
    { rewrite elem_of_list_filter. split; trivial. }
    rewrite lzero in H. rewrite elem_of_nil in H. trivial.
  Qed.
  
  Local Lemma m_count_get1 {B} (m : gmap (L * nat) B) (l : L)
      : (m_count m l ≠ 0%nat) → ∃ i j , m !! (l, i) = Some j.
  Proof.
    unfold m_count. intros ne0.
    destruct (length_filter_ex _ _ _ ne0) as [[[l1 i1] x] [sat is_in]].
    rewrite elem_of_map_to_list in is_in.
    exists i1. exists x. simpl in sat. subst l. trivial.
  Qed.
  
  Local Lemma counts_agree_insert_writing {B: Type} σ (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(WSt, v)]> σ) m.
  Proof.
    unfold counts_agree_r. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_r. unfold heap_count_r in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
    
  Local Lemma counts_agree_insert_reading0 {B} σ (m : gmap (L * nat) B) l v v' :
    σ !! l = Some (WSt, v) →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(RSt 0, v')]> σ) m.
  Proof.
    unfold counts_agree_r. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_r. unfold heap_count_r in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_w_update_reading {B} σ (m : gmap (L * nat) B) l v v' n n' :
    σ !! l = Some (RSt n, v) →
    counts_agree_w σ m →
    counts_agree_w (<[l:=(RSt n', v')]> σ) m.
  Proof.
    unfold counts_agree_w. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count_w. unfold heap_count_w in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_get_fresh_index {B} (m : gmap (L * nat) B) (l: L) :
      ∃ i , m !! (l, i) = None.
  Proof.
    assert (exists x , x ∉ ((λ a , a.1.2) <$> map_to_list m)) as [x H].
    { exists (fresh ((λ a , a.1.2) <$> map_to_list m)). apply infinite_is_fresh. }
    exists x. destruct (m !! (l, x)) as [u|] eqn:mlx; trivial.
    exfalso. apply H. rewrite <- elem_of_map_to_list in mlx.
    rewrite elem_of_list_fmap. exists ((l, x), u). intuition.
  Qed.
       
  Local Lemma erase_count_map_same_update_read_count (σ: gmap L (ReadWriteState * V)) l v n m :
      σ !! l = Some (RSt n, v) →
      erase_count_map (<[l:=(RSt m, v)]> σ) = erase_count_map σ.
  Proof.
    intro is_in. unfold erase_count_map. rewrite fmap_insert. simpl.
    apply map_eq. intros l1. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite lookup_fmap. rewrite is_in. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_count_insert_plus1 {B} (m : gmap (L * nat) B) l i G
    (is_fresh : m !! (l, i) = None)
    : m_count m l + 1 = m_count (<[(l, i):=G]> m) l.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      unfold length. lia.
  Qed.
  
  Local Lemma m_count_insert_ne_helper {B} (m : gmap (L * nat) B) l l1 i G
    (ne : l ≠ l1)
    (mot_in: m !! (l, i) = None)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      destruct (decide (l = l1)); trivial; contradiction.
  Qed.
    
  Local Lemma m_count_insert_ne {B} (m : gmap (L * nat) B) l l1 i G
    (ne : l ≠ l1)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete.
    destruct (m !! (l, i)) as [G2|] eqn:m_in.
     - have t1 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G ne H.
       have t2 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G2 ne H.
       rewrite insert_delete in t2; trivial.
       rewrite insert_delete_insert in t1.
       rewrite t2 in t1. trivial.
     - apply m_count_insert_ne_helper; trivial.
  Qed.
    
  Local Lemma m_count_delete_minus1 {B} (m : gmap (L * nat) B) l i G
    (is_in : m !! (l, i) = Some G)
    : m_count m l - 1 = m_count (delete (l, i) m) l.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete.
    have j := m_count_insert_plus1 (delete (l, i) m) l i G H.
    rewrite insert_delete in j; trivial. lia.
  Qed.
    
  Local Lemma m_count_delete_ne {B} (m : gmap (L * nat) B) l l1 i
    (ne : l ≠ l1)
    : m_count m l1 = m_count (delete (l, i) m) l1.
  Proof.
    destruct (m !! (l, i)) as [G|] eqn:de.
     - have j := m_count_insert_ne (delete (l, i) m) l l1 i G ne.
       rewrite j. rewrite insert_delete; trivial.
     - rewrite delete_notin; trivial.
  Qed.
      
  Local Lemma counts_agree_insert_read {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v n i G
      (is_read : σ !! l = Some (RSt n, v))
      (is_fresh : m !! (l, i) = None)
      (ca: counts_agree_r σ m)
    : counts_agree_r (<[l:=(RSt (n + 1), v)]> σ) (<[(l, i):=G]> m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal. rewrite cal.
       apply m_count_insert_plus1; trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_insert_ne; trivial.
  Qed.

  Local Lemma counts_agree_delete_read {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v n i G
      (is_read : σ !! l = Some (RSt n, v))
      (is_in_m: m !! (l, i) = Some G)
      (n_ge_1: n ≥ 1)
      (ca: counts_agree_r σ m)
   : counts_agree_r (<[l:=(RSt (n - 1), v)]> σ) (delete (l, i) m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal. rewrite cal.
       apply m_count_delete_minus1 with (G := G); trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_delete_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_insert_write {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v i G
      (is_read : σ !! l = Some (RSt 0, v))
      (is_fresh : m !! (l, i) = None)
      (ca: counts_agree_w σ m)
    : counts_agree_w (<[l:=(WSt, v)]> σ) (<[(l, i):=G]> m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal. rewrite cal.
       rewrite <- m_count_insert_plus1; trivial. lia.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_delete_write {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l v v' i G
      (is_read : σ !! l = Some (WSt, v))
      (is_in_m: m !! (l, i) = Some G)
      (ca: counts_agree_w σ m)
   : counts_agree_w (<[l:=(RSt 0, v')]> σ) (delete (l, i) m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal.
       replace 0 with (m_count m l - 1) by lia.
       apply m_count_delete_minus1 with (G := G); trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_delete_ne; trivial.
  Qed.

  Local Lemma counts_agree_r_alloc {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = None →
    counts_agree_r σ m →
    counts_agree_r (<[l:=(RSt 0, v)]> σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_none in cal. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_w_alloc {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = None →
    counts_agree_w σ m →
    counts_agree_w (<[l:=(RSt 0, v)]> σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_none in cal. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_r_delete {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_r σ m →
    counts_agree_r (delete l σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_r in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_delete. rewrite is_none in cal. trivial.
    - rewrite lookup_delete_ne; trivial.
  Qed.
    
  Local Lemma counts_agree_w_delete {B}
    (σ: gmap L (ReadWriteState * V))
    (m : gmap (L * nat) B) l v :
    σ !! l = Some (RSt 0, v) →
    counts_agree_w σ m →
    counts_agree_w (delete l σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count_w in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_delete. rewrite is_none in cal. trivial.
    - rewrite lookup_delete_ne; trivial.
  Qed.
  
  Local Lemma m_count_ge_1_from {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      : m_count m l ≥ 1.
  Proof.
    enough (m_count m l ≠ 0) by lia.
    unfold m_count. 
    apply length_filter_ex_rev with (a := (l, i, G)); trivial.
    rewrite elem_of_map_to_list. trivial.
  Qed.
   
  Local Lemma counts_agree_ge1_is_reading {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      (ca: counts_agree_r σ m)
      : ∃ n v0 , σ !! l = Some (RSt n, v0) ∧ n ≥ 1.
  Proof.
    have cal := ca l.
    have j := m_count_ge_1_from σ m l i G m_has.
    have j2 := j.
    rewrite <- cal in j. unfold heap_count_r in j, cal.
    destruct (σ !! l) as [[r v]|]; last by lia.
    exists (m_count m l). exists v. intuition. f_equal. f_equal.
    destruct r as [|n]. { lia. } { subst n. trivial. }
  Qed.
  
  Local Lemma counts_agree_ge1_is_writing {B}
      (σ: gmap L (ReadWriteState * V))
      (m : gmap (L * nat) B) l i G
      (m_has : m !! (l, i) = Some G)
      (ca: counts_agree_w σ m)
      : ∃ v0 , σ !! l = Some (WSt, v0).
  Proof.
    have cal := ca l.
    have j := m_count_ge_1_from σ m l i G m_has.
    have j2 := j.
    rewrite <- cal in j. unfold heap_count_w in j, cal.
    destruct (σ !! l) as [[r v]|]; last by lia.
    exists v. intuition. f_equal. f_equal.
    destruct r as [|n]. { trivial. } { lia. }
  Qed.
End NonAtomicInternals.

(* end hide *)

Definition cell_id := positive.

Class na_logicG L V `{!EqDecision L, !Countable L, !Inhabited V} Σ := {
  #[local] na1_inG :: cmap_logicG L cell_id V Σ ;
  #[local] na2_inG :: inG Σ (gmap_viewR (L * nat) (agreeR (laterO (iPropO Σ)))) ;
  #[local] na3_inG :: inG Σ (gmap_viewR (L * nat) (agreeR
      (prodO (leibnizO (option (list cell_id * cell_id))) (laterO (iPropO Σ)))
     ))
}.

Definition na_logicΣ L V `{!EqDecision L, !Countable L, !Inhabited V} : gFunctors := #[
  cmap_logicΣ L cell_id V;
  GFunctor (gmap_viewRF (L * nat) (agreeRF (laterOF idOF)));
  GFunctor (gmap_viewRF (L * nat) (agreeRF (prodOF (leibnizO (option (list cell_id * cell_id))) (laterOF idOF))))
].

Global Instance subG_na_logicΣ L V `{!EqDecision L, !Countable L, !Inhabited V} Σ : subG (na_logicΣ L V) Σ → na_logicG L V Σ.
Proof.
  (* why is this not automatic? *)
  split. 
    - apply subG_cmap_logicΣ. unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      apply H3.
    - unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      solve_inG.
    - unfold na_logicΣ in H.
      have H2 := subG_inv _ _ _ H. destruct H2 as [H3 H4].
      solve_inG.
Qed.

Section NonAtomicMap.

  Context `{!EqDecision L, !Countable L}.
  Context `{!Inhabited V}.
  
  Context {Σ: gFunctors}.
  Context `{!na_logicG L V Σ}.
  Context `{!invGS Σ}. 
  
  (* begin hide *)
  
  Implicit Types (ι: gname) (l: L) (v: V).
  Implicit Types (lc: L + cell_id).
  Implicit Types (cv: cell_id + V).
  Implicit Types (cells: list cell_id).
  Implicit Types (G: iProp Σ).
  Implicit Types (σ: gmap L (ReadWriteState * V)).
  
  Local Definition ιf1 (ι: gname) : gname := match prod_decode_fst ι with Some x => x | _ => ι end.
  Local Definition ιf2 (ι: gname) : gname := match prod_decode_snd ι with Some x => x | _ => ι end.
  
  Local Definition ιh (ι: gname) : gname := ιf1 ι.
  Local Definition ιi (ι: gname) : gname := ιf1 (ιf2 ι).
  Local Definition ιj (ι: gname) : gname := ιf2 (ιf2 ι).
  
  Local Definition points_to_seq_def (ι: gname) (lc: L+cell_id) (cells: list cell_id) (cv: cell_id+V) : iProp Σ :=
      cellmap.pt_seq L cell_id V (ιh ι) lc cells cv.
  Local Definition points_to_seq_aux : seal (@points_to_seq_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to_seq ι lc cells cv : iProp Σ. exact (points_to_seq_aux.(unseal) ι lc cells cv). Defined.
  (* begin hide *)
  Local Definition points_to_seq_unseal :
      @points_to_seq = @points_to_seq_def := points_to_seq_aux.(seal_eq).
      
  (* end hide *)
  Notation "l @↦[ ι ][^ cells ] v" := (points_to_seq ι l cells v)
    (at level 20, format "l  @↦[ ι ][^ cells ]  v") : bi_scope.
  
  Notation "l @↦[ ι ] v" := (points_to_seq ι l [] v)
    (at level 20, format "l  @↦[ ι ]  v") : bi_scope.
    
  (* begin hide *)
  
  Local Definition wR := (agreeR (prodO (leibnizO (option (list cell_id * cell_id))) (laterO (iPropO Σ)))).
      
  Local Definition points_to_w_intermediate_def (ι: gname) (l: L)
      (o: option (list cell_id * cell_id)) (G: iProp Σ) : iProp Σ :=
    (∃ i, own (ιj ι) (gmap_view_frag (V:=wR) (l, i) (DfracOwn 1) (to_agree (o, Next G)))).
      
  Local Definition points_to_r_intermediate_def (ι: gname) (l: L) (cells: list cell_id) (v: V) (G: iProp Σ) : iProp Σ :=
    (∃ i, own (ιi ι) (gmap_view_frag (l, i) (DfracOwn 1) (to_agree (Next G)))) ∗ (∃d, £ d ∗ (G &&{↑naN;d}&&> (inl l @↦[ι][^ cells] inr v))).
    
  Local Definition points_to_w_intermediate_aux : seal (@points_to_w_intermediate_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to_w_intermediate ι l (o: option (list cell_id * cell_id)) (G: iProp Σ) : iProp Σ. exact (points_to_w_intermediate_aux.(unseal) ι l o G). Defined.
  (* begin hide *)
  Local Definition points_to_w_intermediate_unseal :
      @points_to_w_intermediate = @points_to_w_intermediate_def := points_to_w_intermediate_aux.(seal_eq).
      
  Local Definition points_to_r_intermediate_aux : seal (@points_to_r_intermediate_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to_r_intermediate ι l cells v G : iProp Σ. exact (points_to_r_intermediate_aux.(unseal) ι l cells v G). Defined.
  (* begin hide *)
  Local Definition points_to_r_intermediate_unseal :
      @points_to_r_intermediate = @points_to_r_intermediate_def := points_to_r_intermediate_aux.(seal_eq).
      
  Local Definition read_bank ι (σ: gmap L (ReadWriteState * V)) : iProp Σ :=
    ∃ (m : gmap (L * nat) (iProp Σ)),
      own (ιi ι) (gmap_view_auth (DfracOwn 1) (to_agree <$> (Next <$> m)))
      ∗ ⌜ counts_agree_r σ m ⌝
      ∗ [∗ map] k ↦ G ∈ m , G ∗ ∃ v cells d, £d ∗ (G &&{↑naN;d}&&> (inl (k.1)) @↦[ι][^ cells ] inr v).
      
  Definition sndNext (a: option (list cell_id * cell_id) * iProp Σ) :=
      match a with (b, c) => (b, Next c) end.
      
  Local Definition write_bank ι (σ: gmap L (ReadWriteState * V)) : iProp Σ :=
    ∃ (m : gmap (L * nat) (option (list cell_id * cell_id) * iProp Σ)),
      own (ιj ι) (gmap_view_auth (V:=wR) (DfracOwn 1) (to_agree <$> (sndNext <$> m)))
      ∗ ⌜ counts_agree_w σ m ⌝
      ∗ [∗ map] k ↦ '(o, G) ∈ m , G ∗ ∃ v , match o with
          | None => inl (k.1) @↦[ι] inr v
          | Some (cells, cell) =>
              (∃ d, £d ∗ (G &&{↑naN;d}&&> inl (k.1) @↦[ι][^cells] inl cell)) ∗
              inr cell @↦[ι] inr v
      end.
      
  Local Definition non_atomic_map_def (ι: gname) (σ: gmap L (ReadWriteState * V)) : iProp Σ
    := 
      cellmap.heap L cell_id V (ιh ι) (erase_count_map σ)
        ∗ read_bank ι σ ∗ write_bank ι σ.
          
  Local Definition non_atomic_map_aux : seal (@non_atomic_map_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition non_atomic_map ι σ : iProp Σ. exact (non_atomic_map_aux.(unseal) ι σ). Defined.
  (* begin hide *)
  Local Definition non_atomic_map_unseal :
      @non_atomic_map = @non_atomic_map_def := non_atomic_map_aux.(seal_eq).
  
  Local Ltac unseal := rewrite
    ?non_atomic_map_unseal /non_atomic_map_def
    ?points_to_seq_unseal /points_to_seq_def
    ?points_to_r_intermediate_unseal /points_to_r_intermediate_def
    ?points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    
  (* read bank *)
  
  Lemma read_bank_contradiction ι σ l n v1 cells v E :
      ↑naN ⊆ E →
      n ≠ 0 →
      σ !! l = Some (RSt n, v1) →
      read_bank ι σ -∗ (inl l @↦[ι][^ cells] inr v) ={E}=∗ False.
  Proof.
    intros Hmask h Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "pt". unseal.
    have ca_l := ca l. unfold heap_count_r in ca_l. rewrite Hσl in ca_l.
    rewrite ca_l in h.
    have ij := m_count_get1 m l h.
    destruct ij as [i [G mli]].
    iDestruct (big_sepM_delete with "big") as "[[g gu] _]". { apply mli. }
    iDestruct "gu" as (v0 cells0 d) "[£ gu]".
    leaf_open_laters "gu" with "g" as "A". { trivial. }
    iMod (lc_fupd_elim_laterN with "£ A") as "A".
    iMod "A" as "[pt2 back]".
    iDestruct (cmap_locs_ne with "pt pt2") as "%Hl". done.
  Qed.
  
  Lemma read_bank_contradiction_guarded_cells ι σ l n v1 cells c v E G d :
      ↑naN ⊆ E →
      n ≠ 0 →
      σ !! l = Some (RSt n, v1) →
      read_bank ι σ -∗
      £ d -∗
      (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗
      G -∗
      (inr c @↦[ι] inr v) ={E}=∗ False.
  Proof.
    intros Hmask h Hσl. iDestruct 1 as (m) "[oh [%ca big]]".
    iIntros "£ #guard G pt". unseal.
    have ca_l := ca l. unfold heap_count_r in ca_l. rewrite Hσl in ca_l.
    rewrite ca_l in h.
    have ij := m_count_get1 m l h.
    destruct ij as [i [G0 mli]].
    iDestruct (big_sepM_delete with "big") as "[[G0 gu] _]". { apply mli. }
    iDestruct "gu" as (v0 cells0 d0) "[£0 #guard0]".
    leaf_hyp "guard" lhs to (G ∗ G0)%I as "guard'". { iApply guards_weaken_sep_l. }
    leaf_hyp "guard0" lhs to (G ∗ G0)%I as "guard0'". { iApply guards_weaken_sep_r. }
    leaf_hyp "guard'" laters to (d + d0) as "guard''". { lia. }
    leaf_hyp "guard0'" laters to (d + d0) as "guard0''". { lia. }
    iMod (guards_and_pers_with_excl _ _ _ False%I with "[] guard'' guard0'' [G G0] pt") as "J"; first by trivial.
     - iModIntro. iIntros "[And pt]".
       iDestruct (cmap_pt_and_gives_prefix with "And") as "%IsPrefix".
       destruct IsPrefix as [cells2 IsPrefix]. rewrite IsPrefix.
       iDestruct "And" as "[_ prefix]".
       iDestruct (cmap_pt_seq_cons_app with "prefix") as "[a b]".
       iDestruct (cmap_cells_ne with "pt b") as "%A". contradiction.
     - iFrame.
     - iCombine "£ £0" as "£".
       iMod (lc_fupd_elim_laterN with "£ J") as "J".
       iMod "J" as "(? & ? & false)". iExFalso. done.
  Qed.
  
  Lemma read_bank_begin ι σ l n v0 cells v E G d :
      ↑naN ⊆ E →
      σ !! l = Some (RSt n, v0) →
      read_bank ι σ -∗
      £(2*d) -∗
      (G &&{↑naN;d}&&> (inl l @↦[ι][^ cells] inr v)) -∗
      G ={E}=∗
      points_to_r_intermediate ι l cells v G ∗ read_bank ι (<[ l := (RSt (n+1), v0) ]> σ).
  Proof.
      intros Hmask is_read.
      iIntros "na [£ £'] #guard g". replace (d + 0) with d by lia.
      iDestruct "na" as (m) "[oi [%ca big]]".
      destruct (m_get_fresh_index m l) as [i is_fresh].
      iMod (@own_update Σ _ na2_inG (ιi ι) _ ((
        gmap_view_auth (V := (agreeR (laterO (iPropO Σ))))
          (DfracOwn 1) (to_agree <$> (Next <$> (<[ (l,i) := G ]> m)))
      ⋅ gmap_view_frag (V := (agreeR (laterO (iPropO Σ))))
          (l, i) (DfracOwn 1) (to_agree (Next G))
      )) with "oi") as "[oi ptr]".
      {
        rewrite fmap_insert. rewrite fmap_insert. apply gmap_view_alloc.
        { rewrite lookup_fmap. rewrite lookup_fmap. rewrite is_fresh. trivial. }
        { done. } { done. }
      }
      iModIntro. iFrame "oi". unseal. iFrame "ptr". iFrame "£". unseal. iFrame "guard".
      iSplitR. { iPureIntro. apply counts_agree_insert_read; trivial. }
      rewrite big_sepM_insert; trivial. iFrame. iFrame "guard".
  Qed.
  
  Local Lemma points_to_heap_agree' ι l cells v σ :
    (inl l @↦[ι][^ cells ] inr v) ∗ cellmap.heap L cell_id V (ιh ι) (erase_count_map σ) ⊢ ⌜ ∃ st, σ !! l = Some (st, v) ⌝.
  Proof.
    unseal. iIntros "[pt heap]". iDestruct (cmap_read with "heap pt") as "%Hv".
    iPureIntro. unfold erase_count_map in Hv. rewrite lookup_fmap in Hv.
    destruct (σ !! l) as [p|].
    - unfold "<$>", option_fmap, option_map in Hv.
      exists (p.1). destruct p; f_equal. f_equal. inversion Hv. trivial.
    - inversion Hv.
  Qed.
  
  Lemma read_bank_end ι σ l cells v E G :
      ↑naN ⊆ E →
      read_bank ι σ -∗
      points_to_r_intermediate ι l cells v G -∗
      cellmap.heap L cell_id V (ιh ι) (erase_count_map σ) -∗
      ▷ |={E}=> ∃ n, G
        ∗ ⌜n ≥ 1 ∧ σ !! l = Some (RSt n, v)⌝
        ∗ read_bank ι (<[ l := (RSt (n-1), v) ]> σ)
        ∗ cellmap.heap L cell_id V (ιh ι) (erase_count_map σ).
  Proof.
      unseal. iIntros (Hmask) "na [ptr guard] oh".
      iDestruct "guard" as (d) "[£ guard]".
      iDestruct "na" as (m) "[oi [%ca big]]".
      iDestruct "ptr" as (i) "ptr".
      iAssert (∃ n G' v0, ⌜ σ !! l = Some (RSt n, v0) ∧ n ≥ 1 ∧ m !! (l, i) = Some G'⌝
        ∗ Next G ≡ Next G')%I as (n G' v0) "[%p #equ]".
      {
        iCombine "oi ptr" as "oi".
        iDestruct (own_valid with "oi") as "oi_val".
        rewrite gmap_view_both_validI_total.
        iDestruct "oi_val" as (v') "[%_valfrac1 [%_valfrac2 [%sm [val1 val2]]]]".
        rewrite lookup_fmap in sm. rewrite lookup_fmap in sm.
        destruct ((@lookup (prod L nat) (uPred (iResUR Σ))
                    (@gmap (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      (uPred (iResUR Σ)))
                    (@gmap_lookup (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      (uPred (iResUR Σ))) (@pair L nat l i) m))
          as [G'|] eqn:dest_eqn.
          2: { inversion sm. }
          simpl in sm. inversion sm. subst v'. 
          rewrite to_agree_includedI.
          destruct (counts_agree_ge1_is_reading σ m l i G' dest_eqn) as [n [v0 is_read]]; trivial.
          iExists n. iExists G'. iExists v0.
          iFrame "val2". { iPureIntro. intuition. }
       }
    
    iExists n.
    destruct p as [in_sig [n_ge1 in_m]].
    iDestruct (big_sepM_delete with "big") as "[[g gu] big]". { apply in_m. }
    iDestruct "gu" as (v1) "gu".
    rewrite later_equivI. iNext. iRewrite -"equ" in "g".
   
    leaf_open_laters "guard" with "g" as "A". { trivial. }
    iMod (lc_fupd_elim_laterN with "£ A") as "A".
    iMod "A" as "[pt back]".
   
    iDestruct (points_to_heap_agree' ι l cells v σ with "[pt oh]") as "%in_sig2". { iFrame. }
    iMod ("back" with "pt") as "G".
   
    iCombine "oi ptr" as "oi".
    iMod (@own_update Σ _ na2_inG (ιi ι) _ ((
      gmap_view_auth (V := (agreeR (laterO (iPropO Σ))))
        (DfracOwn 1) (to_agree <$> (Next <$> (delete (l, i) m)))
    )) with "oi") as "oi".
    {
      rewrite fmap_delete. rewrite fmap_delete.
      apply gmap_view_delete.
    }
    
    assert (v = v0) as veq. {
      destruct in_sig2 as [n0 in_sig2]. rewrite in_sig in in_sig2.
        inversion in_sig2. trivial.
    }
    subst v0.
    
    iModIntro. iFrame "G". iSplitR. { iPureIntro. intuition. }
    
    unfold non_atomic_map. iFrame "oi".
    
    iFrame "big oh".
    iPureIntro. apply (counts_agree_delete_read _ _ _ _ _ _ G'); trivial.
  Qed.
  
  Lemma read_bank_no_op_to_wst ι σ l v :
      σ !! l = Some (RSt 0, v) →
      read_bank ι σ ⊢
      read_bank ι (<[l:=(WSt, v)]> σ).
  Proof.
    iIntros (Hin) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iFrame. iPureIntro. apply counts_agree_insert_writing; trivial.
  Qed.
  
  Lemma read_bank_no_op_to_rst0 ι σ l v v' :
      σ !! l = Some (WSt, v) →
      read_bank ι σ ⊢
      read_bank ι (<[l:=(RSt 0, v')]> σ).
  Proof.
    iIntros (Hin) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iFrame. iPureIntro. eapply counts_agree_insert_reading0; done.
  Qed.
  
  Lemma read_bank_insert ι l v σ :
    (σ !! l = None) →
    read_bank ι σ ⊢ read_bank ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    iIntros (not_in) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. apply (counts_agree_r_alloc σ m l v not_in ca).
  Qed.
  
  Lemma read_bank_delete ι l v σ :
    (σ !! l = Some (RSt 0, v)) →
    read_bank ι σ ⊢ read_bank ι (delete l σ).
  Proof.
    iIntros (not_in) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. apply (counts_agree_r_delete σ m l v not_in ca).
  Qed.
  
  (* write bank *)
  
  Lemma write_bank_contradiction ι σ l v1 v E :
      ↑naN ⊆ E →
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗ (inl l @↦[ι] inr v) ={E}=∗ False%I.
  Proof.
    intros Hmask Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "pt". unseal.
    have ca_l := ca l. unfold heap_count_w in ca_l. rewrite Hσl in ca_l.
    assert (m_count m l ≠ 0) as ca_l' by lia.
    have ij := m_count_get1 m l ca_l'.
    destruct ij as [i [[o G] mli]].
    iDestruct (big_sepM_delete with "big") as "[a _]". { apply mli. }
    simpl. iDestruct "a" as "[G a]".
    destruct o as [[cells cell]|].
       - iDestruct "a" as (v0) "[a pt2]". iDestruct "a" as (d) "[£ guard]".
         leaf_open_laters "guard" with "G" as "A". { trivial. }
         iMod (lc_fupd_elim_laterN with "£ A") as "A".
         iMod "A" as "[pt3 back]".
         repeat rewrite <- pt_seq_singleton.
         iDestruct (cmap_locs_ne with "pt pt3") as "%Hl". done.
       - iDestruct "a" as (v0) "pt2".
         repeat rewrite <- pt_seq_singleton.
         iDestruct (cmap_locs_ne with "pt pt2") as "%Hl". done.
  Qed.
  
  Lemma write_bank_contradiction_guarded_all ι σ l v1 cells v E G d :
      ↑naN ⊆ E →
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗
      £ d -∗
      (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inr v) -∗
      G ={E}=∗ False.
  Proof.
    intros Hmask Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "£ #guard G". unseal.
    have ca_l := ca l. unfold heap_count_w in ca_l. rewrite Hσl in ca_l.
    assert (m_count m l ≠ 0) as ca_l' by lia.
    have ij := m_count_get1 m l ca_l'.
    destruct ij as [i [[o G0] mli]].
    iDestruct (big_sepM_delete with "big") as "[a _]". { apply mli. }
    simpl. iDestruct "a" as "[G0 a]".
    destruct o as [[cells0 cell0]|].
       - iDestruct "a" as (v0) "[a pt0]". iDestruct "a" as (d0) "[£0 #guard0]".
       
         leaf_hyp "guard" lhs to (G ∗ G0)%I as "guard'". { iApply guards_weaken_sep_l. }
         leaf_hyp "guard0" lhs to (G ∗ G0)%I as "guard0'". { iApply guards_weaken_sep_r. }
         leaf_hyp "guard'" laters to (d + d0) as "guard''". { lia. }
         leaf_hyp "guard0'" laters to (d + d0) as "guard0''". { lia. }
         iMod (guards_and_pers_with_excl _ _ _ False%I with "[] guard'' guard0'' [G G0] pt0") as "J"; first by trivial.
           + iModIntro. iIntros "[And pt]". repeat rewrite <- pt_seq_singleton.
             iApply (cmap_pt_and_gives_contra _ _ _ (ιh ι) (inl l) cells cells0 cell0 v v0 with "And [pt]"). { rewrite <- pt_seq_singleton. iFrame. }
           + iFrame.
           + iCombine "£ £0" as "£".
             iMod (lc_fupd_elim_laterN with "£ J") as "J".
             iMod "J" as "(? & ? & false)". iExFalso. done.
      - leaf_open_laters "guard" with "G" as "A". { trivial. }
        iMod (lc_fupd_elim_laterN with "£ A") as "A".
        iMod "A" as "[pt0 back]".
        iDestruct "a" as (v0) "pt1".
        repeat rewrite <- pt_seq_singleton.
        iDestruct (cmap_locs_ne with "pt0 pt1") as "%Hl". done.
  Qed.
    
  Lemma write_bank_contradiction_guarded_cells ι σ l v1 cells c v E G d :
      ↑naN ⊆ E →
      σ !! l = Some (WSt, v1) →
      write_bank ι σ -∗
      £ d -∗
      (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗
      G -∗
      (inr c @↦[ι] inr v) ={E}=∗ False.
  Proof.
    iIntros (Hmask IsSome) "wb £ #guard G pt".
    iApply (write_bank_contradiction_guarded_all ι σ l v1 (cells ++ [c]) v E (G ∗ inr c @↦[ι] inr v)%I d Hmask IsSome with "wb £ [] [G pt]").
      - iApply guards_and_point.
        + unseal. apply cmap_pt_seq_point_prop.
        + unseal. apply cmap_pt_and_cons_back.
        + unseal. iApply (guards_weaken_lhs_sep_l with "guard").
        + unseal. iApply guards_weaken_sep_r.
      - iFrame.
  Qed.
  (*
    intros Hmask Hσl. iDestruct 1 as (m) "[oh [%ca big]]". iIntros "£ #guard G pt". unseal.
    have ca_l := ca l. unfold heap_count_w in ca_l. rewrite Hσl in ca_l.
    assert (m_count m l ≠ 0) as ca_l' by lia.
    have ij := m_count_get1 m l ca_l'.
    destruct ij as [i [[o G0] mli]].
    iDestruct (big_sepM_delete with "big") as "[a _]". { apply mli. }
    simpl. iDestruct "a" as "[G0 a]".
    destruct o as [[cells0 cell0]|].
       - iDestruct "a" as (v0) "[a pt0]". iDestruct "a" as (d0) "[£0 #guard0]".
       
         leaf_hyp "guard" lhs to (G ∗ G0)%I as "guard'". { iApply guards_weaken_sep_l. }
         leaf_hyp "guard0" lhs to (G ∗ G0)%I as "guard0'". { iApply guards_weaken_sep_r. }
         leaf_hyp "guard'" laters to (d + d0) as "guard''". { lia. }
         leaf_hyp "guard0'" laters to (d + d0) as "guard0''". { lia. }
         iCombine "pt pt0" as "pt".
         iMod (guards_and_pers_with_excl _ _ _ False%I with "[] guard'' guard0'' [G G0] pt") as "J"; first by trivial.
           + iModIntro. iIntros "[And [pt pt0]]". rewrite <- pt_seq_singleton.
             iApply (cmap_pt_and_gives_contra with "And pt pt0").
           + iFrame.
           + iCombine "£ £0" as "£".
             iMod (lc_fupd_elim_laterN with "£ J") as "J".
             iMod "J" as "(? & ? & false)". iExFalso. done.
      - leaf_open_laters "guard" with "G" as "A". { trivial. }
        iMod (lc_fupd_elim_laterN with "£ A") as "A".
        iMod "A" as "[pt0 back]".
        iDestruct "a" as (v0) "pt1".
        repeat rewrite <- pt_seq_singleton.
        iDestruct (cmap_locs_ne with "pt0 pt1") as "%Hl". done.
        *)
  
  Lemma write_bank_begin ι σ l v0 v E :
      ↑naN ⊆ E →
      σ !! l = Some (RSt 0, v0) →
      write_bank ι σ -∗
      inl l @↦[ι] inr v
      ={E}=∗
      points_to_w_intermediate ι l None True%I ∗ write_bank ι (<[ l := (WSt, v0) ]> σ).
  Proof.
      intros Hmask is_read.
      iIntros "na pt".
      iDestruct "na" as (m) "[oi [%ca big]]".
      destruct (m_get_fresh_index m l) as [i is_fresh].
      iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
        gmap_view_auth (V := wR)
          (DfracOwn 1) (to_agree <$> (sndNext <$> (<[ (l,i) := (None, True%I) ]> m)))
      ⋅ gmap_view_frag (V := wR)
          (l, i) (DfracOwn 1) (to_agree (sndNext (None, True%I)))
      )) with "oi") as "[oi ptr]".
      {
        rewrite fmap_insert. rewrite fmap_insert. apply (gmap_view_alloc (V:=wR)).
        { rewrite lookup_fmap. rewrite lookup_fmap. rewrite is_fresh. trivial. }
        { done. } { done. }
      }
      iModIntro. iFrame "oi". unseal. iFrame "ptr". unseal.
      iSplitR. { iPureIntro. apply counts_agree_insert_write; trivial. }
      rewrite big_sepM_insert; trivial. iFrame.
  Qed.
    
  Lemma write_bank_begin_guarded_cells ι σ l cells c v0 v E G d :
      ↑naN ⊆ E →
      σ !! l = Some (RSt 0, v0) →
      write_bank ι σ -∗
      £ d -∗
      (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗
      G -∗
      (inr c @↦[ι] inr v)
      ={E}=∗
      points_to_w_intermediate ι l (Some (cells, c)) G ∗ write_bank ι (<[ l := (WSt, v0) ]> σ).
  Proof.
      intros Hmask is_read.
      iIntros "na £ #guard G pt".
      iDestruct "na" as (m) "[oi [%ca big]]".
      destruct (m_get_fresh_index m l) as [i is_fresh].
      iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
        gmap_view_auth (V := wR)
          (DfracOwn 1) (to_agree <$> (sndNext <$> (<[ (l,i) := (Some (cells, c), G) ]> m)))
      ⋅ gmap_view_frag (V := wR)
          (l, i) (DfracOwn 1) (to_agree (sndNext (Some (cells, c), G)))
      )) with "oi") as "[oi ptr]".
      {
        rewrite fmap_insert. rewrite fmap_insert. apply (gmap_view_alloc (V:=wR)).
        { rewrite lookup_fmap. rewrite lookup_fmap. rewrite is_fresh. trivial. }
        { done. } { done. }
      }
      iModIntro. iFrame "oi". unseal. iFrame "ptr".
      iSplitR. { iPureIntro. apply counts_agree_insert_write; trivial. }
      rewrite big_sepM_insert; trivial. iFrame. iFrame "guard".
  Qed.
  
  Lemma write_bank_end ι σ l v' E G :
      ↑naN ⊆ E →
      write_bank ι σ -∗
      points_to_w_intermediate ι l None G
      ={E}=∗ ∃ v1 v2,
      ⌜σ !! l = Some (WSt, v1)⌝ ∗
      inl l @↦[ι] inr v2 ∗
      write_bank ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
      unseal. iIntros (Hmask) "wb wim".
      iDestruct "wb" as (m) "[oi [%ca big]]".
      iDestruct "wim" as (i) "wim".
      iAssert (∃ (G': iProp Σ) v1, ⌜σ !! l = Some (WSt, v1) ∧ m !! (l, i) = Some (None, G') ⌝ ∗ Next G ≡ Next G' )%I as (G' v1) "[%p #equ]". {
        iCombine "oi wim" as "oi".
        iDestruct (own_valid with "oi") as "oi_val".
        rewrite gmap_view_both_validI_total.
        iDestruct "oi_val" as (v1) "[%_valfrac1 [%_valfrac2 [%sm [val1 val2]]]]".
        rewrite lookup_fmap in sm. rewrite lookup_fmap in sm.
        destruct ((@lookup (prod L nat) _ 
                    (@gmap (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      _)
                    (@gmap_lookup (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      (_)) (@pair L nat l i) m))
          as [oG'|] eqn:dest_eqn.
          2: { inversion sm. }
          simpl in sm. inversion sm. subst v1. 
          rewrite to_agree_includedI.
          destruct (counts_agree_ge1_is_writing σ m l i oG' dest_eqn) as [v0 is_read]; trivial.
          destruct oG' as [o' G']. iExists G'. iExists v0. unfold sndNext.
          rewrite prod_equivI. iDestruct "val2" as "[%val3 #val4]". simpl in val3. subst o'.
          iSplit. { iPureIntro. split; trivial. }
          iFrame "val4".
     }
     
    destruct p as [in_sig in_m].
    iDestruct (big_sepM_delete with "big") as "[g big]". { apply in_m. }
     
    iCombine "oi wim" as "oi".
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR) (DfracOwn 1) (to_agree <$> (sndNext <$> (delete (l, i) m)))
    )) with "oi") as "oi".
    { rewrite fmap_delete. rewrite fmap_delete. apply (gmap_view_delete (V := wR)). }
    
    iDestruct "g" as "[G' pt]". iDestruct "pt" as (v2) "pt".
    iModIntro. iExists v1, v2. iSplit. { done. }
    iFrame. unseal. iFrame.
    iPureIntro. eapply (counts_agree_delete_write _ _ _ _ _ _); trivial.
    { apply in_sig. } apply in_m.
  Qed.
  
  Lemma write_bank_end_guarded_cells ι σ l cells c v' E G :
      ↑naN ⊆ E →
      write_bank ι σ -∗
      points_to_w_intermediate ι l (Some (cells, c)) G -∗
      ▷ |={E}=> ∃ v1 v2,
      G ∗
      (∃d', £d' ∗ (G &&{↑naN;d'}&&> inl l @↦[ι][^ cells] inl c)) ∗
      ⌜σ !! l = Some (WSt, v1)⌝ ∗
      inr c @↦[ι] inr v2 ∗
      write_bank ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
      unseal. iIntros (Hmask) "wb wim".
      iDestruct "wb" as (m) "[oi [%ca big]]".
      iDestruct "wim" as (i) "wim".
      iAssert (∃ (G': iProp Σ) v1, ⌜σ !! l = Some (WSt, v1) ∧ m !! (l, i) = Some (Some (cells, c), G') ⌝ ∗ Next G ≡ Next G' )%I as (G' v1) "[%p #equ]". {
        iCombine "oi wim" as "oi".
        iDestruct (own_valid with "oi") as "oi_val".
        rewrite gmap_view_both_validI_total.
        iDestruct "oi_val" as (v1) "[%_valfrac1 [%_valfrac2 [%sm [val1 val2]]]]".
        rewrite lookup_fmap in sm. rewrite lookup_fmap in sm.
        destruct ((@lookup (prod L nat) _ 
                    (@gmap (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      _)
                    (@gmap_lookup (prod L nat) (@prod_eq_dec L _ nat Nat.eq_dec)
                      (@prod_countable L _ _ nat Nat.eq_dec nat_countable)
                      (_)) (@pair L nat l i) m))
          as [oG'|] eqn:dest_eqn.
          2: { inversion sm. }
          simpl in sm. inversion sm. subst v1. 
          rewrite to_agree_includedI.
          destruct (counts_agree_ge1_is_writing σ m l i oG' dest_eqn) as [v0 is_read]; trivial.
          destruct oG' as [o' G']. iExists G'. iExists v0. unfold sndNext.
          rewrite prod_equivI. iDestruct "val2" as "[%val3 #val4]". simpl in val3. subst o'.
          iSplit. { iPureIntro. split; trivial. }
          iFrame "val4".
     }
     
    destruct p as [in_sig in_m].
    iDestruct (big_sepM_delete with "big") as "[g big]". { apply in_m. }
    iDestruct "g" as "[g gu]".
    rewrite later_equivI. iNext. iRewrite -"equ" in "g".
     
    iCombine "oi wim" as "oi".
    iMod (@own_update Σ _ na3_inG (ιj ι) _ ((
      gmap_view_auth (V := wR) (DfracOwn 1) (to_agree <$> (sndNext <$> (delete (l, i) m)))
    )) with "oi") as "oi".
    { rewrite fmap_delete. rewrite fmap_delete. apply (gmap_view_delete (V := wR)). }
    
    iDestruct "gu" as (v2) "[gu pt]".
    iModIntro. iExists v1, v2. iFrame. iDestruct "gu" as (d') "[£ #guard']".
    leaf_hyp "guard'" lhs to G%I as "guard".
       { leaf_by_sep. iIntros "G". iRewrite "equ" in "G". iFrame. iIntros "G'".
        iRewrite -"equ" in "G'". iFrame. }
    iSplitL "£". { iExists d'. iFrame. unseal. iFrame "guard". }
    unseal. iFrame. iSplit; first by done.
    iPureIntro. eapply (counts_agree_delete_write _ _ _ _ _ _); trivial.
    { apply in_sig. } apply in_m.
  Qed.
  
  Lemma write_bank_no_op ι σ l n v n' v' :
      σ !! l = Some (RSt n, v) →
      write_bank ι σ
      ⊢ write_bank ι (<[l := (RSt n', v')]> σ).
  Proof.
    iIntros (Hin) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iFrame. iPureIntro. eapply counts_agree_w_update_reading. - apply Hin. - apply ca.
  Qed.
  
  Lemma write_bank_insert ι l v σ :
    (σ !! l = None) →
    write_bank ι σ ⊢ write_bank ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    iIntros (not_in) "wb". iDestruct "wb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. apply (counts_agree_w_alloc σ m l v not_in ca).
  Qed.
  
  Lemma write_bank_delete ι l v σ :
    (σ !! l = Some (RSt 0, v)) →
    write_bank ι σ ⊢ write_bank ι (delete l σ).
  Proof.
    iIntros (not_in) "rb". iDestruct "rb" as (m) "[oi [%ca big]]".
    iExists m. iFrame. iPureIntro. apply (counts_agree_w_delete σ m l v not_in ca).
  Qed.
  
  (* end hide *)
    
  Global Instance points_to_timeless ι lc cells cv : Timeless (lc @↦[ι][^ cells] cv).
  Proof. unseal. destruct cv; apply _. Qed.
        
  Lemma non_atomic_map_alloc_empty
    : ⊢ |==> ∃ ι, non_atomic_map ι ∅.
  Proof.
    unseal. iIntros.
    iMod (cmap_init) as (ιh0) "H".
    iMod (@own_alloc Σ _ na2_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιi0) "H2". { apply gmap_view_auth_valid. }
    iMod (@own_alloc Σ _ na3_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (ιj0) "H3". { apply gmap_view_auth_valid. }
    iModIntro. iExists (prod_encode ιh0 (prod_encode ιi0 ιj0)).
      unfold non_atomic_map. unfold read_bank, write_bank.
      unfold ιh. unfold ιi. unfold ιj. unfold ιf1. unfold ιf2.
      repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    replace (erase_count_map ∅) with (∅: gmap L V) by done. iFrame "H".
    iSplitL "H2".
      { iExists ∅. iFrame. iSplit.
        { iPureIntro. unfold counts_agree_r, heap_count_r, m_count. intros l.
          rewrite lookup_empty. trivial. }
        done.
      }
      { iExists ∅. iFrame. iSplit.
        { iPureIntro. unfold counts_agree_w, heap_count_w, m_count. intros l.
          rewrite lookup_empty. trivial. }
        done.
      }
  Qed.
        
  Lemma points_to_heap_agree ι l cells v σ :
    (inl l @↦[ι][^ cells] inr v) -∗ non_atomic_map ι σ -∗ ⌜ ∃ st, σ !! l = Some (st, v) ⌝.
  Proof.
    unseal. iIntros "pt na". iDestruct "na" as "[oh _]".
    iApply points_to_heap_agree'. unseal. iFrame.
  Qed.
  
  Lemma points_to_heap_reading0 ι l v σ E :
    ↑naN ⊆ E →
    ⊢ (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ ={E}=∗
      (inl l @↦[ι] inr v) ∗ non_atomic_map ι σ ∗ ⌜ σ !! l = Some (RSt 0, v) ⌝.
  Proof.
    unseal. intros Hask. iIntros "pt [h [rb wb]]".
    iDestruct (points_to_heap_agree' with "[pt h]") as (st) "%Hσl". { iFrame. unseal. iFrame "pt". }
    destruct st.
     - iMod (write_bank_contradiction with "wb [pt]"). { trivial. } { apply Hσl. } { unseal. iFrame "pt". } iExFalso. iFrame.
     - destruct n.
      + iModIntro. iFrame. done.
      + iMod (read_bank_contradiction _ _ _ (S n) with "rb [pt]").  { trivial. } { lia. } { apply Hσl. } { unseal. iFrame. } iExFalso. iFrame.
  Qed.
  
  Lemma points_to_heap_reading0_guarded_cells `{!EqDecision V} ι l cells c v σ E G d :
    ↑naN ⊆ E →
    ⊢ £ d -∗ (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗ G -∗ (inr c @↦[ι] inr v)
          -∗ non_atomic_map ι σ ={E}=∗
      G ∗ (inr c @↦[ι] inr v) ∗ non_atomic_map ι σ ∗ ⌜ σ !! l = Some (RSt 0, v) ⌝.
  Proof.
    unseal. intros Hmask. iIntros "£ #guard G pt na".
    destruct (σ !! l) as [p|] eqn:Hσl; last first.
    {
      leaf_open_laters "guard" with "G" as "A". { trivial. }
      iMod (lc_fupd_elim_laterN with "£ A") as "A".
      iMod "A" as "[prefix back]".
      iCombine "prefix pt" as "pt". rewrite <- cmap_pt_seq_cons_back.
      iDestruct (points_to_heap_agree with "[pt] [na]") as "%is_read". { unseal. iFrame. } { unseal. iFrame. } destruct is_read as [n is_read]. rewrite Hσl in is_read. discriminate.
    }
    destruct p as [st v0].
    destruct (decide (v0 = v)) as [Eq|Ne]; last first.
      {
        leaf_open_laters "guard" with "G" as "A". { trivial. }
        iMod (lc_fupd_elim_laterN with "£ A") as "A".
        iMod "A" as "[prefix back]".
        iCombine "prefix pt" as "pt". rewrite <- cmap_pt_seq_cons_back.
        iDestruct (points_to_heap_agree with "[pt] [na]") as "%is_read". { unseal. iFrame. } { unseal. iFrame. } destruct is_read as [n0 is_read]. rewrite Hσl in is_read. inversion is_read.
        subst v0. contradiction.
      }
    subst v0.
    
    iDestruct "na" as "[h [rb wb]]".
    destruct st.
      + iMod (write_bank_contradiction_guarded_cells with "wb £ [guard] G [pt]").  { trivial. }  { apply Hσl. } { unseal. iFrame "guard". } { unseal. iFrame. } iExFalso. iFrame.
      + destruct n.
        * iModIntro. iFrame. done.
        * iMod (read_bank_contradiction_guarded_cells _ _ _ (S n) with "rb £ [guard] G [pt]").  { trivial. }  { lia. } { apply Hσl. } { unseal. iFrame "guard". } { unseal. iFrame. } iExFalso. iFrame.
  Qed.
  
  Lemma points_to_heap_readingN_guarded_all `{!EqDecision V} ι l cells v σ E G d :
    ↑naN ⊆ E →
    ⊢ £ d -∗ (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inr v) -∗ G
          -∗ non_atomic_map ι σ ={E}=∗
      G ∗ non_atomic_map ι σ ∗ ⌜ ∃ n, σ !! l = Some (RSt n, v) ⌝.
  Proof.
    unseal. intros Hmask. iIntros "£ #guard G na".
    destruct (σ !! l) as [p|] eqn:Hσl; last first.
    {
      leaf_open_laters "guard" with "G" as "A". { trivial. }
      iMod (lc_fupd_elim_laterN with "£ A") as "A".
      iMod "A" as "[pt back]".
      iDestruct (points_to_heap_agree with "[pt] [na]") as "%is_read". { unseal. iFrame. } { unseal. iFrame. } destruct is_read as [n is_read]. rewrite Hσl in is_read. discriminate.
    }
    destruct p as [st v0].
    destruct (decide (v0 = v)) as [Eq|Ne]; last first.
      {
        leaf_open_laters "guard" with "G" as "A". { trivial. }
        iMod (lc_fupd_elim_laterN with "£ A") as "A".
        iMod "A" as "[pt back]".
        iDestruct (points_to_heap_agree with "[pt] [na]") as "%is_read". { unseal. iFrame. } { unseal. iFrame. } destruct is_read as [n0 is_read]. rewrite Hσl in is_read. inversion is_read.
        subst v0. contradiction.
      }
    subst v0.
    
    iDestruct "na" as "[h [rb wb]]".
    destruct st.
      + iMod (write_bank_contradiction_guarded_all with "wb £ [guard] G").  { trivial. }  { apply Hσl. } { unseal. iFrame "guard". } iExFalso. iFrame.
      + iModIntro. iFrame. iPureIntro. exists n. trivial.
  Qed.
  
  (* main stuff here *)

  Lemma na_write_begin ι l v σ E :
    ↑naN ⊆ E →
    ⊢ (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ ={E}=∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ points_to_w_intermediate ι l None True%I
        ∗ non_atomic_map ι (<[ l := (WSt, v) ]> σ).
  Proof.
    unseal. intros Hmask. iIntros "pt na".
    iMod (points_to_heap_reading0 with "[pt] [na]") as "[pt [na %is_read]]".
      { trivial. } { unseal. iFrame "pt". } { unseal. iFrame "na". }
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iMod (cmap_write _ _ _ _ _ _ _ _ v with "oh pt") as "[oh pt]".
    replace (<[l:=v]> (erase_count_map σ))
      with  (erase_count_map (<[ l := (WSt, v) ]> σ)). 2: {
      unfold erase_count_map. rewrite fmap_insert. done.
    }
    iMod (write_bank_begin with "wb [pt]") as "[wim wb]"; trivial. { apply is_read. }
        { unseal. iFrame. }
    iModIntro. unseal. iFrame. iSplit; first by done.
    iApply read_bank_no_op_to_wst; trivial.
  Qed.
  
  Lemma na_write_begin_guarded_cells `{!EqDecision V} ι l cells c v σ E G d :
    ↑naN ⊆ E →
    ⊢ £(3*d) -∗ (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗ G -∗ (inr c @↦[ι] inr v) -∗
        non_atomic_map ι σ ={E}=∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ points_to_w_intermediate ι l (Some (cells, c)) G
        ∗ non_atomic_map ι (<[ l := (WSt, v) ]> σ).
  Proof.
    unseal. intros Hmask. iIntros "[£1 [£2 £3]] #guard G pt na". replace (d + 0) with d by lia.
    iMod (points_to_heap_reading0_guarded_cells with "£1 [guard] G [pt] [na]") as "[G [pt [na %is_read]]]".
      { trivial. } { unseal. iFrame "guard". } { unseal. iFrame "pt". } { unseal. iFrame "na". }
    unseal. iDestruct "na" as "[oh [rb wb]]".
    leaf_open_laters "guard" with "G" as "A". { trivial. }
    iMod (lc_fupd_elim_laterN with "£2 A") as "A".
    iMod "A" as "[prefix back]".
    iCombine "prefix pt" as "pt". rewrite <- cmap_pt_seq_cons_back.
    iMod (cmap_write _ _ _ _ _ _ _ _ (v) with "oh pt") as "[oh pt]".
    rewrite cmap_pt_seq_cons_back. iDestruct "pt" as "[prefix pt]".
    iMod ("back" with "prefix") as "G".
    replace (<[l:=v]> (erase_count_map σ))
      with  (erase_count_map (<[ l := (WSt, v) ]> σ)). 2: {
      unfold erase_count_map. rewrite fmap_insert. done.
    }
    iMod (write_bank_begin_guarded_cells with "wb £3 [guard] G [pt]") as "[wim wb]"; trivial. { apply is_read. } { unseal. iApply "guard". } { unseal. iApply "pt". }
    iModIntro. unseal. iFrame. iSplit; first by done.
    iApply read_bank_no_op_to_wst; trivial.
  Qed.
    
  Lemma na_write_finish ι l v' σ G E :
    ↑naN ⊆ E →
    ⊢ points_to_w_intermediate ι l None G -∗ non_atomic_map ι σ ={E}=∗
        ⌜ ∃ v, σ !! l = Some (WSt, v) ⌝
        ∗ inl l @↦[ι] inr v'
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    iIntros (Hmask) "pt na".
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iMod (write_bank_end _ _ l v' with "wb [pt]") as (v1 v2) "[%Hst [pt wb]]". { trivial. } { unseal. iFrame. }
    unseal. iMod (cmap_write _ _ _ _ _ _ _ _ (v') with "oh pt") as "[oh pt]".
    replace (<[l:=(v')]> (erase_count_map σ))
      with  (erase_count_map (<[ l := (RSt 0, v') ]> σ)). 2: {
      unfold erase_count_map. rewrite fmap_insert.  done.
    }
    iModIntro. iFrame. iSplit. { iExists v1. done. }
    iApply read_bank_no_op_to_rst0; trivial. apply Hst.
  Qed.
   
  Lemma na_write_finish_guarded_cells ι l cells c v' σ E G :
    ↑naN ⊆ E →
    ⊢ points_to_w_intermediate ι l (Some (cells, c)) G -∗
        non_atomic_map ι σ -∗ ▷ |={E}=>
        ⌜ ∃ v, σ !! l = Some (WSt, v) ⌝
        ∗ G
        ∗ inr c @↦[ι] inr v'
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    iIntros (Hmask) "wim na".
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iDestruct (write_bank_end_guarded_cells _ _ l _ _ v' with "wb [wim]") as "A". { apply Hmask. } { unseal. iFrame "wim". }
    iNext.
    iMod "A" as (v1 v2) "[G [guard [%Hst [pt wb]]]]".
    iDestruct "guard" as (d') "[£' #guard]".
    leaf_open_laters "guard" with "G" as "A". { trivial. }
    iMod (lc_fupd_elim_laterN with "£' A") as "A".
    iMod "A" as "[prefix back]".
    
    unseal. iCombine "prefix pt" as "pt". rewrite <- cmap_pt_seq_cons_back.
    iMod (cmap_write _ _ _ _ _ _ _ _ (v') with "oh pt") as "[oh pt]".
    replace (<[l:=(v')]> (erase_count_map σ))
      with  (erase_count_map (<[ l := (RSt 0, v') ]> σ)). 2: {
      unfold erase_count_map. rewrite fmap_insert.  done.
    }
    rewrite cmap_pt_seq_cons_back. iDestruct "pt" as "[prefix pt]".
    iMod ("back" with "prefix").
    
    iModIntro. iFrame. iSplit. { iExists v1. done. }
    iApply read_bank_no_op_to_rst0; trivial. apply Hst.
  Qed.
   
  Lemma na_read_begin `{!EqDecision V} ι l cells v σ G d E :
    ↑naN ⊆ E →
    ⊢ £(3*d) -∗ (G &&{↑naN;d}&&> (inl l @↦[ι][^ cells] inr v)) -∗ G -∗ non_atomic_map ι σ ={E}=∗
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ⌝
        ∗ points_to_r_intermediate ι l cells v G
        ∗ non_atomic_map ι (<[ l := (RSt (n + 1), v) ]> σ).
  Proof.
    iIntros (Hmask) "[£ £2] #guard G na". replace (d + (d + 0)) with (2*d) by trivial. unseal.
    iMod (points_to_heap_readingN_guarded_all with "£ [guard] G [na]") as "[G [na %is_read]]".
      { trivial. } { unseal. iFrame "guard". } { unseal. iFrame "na". }
    unseal. iDestruct "na" as "[oh [rb wb]]". destruct is_read as [n is_read].
    iMod (read_bank_begin with "rb £2 [guard] G") as "[rim rb]". { trivial. } { apply is_read. } { unseal. iFrame "guard". }
    iModIntro. iFrame. iSplit; first by done. unseal. unseal. iFrame "rim".
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ is_read). iFrame "oh".
    iApply (write_bank_no_op with "wb"). apply is_read.
  Qed.
  
  Lemma na_read_end ι l cells v σ G E :
    ↑naN ⊆ E →
    points_to_r_intermediate ι l cells v G -∗ non_atomic_map ι σ -∗ ▷ |={E}=>
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ∧ n ≥ 1 ⌝
        ∗ G
        ∗ non_atomic_map ι (<[ l := (RSt (n - 1), v) ]> σ).
  Proof.
    unseal. intros Hmask. iIntros "ptr [oh [rb wb]]".
    iDestruct (read_bank_end ι σ l cells v E G Hmask with "rb [ptr] oh") as "J".
        { unseal. unseal. iFrame "ptr". }
    iNext. iMod "J" as (n) "[G [%Hσ [rb oh]]]". destruct Hσ as [Hn is_read].
    iModIntro. iExists n. iSplit. { iPureIntro; split; trivial. }
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ is_read). iFrame.
    iApply (write_bank_no_op with "wb"). apply is_read.
  Qed.

  Lemma atomic_write ι l v v' σ E :
    ↑naN ⊆ E →
    ⊢ (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ ={E}=∗
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ (inl l @↦[ι] inr v')
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    iIntros (Hmask) "pt h".
    iMod (na_write_begin with "pt h") as "[%sig [pt heap]]"; first by trivial.
    iMod (na_write_finish with "pt heap") as "[%sig2 [pt heap]]"; first by trivial.
    iModIntro. iFrame "pt". rewrite insert_insert. iFrame "heap".
    iPureIntro. apply sig.
  Qed.
  
  Lemma atomic_write_guarded_cells `{!EqDecision V} ι l v cells c v' σ E G d :
    ↑naN ⊆ E →
    ⊢ £(3*d) -∗ (G &&{↑naN;d}&&> inl l @↦[ι][^ cells] inl c) -∗ G -∗ (inr c @↦[ι] inr v) -∗
        non_atomic_map ι σ -∗ |={E}=> ▷ |={E}=>
        ⌜ σ !! l = Some (RSt 0, v) ⌝
        ∗ G
        ∗ (inr c @↦[ι] inr v')
        ∗ non_atomic_map ι (<[ l := (RSt 0, v') ]> σ).
  Proof.
    iIntros (Hmask) "£ #guard G pt h".
    iMod (na_write_begin_guarded_cells with "£ guard G pt h") as "[%sig [pt heap]]"; first by trivial.
    iDestruct (na_write_finish_guarded_cells with "pt heap") as "A"; first by apply Hmask.
    iModIntro. iNext.
    iMod "A" as "[%sig2 [G [pt heap]]]".
    iModIntro. iFrame "pt". rewrite insert_insert. iFrame "heap G".
    iPureIntro. apply sig.
  Qed.

  Lemma atomic_read `{!EqDecision V} ι l cells v σ G E d :
    ↑naN ⊆ E →
    £(d) -∗
    (G &&{↑naN;d}&&> (inl l @↦[ι][^ cells] inr v)) -∗ G -∗ non_atomic_map ι σ ={E}=∗
        ∃ n , ⌜ σ !! l = Some (RSt n, v) ⌝
        ∗ G ∗ non_atomic_map ι σ.
  Proof.
    iIntros (Hmask) "£ #guard G na".
    iMod (points_to_heap_readingN_guarded_all with "£ [guard] G [na]") as "[G [na %is_read]]".
      { trivial. } { unseal. iFrame "guard". } { unseal. iFrame "na". }
    destruct is_read as [n is_read].
    iModIntro. iExists n. iFrame. unseal. iFrame. done.
  Qed.
  
  Lemma non_atomic_map_insert ι l v σ :
    (σ !! l = None) →
    non_atomic_map ι σ ==∗ (inl l @↦[ι] inr v) ∗ non_atomic_map ι (<[ l := (RSt 0, v) ]> σ).
  Proof.
    unseal. intros not_in. iIntros "[oh [rb wb]]".
    iDestruct (read_bank_insert ι l v σ with "rb") as "rb"; first by trivial.
    iDestruct (write_bank_insert ι l v σ with "wb") as "wb"; first by trivial.
    iMod (cmap_alloc _ _ _ _ _ l (v) with "oh") as "[oh pt]".
      { unfold erase_count_map. rewrite lookup_fmap. rewrite not_in. done. }
    replace ((<[l:=v]> (erase_count_map σ)) : gmap L V)
        with (erase_count_map (<[ l := (RSt 0, v) ]> σ)). 2: {
      unfold erase_count_map. rewrite fmap_insert. done.
    }
    iModIntro. iFrame.
  Qed.
  
  Lemma non_atomic_map_delete ι l v σ E :
    ↑naN ⊆ E →
    (inl l @↦[ι] inr v) -∗ non_atomic_map ι σ ={E}=∗
      ⌜ σ !! l = Some (RSt 0, v) ⌝ ∗ non_atomic_map ι (delete l σ).
  Proof.
    iIntros (Hmask) "pt na".
    iMod (points_to_heap_reading0 with "pt na") as "[pt [na %is_in]]"; first by trivial.
    unseal. iDestruct "na" as "[oh [rb wb]]".
    iDestruct (read_bank_delete ι l v σ with "rb") as "rb"; first by trivial.
    iDestruct (write_bank_delete ι l v σ with "wb") as "wb"; first by trivial.
    iMod (cmap_delete with "oh pt") as "oh".
    replace ((delete l (erase_count_map σ)))
        with (erase_count_map (delete l σ)). 2: {
          unfold erase_count_map. rewrite fmap_delete. done.
        }
    iModIntro. iFrame. done.
  Qed.
  
(*
  Lemma non_atomic_map_alloc_heap σ
    : ⊢ |==> ∃ ι, non_atomic_map ι σ.
  Proof.
    induction σ using map_ind; first by apply non_atomic_map_alloc_empty.
    iIntros. iMod IHσ as (ι) "σ".
    iMod (non_atomic_map_insert with "σ") as "[pt σ]"; first by apply H.
    iModIntro.
*)
  
  (** cell stuff *)
  
  Lemma pt_seq_cons ι lc cell cells cv :
      lc @↦[ι][^ cell :: cells] cv ⊣⊢ lc @↦[ι] (inl cell) ∗ (inr cell) @↦[ι][^ cells] cv.
  Proof.
      unseal. done.
  Qed.
  
  Lemma pt_seq_cons_and ι lc cell cells cv :
      lc @↦[ι] (inl cell) ∧ (inr cell) @↦[ι][^cells] cv ⊢ lc @↦[ι][^ cell :: cells] cv.
  Proof.
      unseal. apply cmap_pt_and_cons.
  Qed.
  
  Lemma pt_seq_cons_back_and ι lc cell cells cv :
      lc @↦[ι][^cells] (inl cell) ∧ (inr cell) @↦[ι] cv ⊢ lc @↦[ι][^ cells ++ [cell]] cv.
  Proof.
      generalize lc. clear lc. induction cells; intro lc.
        - simpl. apply pt_seq_cons_and.
        - simpl. iIntros "And". iApply (pt_seq_cons_and). iSplit.
          + rewrite pt_seq_cons. iDestruct "And" as "[[$ _] _]".
          + iApply IHcells. iSplit.
            * rewrite pt_seq_cons. iDestruct "And" as "[[_ $] _]".
            * iDestruct "And" as "[_ $]".
  Qed.

  Lemma pt_seq_snoc ι lc cell cells cv :
    lc @↦[ι][^ cells ++ [cell]] cv ⊣⊢ lc @↦[ι][^cells] inl cell ∗ inr cell @↦[ι] cv.
  Proof.
    rewrite points_to_seq_unseal.
    rewrite /points_to_seq_def.
    rewrite cellmap.cmap_pt_seq_cons_back.
    done.
  Qed.
      
  (* Cell-And *)
  Lemma pt_seq_app_and ι lc cells1 cell cells2 cv :
      lc @↦[ι][^cells1] (inl cell) ∧ (inr cell) @↦[ι][^cells2] cv
          ⊣⊢ lc @↦[ι][^ cells1 ++ cell :: cells2] cv.
  Proof.
      iSplit.
        - iStopProof. generalize lc. clear lc. induction cells1.
          + iIntros (lc) "_ A". iApply (pt_seq_cons_and with "A").
          + iIntros (lc) "_ A". simpl. iApply pt_seq_cons_and. iSplit.
            * iDestruct "A" as "[A _]". rewrite pt_seq_cons. iDestruct "A" as "[$ _]".
            * iApply IHcells1; first done. iSplit.
              -- iDestruct "A" as "[A _]". rewrite pt_seq_cons. iDestruct "A" as "[_ $]".
              -- iDestruct "A" as "[_ $]".
        - iIntros "A". iSplit.
          + iStopProof. generalize lc. clear lc. induction cells1.
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[$ _]".
            * iIntros (lc). simpl. do 2 rewrite pt_seq_cons. iIntros "[A B]". iFrame "A".
              iApply IHcells1. iFrame "B".
          + iStopProof. generalize lc. clear lc. induction cells1.
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[_ $]".
            * iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "[_ B]".
              iApply IHcells1. iFrame "B".
  Qed.
        
  (* Cell-Sep *)
  Lemma pt_seq_app_sep ι lc cells1 cell cells2 cv :
      lc @↦[ι][^cells1] (inl cell) ∗ (inr cell) @↦[ι][^cells2] cv
          ⊣⊢ lc @↦[ι][^ cells1 ++ cell :: cells2] cv.
  Proof.
      iSplit.
        - iIntros "[A B]". iApply pt_seq_app_and. iSplit; iFrame.
        - iIntros "A".
          iStopProof. generalize lc. clear lc. induction cells1.
          + iIntros (lc). simpl. rewrite pt_seq_cons. iIntros "$".
          + iIntros (lc). simpl. do 2 rewrite pt_seq_cons. iIntros "[$ B]".
            iApply IHcells1. iFrame "B".
  Qed.
  
  Lemma pt_seq_andM_sepM ι (rows: gmap L ((list cell_id) * (cell_id + V))) :
      ([∧ map] l ↦ '(cells, cv) ∈ rows, (inl l) @↦[ι][^cells] cv)%I ⊢
      [∗ map] l ↦ '(cells, cv) ∈ rows, (inl l) @↦[ι][^cells] cv.
  Proof.
      unseal. apply cmap_andM_sepM.
  Qed.
  
  Local Lemma pt_untether' ι lc cell :
      lc @↦[ι] (inl cell) ==∗
        ∃ (v: V), lc @↦[ι] (inr v)
          ∗ (∀ l cells, inl l @↦[ι][^ cells] inr v ==∗ inl l @↦[ι][^ cells] inl cell).
  Proof. 
    unseal. iIntros "pts". iMod (cmap_untether with "pts") as (v) "[pts back]".
    iModIntro. iExists v. rewrite pt_seq_singleton. iFrame "pts". iIntros (l cells) "pt".
    iMod (cmap_retether with "pt back"). done.
  Qed.
  
  Lemma pt_untether ι lc cells cell :
      lc @↦[ι][^cells] (inl cell) ==∗
        ∃ (v: V), lc @↦[ι][^cells] (inr v)
          ∗ (∀ l cells, inl l @↦[ι][^ cells] inr v ==∗ inl l @↦[ι][^ cells] inl cell).
  Proof.
      destruct (cellmap.case_last_c cell_id cells) as [[_ Hcells]|[prefix [last [_ Hcells]]]].
       - subst cells. apply pt_untether'.
       - subst cells. rewrite pt_seq_snoc. iIntros "[A B]".
         iMod (pt_untether' with "B") as (v) "[B back]".
         iModIntro. iExists v. rewrite pt_seq_snoc. iFrame.
  Qed.
  
  Lemma pt_seq_point_prop ι lc cells cv :
      factoring_props.point_prop (lc @↦[ι][^ cells] cv).
  Proof.
      unseal. apply cmap_pt_seq_point_prop.
  Qed.
  
  (* Cell-Fresh *)
  Lemma pt_alloc_cell' ι lc cv :
      lc @↦[ι] cv ==∗ ∃ c, lc @↦[ι][^ [c]] cv.
  Proof.
    destruct lc as [l|c].
    - destruct cv as [c'|v].
      + (* untether the existing cell; insert the new cell; retether *)
        iIntros "pt". iMod (pt_untether with "pt") as (v) "[pt retether]".
        iMod (cmap_alloc_unt _ _ _ (ιh ι) v) as (c) "[pt2 unt]".
        iMod (cmap_retether with "[pt] unt") as "pt". { unseal. iFrame. }
        iDestruct ("retether" $! l [c] with "[pt pt2]") as "J".
          { unseal. rewrite cmap_pt_seq_cons. rewrite pt_seq_singleton. iFrame. }
        iExists c. done.
      + (* insert new cell immediately *)
        iIntros "pt".
        iMod (cmap_alloc_unt _ _ _ (ιh ι) v) as (c) "[pt2 unt]".
        iMod (cmap_retether with "[pt] unt") as "pt". { unseal. iFrame. }
        iModIntro. iExists c. unseal. rewrite pt_seq_singleton. iFrame.
    - iIntros "pt". unseal. iMod (cmap_alloc_cell_after_cell with "pt") as (new_c) "[pt1 pt2]".
      iModIntro. iExists new_c. iFrame.
  Qed.
  
  Lemma pt_alloc_cell ι lc cells cv :
      lc @↦[ι][^ cells] cv ==∗ ∃ c, lc @↦[ι][^ c :: cells] cv.
  Proof.
      destruct cells as [|cell cells].
      - apply pt_alloc_cell'.
      - iIntros "a". rewrite pt_seq_cons. iDestruct "a" as "[pt rest]".
        iMod (pt_alloc_cell' with "pt") as (c) "pt".
        iModIntro. iExists c.
        do 3 rewrite pt_seq_cons. iDestruct "pt" as "[$ $]". iFrame.
  Qed.
  
  Lemma pt_delete_cell ι l c cells cv :
      inl l @↦[ι][^ c :: cells] cv ==∗ inl l @↦[ι][^ cells] cv.
  Proof.
      destruct cells as [|cell cells].
      - iIntros "pt".
        unseal. rewrite !cmap_pt_seq_cons. rewrite !pt_seq_singleton. 
        iDestruct "pt" as "[pt1 pt2]".
        by iMod (cmap_delete_cell  with "pt1 pt2") as "pt".
      - iIntros "pt".
        unseal. rewrite !cmap_pt_seq_cons. rewrite !pt_seq_singleton. 
        iDestruct "pt" as "[pt1 [pt2 pt3]]".
        iMod (cmap_delete_cell  with "pt1 pt2") as "pt".
        by iFrame.
  Qed.

End NonAtomicMap.

Global Notation "l @↦[ ι ][^ cells ] v" := (points_to_seq ι l cells v)
    (at level 20, format "l  @↦[ ι ][^ cells ]  v") : bi_scope.
  
Global Notation "l @↦[ ι ] v" := (points_to_seq ι l [] v)
    (at level 20, format "l  @↦[ ι ]  v") : bi_scope.
