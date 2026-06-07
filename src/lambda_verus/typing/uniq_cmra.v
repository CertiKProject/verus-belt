From iris.algebra Require Import auth cmra functions gmap dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun update cancellable.
From lrust.prophecy Require Import prophecy.
From guarding Require Import guard own_and tactics.

From lrust.lifetime Require Import lifetime_full.

Implicit Type (𝔄i: syn_typei) (𝔄: syn_type).

(** * Camera for Unique Borrowing *)

Local Definition uniq_itemR 𝔄i := dfrac_agreeR (leibnizO (bool * ((~~ (`𝔄i)) * (nat * nat)))).
Local Definition uniq_gmapUR 𝔄i := gmapUR positive (uniq_itemR 𝔄i).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR: ucmra := authUR uniq_smryUR.

Local Definition item {𝔄i} q b x d : uniq_itemR 𝔄i :=
  @to_frac_agree (leibnizO _) q (b, (x, d)).
Local Definition line ξ q b x d : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_id) := item q b x d]}]}.
Local Definition add_line ξ q b x d (S: uniq_smryUR) : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := item q b x d]> (S ξ.(pv_ty))]> S.

Definition uniqΣ: gFunctors := #[GFunctor uniqUR; cnaInv_logicΣ].
Class uniqPreG Σ := UniqPreG {
  #[global] uniq_preG_inG :: inG Σ uniqUR ;
  #[global] type_cnaInv_logicΣ :: cnaInv_logicG Σ
}.
Class uniqG Σ := UniqG { #[global] uniq_inG :: uniqPreG Σ; uniq_name: gname; atomic_pool_name: gname }.
Global Instance subG_uniqPreG Σ : subG uniqΣ Σ → uniqPreG Σ.
Proof. solve_inG. Qed.

Definition uniqN: namespace := NllftUsr .@ "uniq".

(** * Iris Propositions *)

Section defs.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

Definition SendN : namespace := nroot .@ "send_guard".

(** Unique Reference Context *)
Definition uniq_inv: iProp Σ := ∃S, own uniq_name (● S).
Definition uniq_ctx: iProp Σ := inv uniqN uniq_inv
    (* the atomic pool actually has nothing to do with uniq borrows, but I didn't want
       to go through the effort of making a new ctx proposition for this, so I reused
       this one *)
    ∗ (True &&{↑SendN}&&> (cna_lifetimes atomic_pool_name ∅)).

Lemma uniq_ctx_get_cna_lifetimes_inv :
    uniq_ctx -∗ (True &&{↑SendN}&&> (cna_lifetimes atomic_pool_name ∅)).
Proof. iIntros "[_ $]". Qed.

Local Definition own_line ξ q b x d := own uniq_name (◯ line ξ q b x d).

(** Value Observer *)
Definition val_obs (ξ: proph_var) x (d: nat * nat) : iProp Σ :=
  own_line ξ (1/2) false x d.
  
(** Prophecy Controller *)  (* TODO vπ arg is superfluous, it's always `vπ x` *)
Local Definition val_obs2 ξ x d : iProp Σ := own_line ξ 1 false x d.

(** Prophecy Controller *)  (* TODO vπ arg is superfluous, it's always `vπ x` *)
Local Definition val_obs2_done ξ x d : iProp Σ := own_line ξ 1 true x d.

Definition proph_ctrl (ξ: proph_var) x (vπ: proph ξ.(pv_ty)) (d: nat * nat) : iProp Σ :=
  (val_obs ξ x d ∗ 1:[ξ]) ∨ ((∃x' d', val_obs2_done ξ x' d') ∗ (.$ ξ) :== vπ).
End defs.

Notation ".VO[ ξ ]" := (val_obs ξ) (at level 5, format ".VO[ ξ ]") : bi_scope.
Local Notation ".VO2[ ξ ]" := (val_obs2 ξ)
  (at level 5, format ".VO2[ ξ ]") : bi_scope.
Notation ".PC[ ξ ]" := (proph_ctrl ξ)
  (at level 5, format ".PC[ ξ ]") : bi_scope.

(** * Lemmas *)

Definition prval_to_inh {𝔄} (vπ: proph 𝔄) : inh_syn_type 𝔄 :=
  to_inh_syn_type (vπ inhabitant).

Section lemmas.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.
Global Instance val_obs_timeless ξ x d : Timeless (.VO[ξ] x d) := _.

Global Instance proph_ctrl_proper ξ :
  Proper ((=) ==> pointwise_relation _ (=) ==> (=) ==> (⊣⊢)) (proph_ctrl ξ).
Proof.
  move=> ?? E1 ?? E2 ?? E3. rewrite /proph_ctrl. do 2 f_equiv.
  - rewrite E1. rewrite E3. trivial.
  - setoid_rewrite E2. trivial.
Qed.

Local Lemma own_line_agree ξ q q' b x d b' x' d' :
  own_line ξ q b x d -∗ own_line ξ q' b' x' d' -∗ ⌜(q + q' ≤ 1)%Qp ∧ x = x' ∧ d = d' ∧ b = b'⌝.
Proof.
  iIntros "line line'". iDestruct (own_valid_2 with "line line'") as %Val.
  iPureIntro. move: Val.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  by move/frac_agree_op_valid=> [?[= ??]].
Qed.

Local Lemma auth_view_valid_frag au fr : ✓ (View au fr : uniqUR) → ✓ fr.
Proof.
  case: au; [|by apply auth_frag_valid]. move=> [dq ag] [_ valx].
  case: (valx 0)=>/= ?[_[/cmra_discrete_included_r + /cmra_discrete_valid ?]].
  exact: cmra_valid_included.
Qed.

Local Lemma auth_frag_view_included au fr fr' :
  ◯ fr' ≼ (View au fr : uniqUR) → fr' ≼ fr.
Proof. move=> [[??][/=??]]. by eexists _. Qed.

Local Lemma line_included fr ξ q b x d : 
  line ξ q b x d ≼ fr → Some (item q b x d) ≼ fr (pv_ty ξ) !! pv_id ξ.
Proof.
  move=> /(discrete_fun_included_spec_1 _ _ ξ.(pv_ty)).
  setoid_rewrite discrete_fun_lookup_singleton. rewrite lookup_included=> inc.
  move: {inc}(inc (pv_id ξ)). by rewrite lookup_singleton.
Qed.

Local Lemma and_line_agree ξ q q' b x d b' x' d' :
  own_line ξ q b x d ∧ own_line ξ q' b' x' d' ⊢ ⌜x = x' ∧ d = d' ∧ b = b'⌝.
Proof.
  rewrite and_own_discrete. iDestruct 1 as ([au fr]) "H". rewrite own_valid.
  iDestruct "H" as %[val incs]. iPureIntro. move: val=> /auth_view_valid_frag val.
  move: incs=> [/Some_included_total/auth_frag_view_included/line_included +
    /Some_included_total/auth_frag_view_included/line_included +].
  move: {val}(val (pv_ty ξ) (pv_id ξ)).
  case: (fr (pv_ty ξ) !! pv_id ξ); last by move=> _ /Some_included_is_Some[].
  move=> [? ag] [/=_ ?] /Some_pair_included_r/Some_included_total inc
    /Some_pair_included_r/Some_included_total inc'.
  apply agree_valid_included in inc=>//. apply agree_valid_included in inc'=>//.
  move: inc. by rewrite -inc'=> /to_agree_inj/leibniz_equiv_iff[=].
Qed.

Local Lemma vo_vo2 ξ x d : .VO[ξ] x d ∗ .VO[ξ] x d ⊣⊢ .VO2[ξ] x d.
Proof.
  by rewrite -own_op -auth_frag_op discrete_fun_singleton_op singleton_op /item
    -frac_agree_op Qp.half_half.
Qed.

Local Lemma vo_pc ξ x d x' vπ' d' :
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ ⌜x = x'⌝ ∗ ⌜d = d'⌝ ∗ .VO2[ξ] x d ∗ 1:[ξ].
Proof.
  iIntros "Vo [[Vo' ?]|[(%&%& Vo2) _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[A[B [C D]]].
  do 2 (iSplit; [done|]). rewrite -vo_vo2. iFrame. subst x. subst d. iFrame.
Qed.

Local Lemma vo2_vo2_done ξ x d E :
    ↑uniqN ⊆ E →
    uniq_ctx -∗ .VO2[ξ] x d ={E}=∗ val_obs2_done ξ x d.
Proof.
  iIntros (?) "[#? _] Vo2".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 true x d S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 true x d) with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2"; [by iExists S'|]. iModIntro.
  iFrame.
Qed.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃_: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  iMod (cna_pool_alloc) as (p) "[_ cna_lifetimes]".
  iMod (guards_alloc _ SendN with "cna_lifetimes") as "#G".
  iDestruct (guards_remove_later_rhs with "G") as "G'".
  set IUniqG := UniqG Σ _ γ p. iExists IUniqG. iFrame "G'".
  iMod (inv_alloc _ _ uniq_inv with "[●ε]") as "?"; by [iExists ε|].
Qed.

Lemma uniq_intro {𝔄} (x: ~~𝔄) (vπ: proph 𝔄) d E :
  ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗ ∃ξi,
    let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in .VO[ξ] x d ∗ .PC[ξ] x vπ d.
Proof.
  iIntros (?) "PROPH [? _]". iInv uniqN as (S) ">●S".
  set 𝔄i := 𝔄 ↾ prval_to_inh vπ. set I := dom (S 𝔄i).
  iMod (proph_intro 𝔄i I with "PROPH") as (ξi NIn) "ξ"; [by solve_ndisj|].
  set ξ := PrVar 𝔄i ξi. set S' := add_line ξ 1 false x d S.
  move: NIn=> /not_elem_of_dom ?.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 false x d) with "●S") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro. iExists ξi.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_strip_later ξ x d x' vπ' d' :
  ▷ .VO[ξ] x d -∗ ▷ .PC[ξ] x' vπ' d' -∗
    ◇ (⌜x = x'⌝ ∗ ⌜d = d'⌝ ∗ .VO[ξ] x d ∗ .PC[ξ] x' vπ' d').
Proof.
  iIntros ">Vo [>[Vo' ?]|[>(%&%& Vo2) _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_ [-> [-> _]]]. iModIntro.
  do 2 (iSplit; [done|]). iSplitL "Vo"; [done|]. iLeft. by iSplitL "Vo'".
Qed.

Lemma uniq_agree ξ x d x' vπ' d' :
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ ⌜x = x' ∧ d = d'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vo_pc with "Vo Pc") as (->->) "?".
Qed.

Lemma uniq_and_agree ξ x d x' vπ' d' :
  .VO[ξ] x d ∧ .PC[ξ] x' vπ' d' -∗ ⌜x = x' ∧ d = d'⌝.
Proof.
  iIntros "A". unfold proph_ctrl. rewrite bi.and_or_l. iDestruct "A" as "[A|A]".
  - iDestruct (and_line_agree with "[A]") as "[-> [-> _]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ [$ _]]". } } done.
  - iAssert (_ ∧ _)%I with "[A]" as "A". { iSplit. { iDestruct "A" as "[X _]". iApply "X". }
      { iDestruct "A" as "[_ [X _]]". iApply "X". } }
    rewrite bi.and_exist_l. iDestruct "A" as (x'') "A".
    rewrite bi.and_exist_l. iDestruct "A" as (d'') "A".
    iDestruct (and_line_agree with "[A]") as "[_ [_ %Heq]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ $]". } } discriminate.
Qed.

Lemma uniq_proph_tok ξ x d x' vπ' d' :
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ .VO[ξ] x d ∗ 1:[ξ] ∗ (1:[ξ] -∗ .PC[ξ] x' vπ' d').
Proof.
  iIntros "Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->->) "[Vo2 $]".
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iIntros "?". iLeft. iFrame.
Qed.

Lemma uniq_update ξ x'' vπ'' d'' x d x' vπ' d' E : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' ={E}=∗ .VO[ξ] x'' d'' ∗ .PC[ξ] x'' vπ'' d''.
Proof.
  iIntros (?) "[? _] Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->->) "[Vo2 ξ]".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 false x'' d'' S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 false x'' d'') with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_resolve ξ ζl q x d x' vπ' d' E : ↑uniqN ∪ ↑prophN ⊆ E → vπ' ./ ζl →
  uniq_ctx -∗ proph_ctx -∗ .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' d ∗ q:+[ζl].
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-<-) "[Vo2 ξ]".
  iMod (proph_resolve_toks with "PROPH ξ ζl") as "[#? $]"; [solve_ndisj|done|].
  iMod (vo2_vo2_done with "UNIQ Vo2") as "Vo2". { solve_ndisj. }
  iModIntro. iSplitR; [done|]. iRight. iSplitL; [by iExists x, d|].
  by iApply proph_eqz_obs.
Qed.

Lemma uniq_preresolve ξ ζl uπ q x d x'' vπ'' d'' E : ↑uniqN ∪ ↑prophN ⊆ E → uπ ./ ζl →
  uniq_ctx -∗ proph_ctx -∗ .VO[ξ] x d -∗ .PC[ξ] x'' vπ'' d'' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗ q:+[ζl] ∗ (∀x' vπ' d', uπ :== vπ' -∗ .PC[ξ] x' vπ' d').
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-<-) "[Vo2 ξ]".
  iMod (proph_resolve_toks with "PROPH ξ ζl") as "[#Obs $]"; [solve_ndisj|done|].
  iMod (vo2_vo2_done with "UNIQ Vo2") as "Vo2"; [solve_ndisj|].
  iModIntro. iSplitR; [done|]. iIntros (???) "Eqz". iRight.
  iSplitR "Eqz"; [by iExists x, d|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

Local Fixpoint remove_dupes (ζl: list proph_var) : list proph_var :=
  match ζl with
    | [] => []
    | ζ :: ζl' => if bool_decide (ζ ∈ ζl') then remove_dupes ζl' else ζ :: remove_dupes ζl'
  end.
  
Local Lemma elem_of_remove_dupes ζ (ζl: list proph_var) :
    ζ ∈ ζl ↔ ζ ∈ remove_dupes ζl.
Proof.
  induction ζl in ζ |- *; first done.
  simpl. case_bool_decide.
   - destruct (decide (ζ = a)) as [He|Hn].
    + subst a. split.
      * intros Ha. rewrite <- IHζl. trivial.
      * intros Ha. rewrite elem_of_cons. left; trivial.
    + rewrite elem_of_cons. have Ih := IHζl ζ. intuition.
   - destruct (decide (ζ = a)) as [He|Hn].
    + do 2 (rewrite elem_of_cons). intuition.
    + do 2 (rewrite elem_of_cons). have Ih := IHζl ζ. intuition.
Qed.

Local Lemma indep_remove_dupes {A} (vπ: proph A) ζl :
  vπ ./ ζl → vπ ./ remove_dupes ζl.
Proof.
  unfold proph_dep. intros Ha π π' Hc. apply (Ha π π').
  unfold prophecy.proph_asn_eqv. intros ξ Hin.
  rewrite elem_of_remove_dupes in Hin. apply Hc. apply Hin.
Qed.


Local Lemma combine_guard_proph_vars ζl n F G :
    (∀ ζ , ⌜ζ ∈ ζl⌝ -∗ (G &&{F; n}&&> 1:[ζ])) -∗
    (G &&{F; n}&&> 1:+[remove_dupes ζl]).
Proof.
    induction ζl.
     - iIntros. iApply guards_true.
     - iIntros "#G". simpl. case_bool_decide as Ha.
      + iApply IHζl. iIntros (ζ) "%Hin". iApply "G". iPureIntro. rewrite elem_of_cons.
        right; trivial.
      + simpl. iApply (guards_and_point _ (1:[a])%I (1:+[remove_dupes ζl])%I).
        * apply factoring_props.point_prop_sep.
          -- apply proph_tok_point_prop.
          -- apply proph_tokl_point_prop.
        * apply proph_tok_list_and. rewrite <- elem_of_remove_dupes. trivial.
        * iApply "G". iPureIntro. rewrite elem_of_cons. left. trivial.
        * iApply IHζl. iIntros (ζ) "%Hin". iApply "G". iPureIntro.
          rewrite elem_of_cons. right. trivial.
Qed.
  
Local Lemma proph_eqz_to_obs_with_guard {A} (uπ vπ: proph A) E n (ξl: list proph_var) G :
    ↑NllftG ∪ ↑prophN ⊆ E →
    vπ ./ ξl →
    £n -∗
    (∀ ζ : proph_var, ⌜ζ ∈ ξl⌝ -∗ (G &&{ ↑NllftG; n }&&> 1:[ζ])) -∗
    G -∗
    uπ :== vπ ={E}=∗ ⟨π, uπ π = vπ π⟩ ∗ G.
Proof.
    iIntros (Hmask Indep) "£ Guard' G eqz".
    iDestruct (combine_guard_proph_vars with "Guard'") as "#Guard".
    leaf_open_laters "Guard" with "G" as "Opened"; first by solve_ndisj.
    iMod (lc_fupd_elim_laterN with "£ Opened") as ">[tok back]".
    iMod ("eqz" with "[] tok") as "[Obs tok]".
      - iSplit; first solve_ndisj. iPureIntro. apply indep_remove_dupes. trivial.
      - iMod ("back" with "tok") as "G". iModIntro. iFrame.
Qed.

Lemma uniq_resolve_guarded ξ ζl x d x' vπ' d' E G n : ↑NllftG ∪ ↑prophN ∪ ↑uniqN ⊆ E → vπ' ./ ζl →
  (∀ ζ , ⌜ζ ∈ ζl⌝ -∗ (G &&{↑NllftG; n}&&> 1:[ζ])) -∗
  uniq_ctx -∗ proph_ctx -∗
  .VO[ξ] x d -∗ .PC[ξ] x' vπ' d' -∗ G ={E,E∖↑NllftG}=∗ ▷^n |={E∖↑NllftG,E}=>
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' d ∗ G.
Proof.
  iIntros (Hmask Indep) "Guard' UNIQ PROPH Vo Pc G".
  iDestruct (combine_guard_proph_vars with "Guard'") as "#Guard".
  leaf_open_laters "Guard" with "G" as "Opened"; first by solve_ndisj. iModIntro. iNext.
  iMod "Opened" as "[tok back]".
  iMod (uniq_resolve with "UNIQ PROPH Vo Pc tok") as "(Obs & Pc & Tok)"; first by solve_ndisj.
   { apply (indep_remove_dupes _ _ Indep). }
  iMod ("back" with "Tok") as "G".
  iModIntro. iFrame.
Qed.

Lemma proph_ctrl_eqz ξ x vπ d : proph_ctx -∗ .PC[ξ] x vπ d -∗ (.$ ξ) :== vπ.
Proof. iIntros "#? [[_ ?]|[_ ?]]"; by [iApply proph_eqz_token|]. Qed.

Lemma proph_ctrl_and_value_obs_entails_proph_tok ξ x vπ d :
  .PC[ξ] x vπ d ∧ .VO[ξ] x d ⊢ 1:[ξ].
Proof.
  iIntros "A". unfold proph_ctrl. rewrite bi.and_or_r. iDestruct "A" as "[A|A]".
   - iDestruct "A" as "[[_ $] _]".
   - iAssert (_ ∧ _)%I with "[A]" as "A". { iSplit. { iDestruct "A" as "[_ X]". iApply "X". }
      { iDestruct "A" as "[[X _] _]". iApply "X". } }
    rewrite bi.and_exist_l. iDestruct "A" as (x'') "A".
    rewrite bi.and_exist_l. iDestruct "A" as (d'') "A".
    iDestruct (and_line_agree with "[A]") as "[_ [_ %Heq]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ $]". } } discriminate.
Qed.

End lemmas.

Global Opaque uniq_ctx val_obs proph_ctrl.
