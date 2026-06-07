(**** from iris 4.3 codebase, slightly modified ****)

From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre adequacy.
From iris.prelude Require Import options.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxiliary results. *)

Section adequacy.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.

Local Lemma wp_step s e1 σ1 ns κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 ns (κ ++ κs) nt -∗
  £ (S (num_laters_per_step ns)) -∗
  WP e1 @ s; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
    state_interp σ2 (S ns) κs (nt + length efs) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗
    wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ Hcred H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 ns with "Hσ") as "(_ & H)". iModIntro.
  iApply (step_fupdN_wand with "(H [//] Hcred)"). iIntros ">H".
  by rewrite Nat.add_comm big_sepL2_replicate_r.
Qed.

Local Lemma wptp_step s es1 es2 κ κs σ1 ns σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  state_interp σ1 ns (κ ++ κs) nt -∗
  £ (S (num_laters_per_step ns)) -∗
  wptp s es1 Φs -∗
  ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step$ ns) |={∅,⊤}=>
         state_interp σ2 (S ns) κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hσ Hcred Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iExists _. iMod (wp_step with "Hσ Hcred Ht") as "H"; first done. iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros ">($ & He2 & Hefs) !>".
  rewrite -(assoc_L app) -app_comm_cons. iFrame.
Qed.

(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Local Lemma wptp_preservation s n es1 es2 κs κs' σ1 ns σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 ns σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 ns σ2 Φs /=.
  { inversion_clear 1; iIntros "? ? ?"; iExists 0=> /=.
    rewrite Nat.add_0_r right_id_L. iFrame. by iApply fupd_mask_subseteq. }
  iIntros (Hsteps) "Hσ Hcred He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)) Nat.iter_add -{1}plus_Sn_m plus_n_Sm.
  rewrite lc_split. iDestruct "Hcred" as "[Hc1 Hc2]".
  iDestruct (wptp_step with "Hσ Hc1 He") as (nt') ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "H").
  iIntros ">(Hσ & He)". iMod (IH with "Hσ Hc2 He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as (nt'') "[??]".
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_add. by eauto with iFrame.
Qed.

Local Lemma wp_not_stuck κs nt e σ ns Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤, ∅}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iMod (fupd_mask_subseteq ∅); first set_solver. iModIntro. eauto. }
  iSpecialize ("H" $! σ ns [] κs with "Hσ"). rewrite sep_elim_l.
  iMod "H" as "%". iModIntro. eauto.
Qed.

(** The adequacy statement of Iris consists of two parts:
      (1) the postcondition for all threads that have terminated in values
      and (2) progress (i.e., after n steps the program is not stuck).
    For an n-step execution of a thread pool, the two parts are given by
    [wptp_strong_adequacy] and [wptp_progress] below.

    For the final adequacy theorem of Iris, [wp_strong_adequacy_gen], we would
    like to instantiate the Iris proof (i.e., instantiate the
    [∀ {Hinv : !invGS_gen hlc Σ} κs, ...]) and then use both lemmas to get
    progress and the postconditions. Unfortunately, since the addition of later
    credits, this is no longer possible, because the original proof relied on an
    interaction of the update modality and plain propositions. So instead, we
    employ a trick: we duplicate the instantiation of the Iris proof, such
    that we can "run the WP proof twice". That is, we instantiate the
    [∀ {Hinv : !invGS_gen hlc Σ} κs, ...] both in [wp_progress_gen] and
    [wp_strong_adequacy_gen]. In doing  so, we can avoid the interactions with
    the plain modality. In [wp_strong_adequacy_gen], we can then make use of
    [wp_progress_gen] to prove the progress component of the main adequacy theorem.
*)

Local Lemma wptp_postconditions Φs κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ Hcred He". iMod (wptp_preservation with "Hσ Hcred He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iExists _. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Ht").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp_value_fupd'. done.
Qed.


Local Lemma wptp_progress Φs κs' n es1 es2 κs σ1 ns σ2 nt e2 :
  nsteps n (es1, σ1) κs (es2, σ2) →
  e2 ∈ es2 →
  state_interp σ1 ns (κs ++ κs') nt -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp NotStuck es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅}=> ⌜not_stuck e2 σ2⌝.
Proof.
  iIntros (Hstep Hel) "Hσ Hcred He". iMod (wptp_preservation with "Hσ Hcred He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  eapply elem_of_list_lookup in Hel as [i Hlook].
  destruct ((Φs ++ replicate nt' fork_post) !! i) as [Φ|] eqn: Hlook2; last first.
  { rewrite big_sepL2_alt. iDestruct "Ht" as "[%Hlen _]". exfalso.
    eapply lookup_lt_Some in Hlook. rewrite Hlen in Hlook.
    eapply lookup_lt_is_Some_2 in Hlook. rewrite Hlook2 in Hlook.
    destruct Hlook as [? ?]. naive_solver. }
  iDestruct (big_sepL2_lookup with "Ht") as "Ht"; [done..|].
  by iApply (wp_not_stuck with "Hσ").
Qed.
End adequacy.

Local Lemma wp_progress_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} es σ1 n κs t2 σ2 e2 k
        (num_laters_per_step : nat → nat)  :
    (∀ `{Hinv : !invGS_gen hlc Σ},
    ⊢ £k -∗ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         state_interp_mono,
       let _ : irisGS_gen hlc Λ Σ := IrisG Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 1 κs 0 ∗
       (([∗ list] e;Φ ∈ es;Φs, WP e @ ⊤ {{ Φ }}))) →
  nsteps n (es, σ1) κs (t2, σ2) →
  e2 ∈ t2 →
  not_stuck e2 σ2.
Proof.
  intros Hwp ??. 
  eapply pure_soundness.
  eapply (step_fupdN_soundness_gen _ hlc (steps_sum num_laters_per_step 1 n)
    (steps_sum num_laters_per_step 1 n + k)).
  iIntros (Hinv) "[Hcred Hk]".
  iDestruct (Hwp with "Hk") as "Hwp".
  iMod "Hwp" as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_progress _ _ _ 
       (IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hcred  Hwp") as "H"; [done| done |by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 1 n) |={∅}=> ⌜not_stuck e2 σ2⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H"). iIntros "$".
Qed.
  
(** Iris's generic adequacy result *)
(** The lemma is parameterized by [use_credits] over whether to make later credits available or not.
  Below, a concrete instances is provided with later credits (see [wp_strong_adequacy]). *)
Lemma wp_strong_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} s es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) k :
  (* WP *)
  (∀ `{Hinv : !invGS_gen hlc Σ},
      £k ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should
         usually work. *)
         state_interp_mono,
       let _ : irisGS_gen hlc Λ Σ := IrisG Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 1 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 (n+1) [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_gen _ hlc (steps_sum num_laters_per_step 1 n)
    (steps_sum num_laters_per_step 1 n + k + k)).
  iIntros (Hinv) "[[Hcred Hk1] Hk2]".
  iDestruct (Hwp with "Hk1") as "Hwp".
  iMod "Hwp" as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_postconditions _ _ _
       (IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hcred Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 1 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt') "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite length_replicate in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  iApply ("Hφ" with "[//] [%] [ ] Hσ Hes'");
    (* FIXME: Different implicit types for [length] are inferred, so [lia] and
    [congruence] do not work due to https://github.com/coq/coq/issues/16634 *)
    [by rewrite Hlen1 Hlen3| |]; last first.
  { by rewrite big_sepL2_replicate_r // big_sepL_omap. }
  (* At this point in the adequacy proof, we use a trick: we effectively run the
    user-provided WP proof again (i.e., instantiate the `invGS_gen` and execute the
    program) by using the lemma [wp_progress_gen]. In doing so, we can obtain
    the progress part of the adequacy theorem.
  *)
  iPureIntro. intros e2 -> Hel.
  eapply (wp_progress_gen hlc);
    [ done | clear stateI Φ fork_post state_interp_mono Hlen1 Hlen3 | done|done].
  iIntros (?) "Hk".
  iDestruct (Hwp with "Hk") as "Hwp".
  iMod "Hwp" as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

(** Adequacy when using later credits (the default) *)
Definition wp_strong_adequacy := wp_strong_adequacy_gen HasLc.
Global Arguments wp_strong_adequacy _ _ {_}.
