Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
From lrust.util Require Import cancellable_na_invariants.
Require Import lrust.lifetime.lifetime_full.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

Class cnaInv_logicG Σ := {
  cnaInv_na_inv_inG : na_invG Σ ;
}.
Local Existing Instance cnaInv_na_inv_inG. 
  
Definition cnaInv_logicΣ : gFunctors := #[ GFunctor (exclR unitO) ; na_invΣ ].

Global Instance subG_cnaInv_logicΣ Σ : subG cnaInv_logicΣ Σ → cnaInv_logicG Σ.
Proof.
  solve_inG.
Qed.  

(* note: as a wrapper around cancellable_na_invariant, this doesn't really do anything *)

Section CancellableInvariants.
  Context {Σ: gFunctors}.
  Context `{!cnaInv_logicG Σ}.
  Context `{!invGS Σ}.
  Context `{!llft_logicGS Σ}.
  
  Definition cna_active (γ: gname) : iProp Σ := na_active γ.
  
  Definition cna_inv (γ: gname) (p: na_inv_pool_name) (N: namespace) (P: iProp Σ) : iProp Σ := 
      na_inv γ p N P.
  
  Definition cna_lifetimes (p: na_inv_pool_name) (κs: gmultiset lft) : iProp Σ :=
      cancellable_na_invariants.na_lfts_own_gmultiset (cancellable_na_invariants.γm p) κs.
    
  Definition cna_own (p: na_inv_pool_name) (Ena: coPset) : iProp Σ := na_own p Ena.
  
  Global Instance pers_na_inv γ p N P : Persistent (cna_inv γ p N P).
  Proof.
    typeclasses eauto.
  Qed.
  
  Definition cna_closer (κ: lft) (p: na_inv_pool_name) (N: namespace) (P: iProp Σ) : iProp Σ :=
    (∀ F' E' κs', ⌜↑nainvN ⊆ E'⌝ → ▷ P ∗ na_own p F' ∗ cancellable_na_invariants.na_lfts_own_gmultiset (cancellable_na_invariants.γm p) κs'
          ={E'}=∗ ∃ κs'', ⌜ κs' = {[+ κ +]} ⊎ κs'' ∧ F' ## ↑N ⌝ ∗ na_own p (F' ∪ ↑N) ∗ cancellable_na_invariants.na_lfts_own_gmultiset (cancellable_na_invariants.γm p) κs'').
  
  Lemma cna_pool_alloc E :
    ⊢ |={E}=> ∃ p, cna_own p ⊤ ∗ cna_lifetimes p ∅.
  Proof. iApply na_alloc. Qed.
    
  Lemma cna_alloc (p: na_inv_pool_name) (N: namespace) (E : coPset) (P : iProp Σ) :
    ▷ P ={E}=∗ ∃ γ, cna_inv γ p N P ∗ cna_active γ.
  Proof.
    setoid_rewrite bi.sep_comm. iApply na_inv_alloc.
  Qed.
  
  Lemma cna_inv_acc_with_lifetime_guard γ p N P (G: iProp Σ) Ena E κ κs d :
    (↑nainvN ∪ ↑NllftG ⊆ E) →
    (↑N ⊆ Ena) →
    cna_inv γ p N P -∗
    cna_own p Ena -∗
    cna_lifetimes p κs -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    £ (d+1) -∗
    (@[κ] &&{↑NllftG; d}&&> cna_active γ) -∗
    G
    ={E}=∗
      cna_own p (Ena ∖ ↑N) ∗
      cna_lifetimes p ({[+ κ +]} ⊎ κs) ∗
      G ∗
      (▷ P) ∗
      cna_closer κ p N P.
  Proof.
      iIntros (Hmask1 Hmask2) "Inv Own Lt #Guards £ #Guard2 G".
      iDestruct (guards_transitive_right with "Guards Guard2") as "Guard3".
      iMod (na_inv_acc γ p E Ena N P κs κ G d with "Inv Own Lt Guard3 Guard2 £ G")
          as "(? & ? & ? & ? & ?)"; trivial.
      iModIntro. iFrame.
  Qed.
  
  Lemma cna_close κ p N P κs Ena E :
      ↑nainvN ⊆ E →
      cna_closer κ p N P -∗
      (▷ P) -∗
      cna_own p Ena -∗
      cna_lifetimes p κs ={E}=∗ ∃ κs',
        ⌜κs = {[+ κ +]} ⊎ κs' ∧ Ena ## ↑N⌝ ∗
        cna_own p (Ena ∪ ↑N) ∗
        cna_lifetimes p κs'.
  Proof.
      iIntros (Hmask) "A P Own Lt". unfold cna_closer.
      iDestruct ("A" $! Ena E with "[] [P Own Lt]") as "Y"; first by done. { iFrame. }
      iApply "Y".
  Qed.
  
  Lemma cna_destroy γ p (N: namespace) P κs (E : coPset) G :
    (↑nainvN ∪ ↑NllftG ⊆ E) →
    cna_inv γ p N P -∗
    cna_lifetimes p κs -∗
    cna_active γ -∗
    (∀ (κ: lft) , ⌜κ ∈ κs⌝ -∗ (G &&{↑NllftG}&&> @[κ])) -∗
    G
    ={E}=∗
      cna_lifetimes p κs ∗ G ∗ ▷ P.
  Proof.
      iIntros (Hmask) "Inv Lt Active Gs G".
      iMod (na_inv_destroy with "Inv Lt Active Gs G") as "X"; trivial.
  Qed.
  
  (*
  Lemma na_inv_acc_strong γ p N P G F E1 E2 :
    (↑N ## F) →
    (↑nainvN ∪ F ⊆ E1) →
    (↑N ⊆ E2) →
    na_inv γ p N P -∗ (G &&{F}&&> na_active γ) -∗ G -∗ na_own p E2 ={E1}=∗
      na_own p (E2 ∖ ↑N) ∗
      G ∗ (▷ P) ∗ (∀ E', (▷ (P ∨ na_active γ)) ∗ na_own p E' ={E1}=∗ na_own p (E' ∪ ↑N)).
  Proof.
    intros disj subs subs2. iIntros "#ei #gu g NaOwn".
    iAssert (na_own p (↑N) ∗ na_own p (E2 ∖ ↑N))%I with "[NaOwn]" as "[NaOwn1 NaOwn2]".
      { rewrite <- na_own_union; last by set_solver.
        replace (↑N ∪ (E2 ∖ ↑N)) with E2. { iFrame. } rewrite <- guard.copset_diff_union; trivial.
      }
    iDestruct (na_inv_acc p E1 (↑N) N with "ei NaOwn1") as "T". { set_solver. } { set_solver. }
    iMod "T" as "[[P|a] [NaOwnEmp back]]".
    - replace ((↑N ∪ F) ∖ ↑N) with F by set_solver.
      + iModIntro. iFrame "g". iFrame "P". iFrame "NaOwn2".
        iIntros (E') "[POrna_active NaOwn]".
        iDestruct ("back" with "[NaOwnEmp POrna_active]") as "B". { iFrame. }
        iMod "B". iModIntro.
        iDestruct (na_own_disjoint with "NaOwn B") as "%disj2".
        rewrite na_own_union. { iFrame. } set_solver.
    - iDestruct (guards_open G (na_active γ) F F with "gu g") as "X". { set_solver. }
      iApply (fupd_mask_mono F). { set_solver. }
      iMod "X" as "[a2 _]". iMod "a".
      iExFalso. iApply active_active_false. iFrame "a". iFrame "a2".
  Qed.
  
  Lemma na_inv_cancel γ p N P E1 E2 :
    (↑nainvN ⊆ E1) →
    (↑N ⊆ E2) →
    na_inv γ p N P -∗ na_active γ -∗ na_own p E2 ={E1}=∗ (▷ P) ∗ na_own p E2.
  Proof.
    intros subs subs2. iIntros "#ei a NaOwn".
    iDestruct (na_inv_acc_strong γ p N P (na_active γ) ∅ E1 E2 with "ei [] a NaOwn") as "J".
      { set_solver. } { set_solver. } { trivial. } { iApply guards_refl. }
    iMod "J" as "[NaOwn [a [p back]]]". iDestruct ("back" $! (E2 ∖ ↑N)) as "back".
    iDestruct ("back" with "[a NaOwn]") as "back". { iFrame. }
    iMod "back".
    replace ((E2 ∖ (↑N) ∪ ↑N)) with E2. { iModIntro. iFrame. }
    have j := guard.copset_diff_union E2 (↑N).
    rewrite union_comm_L.
    rewrite <- (guard.copset_diff_union); trivial.
  Qed.
  *)

End CancellableInvariants.
