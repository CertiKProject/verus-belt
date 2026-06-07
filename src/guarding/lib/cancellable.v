Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import guarding.internal.na_invariants_fork.

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

Class ecInv_logicG Σ := {
  ecInv_exclG : inG Σ (exclR unitO) ;
}.
Local Existing Instance ecInv_exclG. 
  
Definition ecInv_logicΣ : gFunctors := #[ GFunctor (exclR unitO) ].

Global Instance subG_ecInv_logicΣ Σ : subG ecInv_logicΣ Σ → ecInv_logicG Σ.
Proof.
  solve_inG.
Qed.  

Section CancellableInvariants.

  Context {Σ: gFunctors}.
  Context `{!ecInv_logicG Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!na_invG Σ}.

  Definition Active (γ: gname) : iProp Σ := own γ (Excl ()).
  
  Definition external_inv (γ: gname) (N: namespace) (P: iProp Σ) : iProp Σ := 
      inv N (P ∨ Active γ).
      
  Definition external_na_inv (γ: gname) (p: na_inv_pool_name) (N: namespace) (P: iProp Σ) : iProp Σ := 
      na_inv p N (P ∨ Active γ).
      
  Global Instance external_inv_proper γ N :
      Proper ((≡) ==> (≡)) (external_inv γ N).
  Proof.
      solve_proper.
  Qed.
      
  Global Instance external_na_inv_proper γ p N :
      Proper ((≡) ==> (≡)) (external_na_inv γ p N).
  Proof.
      solve_proper.
  Qed.
  
  Local Lemma new_active : ⊢ |==> ∃ γ , Active γ.
  Proof.
    iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold Active. iFrame "H".
  Qed.
  
  Local Lemma active_active_false (γc : gname) : Active γc ∗ Active γc ⊢ False.
  Proof. 
    iIntros "X". unfold Active. rewrite <- own_op.
    iDestruct (own_valid with "X") as "%J". contradiction.
  Qed.
  
  Lemma external_inv_alloc (N: namespace) (E : coPset) (P : iProp Σ) :
    ▷ P ={E}=∗ ∃ γ, external_inv γ N P ∗ Active γ.
  Proof.
    iIntros "latp".
    iMod new_active as (γ) "a".
    iMod (inv_alloc N E (P ∨ Active γ) with "[latp]") as "x".
    { iNext. iLeft. iFrame "latp". }
    iModIntro. iExists γ. iFrame "a". iFrame "x".
  Qed.
  
  Global Instance pers_external_inv γ N P : Persistent (external_inv γ N P).
  Proof.
    typeclasses eauto.
  Qed.
  
  Lemma external_inv_acc_strong γ N P G F E :
    (↑N ## F) →
    (↑N ∪ F ⊆ E) →
    external_inv γ N P ∗ (G &&{F}&&> Active γ) ∗ G ={E, E ∖ ↑N}=∗
      G ∗ (▷ P) ∗ (∀ E', (▷ (P ∨ Active γ)) ={E', ↑N ∪ E'}=∗ True).
  Proof.
    intros disj subs. iIntros "[#ei [#gu g]]".
    iDestruct (inv_acc_strong E N with "ei") as "T". { set_solver. }
    iMod "T" as "[[P|a] back]".
    - replace ((↑N ∪ F) ∖ ↑N) with F by set_solver.
      + iModIntro. iFrame "g". iFrame "P". iFrame "back".
    - iDestruct (guards_open G (Active γ) F F with "gu g") as "X". { set_solver. }
      iApply (fupd_mask_mono F). { set_solver. }
      iMod "X" as "[a2 _]". iMod "a".
      iExFalso. iApply active_active_false. iFrame "a". iFrame "a2".
  Qed.
  
  Lemma external_inv_cancel γ N P E :
    (↑N ⊆ E) →
    external_inv γ N P ∗ Active γ ={E}=∗ ▷ P.
  Proof.
    intros subs. iIntros "[#ei a]".
    iDestruct (external_inv_acc_strong γ N P (Active γ) ∅ E with "[a]") as "J".
      { set_solver. } { set_solver. }
      { iFrame "a". iFrame "ei". iApply guards_refl. }
    iMod "J" as "[a [p back]]". iDestruct ("back" $! (E ∖ ↑N)) as "back".
    iDestruct ("back" with "[a]") as "back".
    { iModIntro. iRight. iFrame "a". }
    iMod "back".
    replace ((↑N) ∪ (E ∖ (↑N))) with E. { iModIntro. iFrame "p". }
    rewrite <- (guard.copset_diff_union); trivial.
  Qed.
    
  Lemma external_inv_na_alloc (p: na_inv_pool_name) (N: namespace) (E : coPset) (P : iProp Σ) :
    ▷ P ={E}=∗ ∃ γ, external_na_inv γ p N P ∗ Active γ.
  Proof.
    iIntros "latp".
    iMod new_active as (γ) "a".
    iMod (na_inv_alloc p E N (P ∨ Active γ) with "[latp]") as "x".
    { iNext. iLeft. iFrame "latp". }
    iModIntro. iExists γ. iFrame "a". iFrame "x".
  Qed.
  
  Global Instance pers_external_na_inv γ p N P : Persistent (external_na_inv γ p N P).
  Proof.
    typeclasses eauto.
  Qed.
  
  Lemma external_na_inv_acc_strong γ p N P G F E1 E2 :
    (↑nainvN ∪ F ⊆ E1) →
    (↑N ⊆ E2) →
    external_na_inv γ p N P -∗ (G &&{F}&&> Active γ) -∗ G -∗ na_own p E2 ={E1}=∗
      na_own p (E2 ∖ ↑N) ∗
      G ∗ (▷ P) ∗ (∀ E', (▷ (P ∨ Active γ)) ∗ na_own p E' ={E1}=∗ na_own p (E' ∪ ↑N)).
  Proof.
    intros subs subs2. iIntros "#ei #gu g NaOwn".
    iAssert (na_own p (↑N) ∗ na_own p (E2 ∖ ↑N))%I with "[NaOwn]" as "[NaOwn1 NaOwn2]".
      { rewrite <- na_own_union; last by set_solver.
        replace (↑N ∪ (E2 ∖ ↑N)) with E2. { iFrame. } rewrite <- guard.copset_diff_union; trivial.
      }
    iDestruct (na_inv_acc p E1 (↑N) N with "ei NaOwn1") as "T". { set_solver. } { set_solver. }
    iMod "T" as "[[P|a] [NaOwnEmp back]]".
    - iModIntro. iFrame "g". iFrame "P". iFrame "NaOwn2".
      iIntros (E') "[POrActive NaOwn]".
      iDestruct ("back" with "[NaOwnEmp POrActive]") as "B". { iFrame. }
      iMod "B". iModIntro.
      iDestruct (na_own_disjoint with "NaOwn B") as "%disj2".
      rewrite na_own_union. { iFrame. } set_solver.
    - iDestruct (guards_open G (Active γ) F F with "gu g") as "X". { set_solver. }
      iApply (fupd_mask_mono F). { set_solver. }
      iMod "X" as "[a2 _]". iMod "a".
      iExFalso. iApply active_active_false. iFrame "a". iFrame "a2".
  Qed.
     
  Lemma external_na_inv_cancel γ p N P E1 E2 :
    (↑nainvN ⊆ E1) →
    (↑N ⊆ E2) →
    external_na_inv γ p N P -∗ Active γ -∗ na_own p E2 ={E1}=∗ (▷ P) ∗ na_own p E2.
  Proof.
    intros subs subs2. iIntros "#ei a NaOwn".
    iDestruct (external_na_inv_acc_strong γ p N P (Active γ) ∅ E1 E2 with "ei [] a NaOwn") as "J".
      { set_solver. } { set_solver. } { iApply guards_refl. }
    iMod "J" as "[NaOwn [a [p back]]]". iDestruct ("back" $! (E2 ∖ ↑N)) as "back".
    iDestruct ("back" with "[a NaOwn]") as "back". { iFrame. }
    iMod "back".
    replace ((E2 ∖ (↑N) ∪ ↑N)) with E2. { iModIntro. iFrame. }
    have j := guard.copset_diff_union E2 (↑N).
    rewrite union_comm_L.
    rewrite <- (guard.copset_diff_union); trivial.
  Qed.

End CancellableInvariants.

Section CancellableInvariantsLc.
  Context {Σ: gFunctors}.
  Context `{!ecInv_logicG Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  
  Local Lemma lc_fupd_elim_laterN E P n : 
    £ n -∗ (▷^n P) -∗ |={E}=> P.
  Proof.
    induction n.
    - iIntros. done.
    - iIntros "C P". replace (S n) with (n + 1) by lia.
      iDestruct (lc_split with "C") as "[C1 C2]". replace (n + 1) with (S n) by lia.
      iDestruct (lc_fupd_elim_later with "C2 P") as "P". iMod (IHn with "C1 P") as "P".
      done.
  Qed.
 
  Lemma external_na_inv_acc_strong_later γ p N P G F E1 E2 n :
    (↑nainvN ∪ F ⊆ E1) →
    (↑N ⊆ E2) →
    £n -∗
    external_na_inv γ p N P -∗ (G &&{F;n}&&> Active γ) -∗ G -∗ na_own p E2 ={E1}=∗
      na_own p (E2 ∖ ↑N) ∗
      G ∗ (▷ P) ∗ (∀ E', (▷ (P ∨ Active γ)) ∗ na_own p E' ={E1}=∗ na_own p (E' ∪ ↑N)).
  Proof.
    intros subs subs2. iIntros "£ #ei #gu g NaOwn".
    iAssert (na_own p (↑N) ∗ na_own p (E2 ∖ ↑N))%I with "[NaOwn]" as "[NaOwn1 NaOwn2]".
      { rewrite <- na_own_union; last by set_solver.
        replace (↑N ∪ (E2 ∖ ↑N)) with E2. { iFrame. } rewrite <- guard.copset_diff_union; trivial.
      }
    iDestruct (na_inv_acc p E1 (↑N) N with "ei NaOwn1") as "T". { set_solver. } { set_solver. }
    iMod "T" as "[[P|a] [NaOwnEmp back]]".
    - iModIntro. iFrame "g". iFrame "P". iFrame "NaOwn2".
      iIntros (E') "[POrActive NaOwn]".
      iDestruct ("back" with "[NaOwnEmp POrActive]") as "B". { iFrame. }
      iMod "B". iModIntro.
      iDestruct (na_own_disjoint with "NaOwn B") as "%disj2".
      rewrite na_own_union. { iFrame. } set_solver.
    - iDestruct (guards_open_later G (Active γ) F F with "gu g") as "X". { set_solver. }
      iApply (fupd_mask_mono F). { set_solver. }
      iMod "X". iMod (lc_fupd_elim_laterN with "£ X") as "X".
      iMod "X" as "[a2 _]". iMod "a".
      iExFalso. iApply active_active_false. iFrame "a". iFrame "a2".
  Qed.
End CancellableInvariantsLc.
