From iris.bi Require Import updates.
From iris.proofmode Require Import proofmode.
From lrust.util Require Import basic.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop wsat invariants.
From iris.base_logic.lib Require Export later_credits.

(* TODO : move all that to Iris *)

(** * Utility for Multi-Step-Taking Updates *)

Section lemmas.
Context `{!BiFUpd PROP}.
Implicit Type P Q R: PROP.

Global Instance step_fupdN_proper E n : Proper ((⊣⊢) ==> (⊣⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_ne E n m : Proper (dist m ==> dist m) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_mono E n : Proper ((⊢) ==> (⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_flip_mono E n :
  Proper (flip (⊢) ==> flip (⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. move=> ???. by apply step_fupdN_mono. Qed.

Lemma step_fupdN_full_intro E n P : P ={E}▷=∗^n P.
Proof. iIntros "?". by iApply step_fupdN_intro. Qed.

Lemma step_fupdN_nmono m n P E : m ≤ n → (|={E}▷=>^m P) -∗ (|={E}▷=>^n P).
Proof.
  move: n. elim m=>/= [|?]; [iIntros; by iApply step_fupdN_full_intro|].
  move=> IH ? /succ_le [?[->Le]]/=. iIntros "?". by iApply IH.
Qed.

Lemma step_fupdN_sep n P Q E :
  (|={E}▷=>^n P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^n (P ∗ Q)).
Proof.
  elim n=>/= [|?]; [iIntros; by iFrame|]. iIntros (IH) ">UpdP >UpdQ !>!>".
  by iMod (IH with "UpdP UpdQ").
Qed.

Global Instance step_fupdN_from_sep n P Q E :
  FromSep (|={E}▷=>^n (P ∗ Q)) (|={E}▷=>^n P) (|={E}▷=>^n Q).
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_sep with "P Q").
Qed.

Global Instance step_fupdN_combine_sep_as n P Q E :
  CombineSepAs (|={E}▷=>^n P) (|={E}▷=>^n Q) (|={E}▷=>^n (P ∗ Q)).
Proof.
  rewrite /CombineSepAs. iIntros "[P Q]". iApply (step_fupdN_sep with "P Q").
Qed.

Global Instance frame_step_fupdN p R E n P Q :
  Frame p R P Q → Frame p R (|={E}▷=>^n P) (|={E}▷=>^n Q).
Proof.
  rewrite /Frame=> <-. iIntros "[R Q]".
  iApply step_fupdN_frame_l. iFrame "R". iFrame.
Qed.

Lemma step_fupdN_sep_max m n P Q E :
  (|={E}▷=>^m P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^(m `max` n) (P ∗ Q)).
Proof.
  set l := m `max` n. iIntros "A B". 
  iDestruct (step_fupdN_nmono _ l with "A") as "A". { lia. }
  iDestruct (step_fupdN_nmono _ l with "B") as "B". { lia. }
  iDestruct (step_fupdN_sep with "A B") as "X".
  iFrame.
Qed.

Global Instance step_fupdN_from_sep_max m n P Q E :
  FromSep (|={E}▷=>^(m `max` n) (P ∗ Q)) (|={E}▷=>^m P) (|={E}▷=>^n Q) | 10.
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_sep_max with "P Q").
Qed.

Global Instance step_fupdN_combine_sep_as_max m n P Q E :
  CombineSepAs (|={E}▷=>^m P) (|={E}▷=>^n Q) (|={E}▷=>^(m `max` n) (P ∗ Q)) | 10.
Proof.
  rewrite /CombineSepAs. iIntros "[P Q]". iApply (step_fupdN_sep_max with "P Q").
Qed.

Lemma step_fupdN_with_emp n P E F :
  (|={E, F}=> |={F}▷=>^n |={F, E}=> P) -∗ (|={E, ∅}=> |={∅}▷=>^n |={∅, E}=> P).
Proof.
  iIntros ">Upd". iInduction n as [|] "IH"=>/=.
  - iApply fupd_mask_intro; [set_solver|]. by iIntros ">?".
  - iApply fupd_mask_intro; [set_solver|]. iIntros ">_". iMod "Upd".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Get !>". iMod "Get".
    iMod ("IH" with "Upd") as "$".
Qed.

Lemma step_fupdN_addS E m P :
  (|={E}▷=>^(S m) P) ⊣⊢ (|={E}▷=> |={E}▷=>^m P).
Proof.
  trivial.
Qed.

Lemma step_fupdN_add E n m P :
  (|={E}▷=>^(n + m) P) ⊣⊢ (|={E}▷=>^n |={E}▷=>^m P).
Proof.
  induction n as [|n IH]; [done| rewrite /= IH //].
Qed.

Lemma step_fupdN_fupd_mask_mono E₁ E₂ n P :
  E₁ ⊆ E₂ → (|={E₁}▷=>^n |={E₁}=> P) -∗ (|={E₂}▷=>^n |={E₂}=> P).
Proof.
  move=> Hsub. induction n as [|n IH].
  - by iApply fupd_mask_mono.
  - iIntros "H /=". iApply fupd_mask_mono; [done|]. iApply IH.
    iMod "H". iModIntro. by iApply fupd_mask_mono; [done|].
Qed.

Lemma step_fupdN_mask_mono Eo1 Eo2 Ei1 Ei2 n P :
  Ei2 ⊆ Ei1 → Eo1 ⊆ Eo2 → (|={Eo1}[Ei1]▷=>^n P) ⊢ |={Eo2}[Ei2]▷=>^n P.
Proof.
  intros Hm1 Hm2. induction n; first done.
  iIntros "A".
  iDestruct (step_fupd_mask_mono Eo1 Eo2 Ei1 Ei2 with "A") as "A"; trivial.
  iMod "A". iModIntro. iNext. iMod "A". iModIntro. iApply IHn. done.
Qed.

Lemma fupd_step_fupdN_front E n P :
  (|={E}=> |={E}▷=>^n |={E}=> P) -∗ (|={E}▷=>^n |={E}=> P).
Proof.
  destruct n. - simpl. iIntros ">>$". done. - iIntros ">>A". iModIntro. iNext. done.
Qed.

End lemmas.

Section later_credits_lemmas.
Context `{!invGS Σ}. 
Implicit Type P Q R: iProp Σ.

Lemma lc_fupd_elim_laterN E P n : 
   £ n -∗ (▷^n P) -∗ |={E}=> P.
Proof.
  induction n.
  - iIntros. done.
  - iIntros "C P". replace (S n) with (n + 1) by lia.
    iDestruct (lc_split with "C") as "[C1 C2]". replace (n + 1) with (S n) by lia.
    iDestruct (lc_fupd_elim_later with "C2 P") as "P". iMod (IHn with "C1 P") as "P".
    done.
Qed.

Lemma lc_step_fupd_elim_later P Eo Ei :
  £ 1 -∗ (|={Eo}[Ei]▷=> P) ={Eo}=∗ P.
Proof.
  iIntros "A B".
  iMod "B". iMod (lc_fupd_elim_later with "A B") as "B".
  iFrame.
Qed.

Lemma lc_step_fupdN_elim_later k P Eo Ei :
  £ k -∗ (|={Eo}[Ei]▷=>^(k) P) ={Eo}=∗ P.
Proof.
  induction k.
  - iIntros "A B". iFrame "B". iModIntro. done.
  - iIntros "A B". iDestruct "A" as "[A A']".
    iMod "B". iMod (lc_fupd_elim_later with "A B") as "B".
    iDestruct (IHk with "A' B") as "C". iMod "C". iFrame "C".
Qed.

End later_credits_lemmas.
