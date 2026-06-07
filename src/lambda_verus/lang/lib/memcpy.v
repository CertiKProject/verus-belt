From guarding Require Import guard tactics.
From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode.
From lrust.util Require Import non_atomic_cell_map update.
Set Default Proof Using "Type".

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #☠
    else "dst" <- !"src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].

Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Notation "e1 <-{ n ',Σ' i } ! e2" :=
  (e1%E%E <- #(LitInt i);; e1 +ₗ #(LitInt 1) <-{n} !e2)%E
  (at level 80, n, i at next level, format "e1  <-{ n ,Σ  i }  ! e2") : expr_scope.

(*
Lemma wp_memcpy `{!lrustGS Σ} E l1 l2 vl1 vl2 (n : Z):
  ↑non_atomic_cell_map.naN ⊆ E →
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  {{{ l1 ↦∗ vl1 ∗ l2 ↦∗ vl2 }}}
    #l1 <-{n} !#l2 @ E
  {{{ RET #☠; l1 ↦∗ vl2 ∗ l2 ↦∗ vl2 }}}.
Proof.
  iIntros (? Hvl1 Hvl2 Φ) "(Hl1 & Hl2) HΦ".
  iLöb as "IH" forall (n l1 l2 vl1 vl2 Hvl1 Hvl2). wp_rec. wp_op; case_bool_decide; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n|]; try (discriminate || lia).
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]; rewrite !heap_mapsto_vec_cons. subst n.
    iDestruct "Hl1" as "[Hv1 Hl1]". iDestruct "Hl2" as "[Hv2 Hl2]".
    Local Opaque Zminus.
    wp_read; wp_write. do 3 wp_op. iApply ("IH" with "[%] [%] Hl1 Hl2"); [lia..|].
    iIntros "!> [Hl1 Hl2]"; iApply "HΦ"; by iFrame.
Qed.
*)

(*
Lemma wp_memcpy_guarded `{!lrustGS Σ} E l1 l2 vl1 vl2 H F (n : Z) d d' :
  F ⊆ E →
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  {{{ l1 ↦∗ vl1 ∗ (H &&{F; d+1}&&> (l2 ↦∗ vl2)) ∗ H ∗ ⧖d ∗ ⧖d' }}}
    #l1 <-{n} !#l2 @ E
  {{{ RET #☠; l1 ↦∗ vl2 ∗ H ∗ £ (d' * d') }}}.
Proof.
*)

Lemma wp_memcpy_guarded `{!lrustGS Σ} E l1 l2 vl1 vl2 Hw Hr (n : Z) d :
  ↑naN ∪ ↑timeN ⊆ E →
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  time_ctx -∗
  {{{ l1 #↦∗ vl1 ∗
      (Hw &&{↑naN; d}&&> l1 #↦∗_) ∗
      (Hr &&{↑naN; d}&&> (l2.1 ↦[^ l2.2]∗ vl2))
      ∗ Hw ∗ Hr
      ∗ ⧖d ∗ £(6*d) }}}
    #(l1.1) <-{n} !#(l2.1) @ E
  {{{ RET #☠; l1 #↦∗ vl2 ∗ Hw ∗ Hr }}}.
Proof.
  iIntros (? Hvl1 Hvl2) "#TIME". iIntros (Φ). iModIntro.
  iIntros "(Hl1 & wguard & rguard & Hw & Hr & ⧖ & £) HΦ".
  iLöb as "IH" forall (n l1 l2 vl1 vl2 Hvl1 Hvl2). wp_rec. wp_op; case_bool_decide; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n|]; try (discriminate || lia).
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]. subst n.
    iDestruct "⧖" as "#⧖".
    
    destruct l1 as [l1 cells1]. destruct cells1; first by done.
    rewrite heap_mapsto_cloc_vals_vec_cons.
    iDestruct "Hl1" as "[Hv1 Hl1]". 
    rewrite heap_mapsto_cloc_emp_cons.
    
    destruct l2 as [l2 cells2]. destruct cells2.
      { iApply fupd_wp. leaf_open_laters "rguard" with "Hr" as "R"; first by set_solver.
        iDestruct "£" as "[£d £]".
        iMod (lc_fupd_elim_laterN with "£d R") as "R".
        iMod "R" as "[R back]". done.
      }
    simpl. rewrite heap_mapsto_cells_val_vec_cons.
    
    iDestruct (guards_weaken_rhs_sep_l with "wguard") as "#wguard1".
    iDestruct (guards_weaken_rhs_sep_r with "wguard") as "#wguard2".
    iDestruct (guards_weaken_rhs_sep_l with "rguard") as "#rguard1".
    iDestruct (guards_weaken_rhs_sep_r with "rguard") as "#rguard2".
    
    iAssert (£(3*d + 3*d))%I with "[£]" as "[£1 £2]". { iApply (lc_weaken with "£"). lia. }
    
    wp_bind (!#l2)%E. iApply (wp_read_na_guarded_cells with "[Hr £1]"); first by set_solver.
      { iFrame "rguard1". iFrame. }
    iNext. iIntros "Hr".
    wp_bind (#l1 <- v2)%E.
    iApply (wp_write_na_guarded_more_credits with "TIME [Hw Hv1 £2]"); first by set_solver.
      { iFrame "wguard1". iFrame. iFrame "⧖". }
    
    iNext. iIntros "[Hv2 [Hw £]]".
    
    wp_seq. do 3 wp_op.
    iApply ("IH" $! (Z.pos (Pos.of_succ_nat (length vl1)) - 1)%Z (l1 +ₗ 1, cells1) (l2 +ₗ 1, cells2) with "[%] [%] Hl1 wguard2 rguard2 Hw Hr ⧖ £"); [lia..|].
    iIntros "!> [Hl1 Hl2]"; iApply "HΦ"; by iFrame.
Qed.
