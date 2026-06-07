From iris.algebra Require Import lib.mono_nat numbers dfrac_agree.
From iris.base_logic Require Import lib.own.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Class timeGS Σ := TimeG {
  #[global] time_mono_nat_inG :: inG Σ mono_natR;
  #[global] time_nat_inG :: inG Σ (authR natUR);
  #[global] time_bool_fracG :: inG Σ (dfrac_agreeR (leibnizO bool)) ;
  #[global] time_nat_fracG :: inG Σ (dfrac_agreeR (leibnizO nat)) ;
  time_global_name : gname;
  time_persistent_name : gname;
  time_cumulative_name : gname;
  time_enabled_bool_name : gname;
  time_sum_name : gname;
}.

Class timePreG Σ := TimePreG {
  #[global] time_preG_mono_nat_inG :: inG Σ mono_natR;
  #[global] time_preG_nat_inG :: inG Σ (authR natUR);
  #[global] time_preG_bool_frac_inG :: inG Σ (dfrac_agreeR (leibnizO bool));
  #[global] time_preG_nat_frac_inG :: inG Σ (dfrac_agreeR (leibnizO nat));
}.

Definition timeΣ : gFunctors :=
  #[GFunctor (constRF mono_natR); GFunctor (constRF (authR natUR)); GFunctor (dfrac_agreeR (leibnizO bool)); GFunctor (dfrac_agreeR (leibnizO nat))].
Global Instance subG_timePreG Σ : subG timeΣ Σ → timePreG Σ.
Proof. solve_inG. Qed.

Definition timeN : namespace := nroot .@ "leaf_lifetime_logic" .@ "user" .@ "time".

(* when this namespace is available, you can get ⧗ (and thus increment ⧖, get credits)
   for the step. This lets us get access to the resources before the step actually executes *)
Definition advN : namespace := nroot .@ "timeAdv".

Definition advance_credits (n: nat) : nat := (10*n*n + 10*n + 10)%nat.

Lemma advance_credits_mono (n n': nat) :
    (n ≤ n' → advance_credits n ≤ advance_credits n')%nat.
Proof. unfold advance_credits. nia. Qed.
    
Fixpoint sum_advance_credits (n: nat) : nat :=
    match n with
      | 0%nat => 0
      | S n' => (2 ^ (S (S n'))) * advance_credits (2 ^ S (S n')) + sum_advance_credits n'
    end.

Lemma sum_advance_credits_ge1 (n: nat) :
    n ≥ 1 →
    sum_advance_credits n = ((2 ^ S n) * advance_credits (2 ^ S n) + sum_advance_credits (n-1))%nat.
Proof.
  intro Hn. destruct n.
  - lia.
  - replace (S n - 1)%nat with n; last by lia. trivial.
Qed.

Section definitions.
  Context `{!timeGS Σ}.
  
  Definition enable γ (b: bool): iProp Σ := own γ (to_frac_agree (A:=leibnizO bool) (1/2)%Qp b).
  Lemma enable_agree γ (b1 b2: bool) : enable γ b1 -∗ enable γ b2 -∗ ⌜ b1 = b2 ⌝.
  Proof.
    unfold enable. iIntros "A B". iCombine "A B" as "H".
    iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
  Lemma enable_upd γ (b1 b2 b3: bool) : enable γ b1 -∗ enable γ b2 ==∗ enable γ b3 ∗ enable γ b3. 
  Proof.
    unfold enable. iIntros "A B". iCombine "A B" as "H".
    rewrite <- own_op. iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
  
  Lemma enable_alloc b :
      ⊢ |==> ∃ γ, enable γ b ∗ enable γ b.
  Proof.
    unfold enable. iMod (own_alloc (to_frac_agree (A:=leibnizO bool) (1 / 2) b ⋅ to_frac_agree (A:=leibnizO bool) (1 / 2) b)) as (γo) "[Ho Ho2]".
      - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
      - iModIntro. iExists γo. iFrame.
  Qed.
  
  Local Definition cur_sum γ (n: nat): iProp Σ := own γ (to_frac_agree (A:=leibnizO nat) (1/2)%Qp n).
  Local Lemma cur_sum_agree γ (n1 n2: nat) : cur_sum γ n1 -∗ cur_sum γ n2 -∗ ⌜ n1 = n2 ⌝.
  Proof.
    unfold cur_sum. iIntros "A B". iCombine "A B" as "H".
    iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
  Lemma cur_sum_upd γ (n1 n2 n3: nat) : cur_sum γ n1 -∗ cur_sum γ n2 ==∗ cur_sum γ n3 ∗ cur_sum γ n3. 
  Proof.
    unfold cur_sum. iIntros "A B". iCombine "A B" as "H".
    rewrite <- own_op. iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
  Local Lemma cur_sum_alloc n :
      ⊢ |==> ∃ γ, cur_sum γ n ∗ cur_sum γ n.
  Proof.
    unfold enable. iMod (own_alloc (to_frac_agree (A:=leibnizO nat) (1 / 2) n ⋅ to_frac_agree (A:=leibnizO nat) (1 / 2) n)) as (γo) "[Ho Ho2]".
      - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
      - iModIntro. iExists γo. iFrame.
  Qed.

  (** persistent time receipt *)
  Definition persistent_time_receipt (n : nat) :=
    own time_persistent_name (mono_nat_lb n).
  (** cumulative time receipt *)
  Definition cumulative_time_receipt (n : nat) :=
    own time_cumulative_name (◯ n).
  (** invariant *)
  Definition time_ctx `{!invGS Σ} : iProp Σ :=
    inv timeN (∃ n m,
       own time_global_name (mono_nat_lb (n + m)) ∗
       own time_cumulative_name (● n) ∗
       own time_persistent_name (●MN m) ∗
       £ (n * advance_credits (n + m)) ∗
       cur_sum time_sum_name (n + m)%nat) ∗
    inv advN (∃ n, enable time_enabled_bool_name true ∗ cur_sum time_sum_name (n + 2 + n)%nat ∗ cumulative_time_receipt (n + 2)%nat).
  (** authority *)

  Definition time_interp (n: nat) : iProp Σ :=
    (enable time_enabled_bool_name true ∗ own time_global_name (●MN (2 ^ (S n) - 2)) ∗ ⌜(n ≥ 1)%nat⌝)
    ∨ (enable time_enabled_bool_name false ∗ own time_global_name (●MN (2 ^ (S (S n)) - 2)%nat ) ).
End definitions.

Global Typeclasses Opaque persistent_time_receipt cumulative_time_receipt.
Global Instance: Params (@persistent_time_receipt) 2 := {}.
Global Instance: Params (@cumulative_time_receipt) 2 := {}.

Notation "⧖ n" := (persistent_time_receipt n)
  (at level 1, format "⧖ n") : bi_scope.
Notation "⧗ n" := (cumulative_time_receipt n)
  (at level 1, format "⧗ n") : bi_scope.

Section time.
  Context `{!timeGS Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance persistent_time_receipt_timeless n : Timeless (⧖n).
  Proof. unfold persistent_time_receipt. apply _. Qed.
  Global Instance persistent_time_receipt_persistent n : Persistent (⧖n).
  Proof. unfold persistent_time_receipt. apply _. Qed.
  Global Instance cumulative_time_receipt_timeless n : Timeless (⧗n).
  Proof. unfold cumulative_time_receipt. apply _. Qed.

  Lemma time_interp_step n :
    time_interp n ⊢ |==> time_interp (S n).
  Proof. 
    iIntros "[[En [A %nge1]]|[En A]]".
     - iLeft. iFrame. iSplitL.
      + iApply own_update; last by iFrame "A". eapply mono_nat_update.
        cbn [Nat.pow].
        nia.
      + iPureIntro. lia.
     - iRight. iFrame.
      + iApply own_update; last by iFrame "A". eapply mono_nat_update.
        cbn [Nat.pow].
        nia.
  Qed.

  Lemma persistent_time_receipt_mono n m :
    (n ≤ m)%nat → ⧖m ⊢ ⧖n.
  Proof.
    intros ?. unfold persistent_time_receipt. by apply own_mono, mono_nat_lb_mono.
  Qed.
  
  Lemma cumulative_time_receipt_mono n m :
    (n ≤ m)%nat → ⧗m ⊢ ⧗n.
  Proof.
    intros ?. unfold cumulative_time_receipt.
    by apply own_mono, auth_frag_mono, nat_included.
  Qed.

  Lemma persistent_time_receipt_sep n m : ⧖(n `max` m) ⊣⊢ ⧖n ∗ ⧖m.
  Proof. by rewrite /persistent_time_receipt mono_nat_lb_op own_op. Qed.
  Lemma cumulative_time_receipt_sep n m : ⧗(n + m) ⊣⊢ ⧗n ∗ ⧗m.
  Proof. by rewrite /cumulative_time_receipt -nat_op auth_frag_op own_op. Qed.

  Global Instance persistent_time_receipt_from_sep n m : FromSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /FromSep. by rewrite persistent_time_receipt_sep. Qed.
  Global Instance persistent_time_receipt_combine_sep_as n m : CombineSepAs ⧖n ⧖m ⧖(n `max` m).
  Proof. rewrite /CombineSepAs. by rewrite persistent_time_receipt_sep. Qed.
  Global Instance persistent_time_receipt_into_sep n m : IntoSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /IntoSep. by rewrite persistent_time_receipt_sep. Qed.
  Global Instance cumulative_time_receipt_from_sep n m : FromSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /FromSep. by rewrite cumulative_time_receipt_sep. Qed.
  Global Instance cumulative_time_receipt_combine_sep_as n m : CombineSepAs ⧗n ⧗m ⧗(n + m).
  Proof. rewrite /CombineSepAs. by rewrite cumulative_time_receipt_sep. Qed.
  Global Instance cumulative_time_receipt_into_sep n m : IntoSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /IntoSep. by rewrite cumulative_time_receipt_sep. Qed.

  Lemma persistent_time_receipt_0 : ⊢ |==> ⧖0.
  Proof. rewrite /persistent_time_receipt. apply own_unit. Qed.
  Lemma cumulative_time_receipt_0 : ⊢ |==> ⧗0.
  Proof. rewrite /cumulative_time_receipt. apply own_unit. Qed.

  Lemma cumulative_persistent_time_receipt `{!invGS Σ} E n m :
    ↑timeN ⊆ E → time_ctx -∗ ⧗n -∗ ⧖m ={E}=∗ ⧖(n + m).
  Proof.
    iIntros (?) "[#TIME #ADV] Hn #Hm".
    unfold persistent_time_receipt, cumulative_time_receipt.
    iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm' & Hc & Hsum)".
    iDestruct (own_valid_2 with "Hn' Hn")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hm' Hm") as %?%mono_nat_both_valid.
    iMod (own_update_2 with "Hn' Hn") as "Hnn'".
    { apply (auth_update_dealloc _ _ (n'-n)%nat), nat_local_update.
      rewrite -plus_n_O. lia. }
    iMod (own_update with "Hm'") as "Hm'n".
    { apply (mono_nat_update (m'+n)%nat); lia. }
    iDestruct (own_mono _ _ (mono_nat_lb _) with "Hm'n") as "#$".
    { rewrite <-mono_nat_included. apply mono_nat_lb_mono. lia. }
    iModIntro; iSplitL; [|done]. iExists _, _. iFrame.
    rewrite (_:(n'+m')%nat = ((n' - n) + (m'+n))%nat); [iFrame|lia].
    iApply (lc_weaken with "Hc"). nia.
  Qed.
  
  Lemma cumulative_persistent_time_receipt_get_credits `{!invGS Σ} E m :
    ↑timeN ⊆ E → time_ctx -∗ ⧗1 -∗ ⧖m ={E}=∗ ⧖(m + 1) ∗ £(advance_credits m).
  Proof.
    iIntros (Hmask) "[#TIME _] Hn #Hm".
    unfold persistent_time_receipt, cumulative_time_receipt.
    iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm' & H£ & Sum')" "Hclose".
    iDestruct (own_valid_2 with "Hn' Hn")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hm' Hm") as %?%mono_nat_both_valid.
    iMod (own_update_2 with "Hn' Hn") as "Hnn'".
    { apply (auth_update_dealloc _ _ (n'-1)%nat), nat_local_update.
      rewrite -plus_n_O. lia. }
    iMod (own_update with "Hm'") as "Hm'n".
    { apply (mono_nat_update (m'+1)%nat); lia. }
    replace (n' * advance_credits (n' + m'))%nat
      with ((n'-1) * advance_credits (n' + m') + advance_credits (n' + m'))%nat; last by nia.
    iDestruct "H£" as "[H£ H£1]".
    iDestruct (own_mono _ _ (mono_nat_lb _) with "Hm'n") as "#$".
    { rewrite <-mono_nat_included. apply mono_nat_lb_mono. lia. }
    iMod ("Hclose" with "[Hglob H£ Sum' Hnn' Hm'n]"). {
      iFrame. replace (n' - 1 + (m' + 1))%nat with (n' + m')%nat by lia. iFrame.
    }
    iApply (lc_weaken with "H£1"). apply advance_credits_mono. lia.
  Qed.

  Lemma step_cumulative_time_receipt `{!invGS Σ} E n d :
    ↑timeN ∪ ↑advN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖ d ={E, E∖↑advN}=∗ ⌜n ≥ 1⌝ ∗ time_interp (n-1) ∗ enable time_enabled_bool_name false ∗ ⧗(d + 2)%nat ∗
    (time_interp n ∗ enable time_enabled_bool_name false ∗ £(2^(S (S n)) * advance_credits (2 ^(S (S n)) )) ={E∖↑advN, E}=∗ time_interp (S n)).
  Proof.
    iIntros (?) "[#TIME #ADV] Hn #Hd".
    iInv "ADV" as (nm) ">(Enable & Sum & ⧗)" "Hclose1".
    iDestruct "Hn" as "[[En2 [Hn %Hge1]]|[En2 Hn]]".
    2: { iDestruct (enable_agree with "En2 Enable") as "%X". discriminate. }

    rewrite /persistent_time_receipt /cumulative_time_receipt.
    iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm' & H£ & Sum')" "Hclose".
    iDestruct (cur_sum_agree with "Sum Sum'") as "%Hsumeq".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm' Hd") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hn' ⧗") as %[Hnm_n' _]%auth_both_valid.
    move: (Hnm_n' 0%nat); clear Hnm_n'; rewrite -cmra_discrete_included_iff nat_included => Hnm_n'.

    iMod ("Hclose" with "[$]").
    iMod (enable_upd _ _ _ false with "Enable En2") as "[En1 En2]".

    iModIntro. iSplitR. { done. }
    iSplitL "En2 Hn".
      { iRight. iFrame. replace (S (n-1)) with n; last by lia. done. }
    iFrame "En1". iSplitL "⧗".
      { iApply (own_mono with "⧗"). apply auth_frag_mono. 
        apply nat_included. nia. }
    iIntros "[HSn [En1 Hc1]]". 
    iDestruct "HSn" as "[[En2 [HSn _]]|[En2 HSn]]".
    { iDestruct (enable_agree with "En1 En2") as "%X". discriminate. }
    
    iInv "TIME" as (n'' m'') ">(Hglob & Hn' & Hm' & H£ & Sum')" "Hclose".
    iDestruct (cur_sum_agree with "Sum Sum'") as "%Hsumeq2".
    iDestruct (own_valid_2 with "Hm' Hd") as %?%mono_nat_both_valid.

    iMod (enable_upd _ _ _ true with "En1 En2") as "[En1 En2]".
    iDestruct (own_mono _ _ (mono_nat_lb _) with "HSn ") as "#Hglob'". 
    { apply mono_nat_included. }
    iLeft.
    iFrame "En1 HSn".

    iMod (cur_sum_upd _ _ _ ((n'' + m'') + 2 + (n'' + m''))%nat with "Sum Sum'") as "[Sum Sum']".
    iMod (own_update _ _ (_ ⋅ ◯(n'' + m'' + 2)%nat) with "Hn'") as "[HSn' Hcum]".
    { apply auth_update_alloc, nat_local_update. by rewrite -plus_n_O. }


    iMod ("Hclose" with "[HSn' Hm' Hc1 Sum']"). { iExists (n'' + m''  + 2 + n'' )%nat, m''. iFrame.
    iSplitR.
    - iApply (own_mono with "Hglob'"). apply mono_nat_lb_mono.
      cbn [Nat.pow] in *.
      nia.
    - replace (n'' + (n'' + m'' + 2))%nat with (n'' + m'' + 2 + n'')%nat by lia.
      rewrite Nat.add_assoc.
      iFrame.
      iApply (lc_weaken with "Hc1").
      have ? : (n'' + m'' + 2 + n'' ≤ 2 ^ S( S n ))%nat.
      { cbn [Nat.pow] in *. nia. }
      assert (advance_credits (n'' + m'' + 2 + n'' + m'')%nat <= advance_credits (2^(S (S n)) ))%nat.
      { apply advance_credits_mono.
        cbn [Nat.pow] in *.
        nia.
      }
      apply Nat.mul_le_mono; try nia.
    }
    iMod ("Hclose1" with "[Hcum En2 Sum]"). { iFrame . }
    iModIntro.
    iPureIntro;lia.
  Qed.
  
  (*Lemma step_persistent_time_receipt `{!invGS Σ} E n m :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖m ={E, E∖↑timeN}=∗ ⌜n ≥ 1⌝ ∗ time_interp (n - 1) ∗ enable time_enabled_bool_name false ∗ £(advance_credits m) ∗
    (time_interp n ∗ enable time_enabled_bool_name false ∗ £(advance_credits (S n)) ={E∖↑timeN, E}=∗ time_interp (S n) ∗ ⧖(S m)).
  Proof.
    iIntros (?) "#TIME Hn H⧖". iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm' & Hc & Enable)" "Hclose".
    iDestruct "Hn" as "[[En2 [Hn %Hge1]]|[En2 Hn]]".
    2: { iDestruct (enable_agree with "En2 Enable") as "%X". discriminate. }
    iMod (enable_upd _ _ _ false with "Enable En2") as "[En1 En2]".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iModIntro. iSplitR. { done. } iSplitL "En2 Hn".
      { iRight. iFrame. replace (S (n-1)) with n; last by lia. done. }
    iFrame "En1".
    iDestruct (own_valid_2 with "Hm' H⧖") as %?%mono_nat_both_valid.
    iSplitL "Hc".
    { iApply lc_weaken; last by iFrame "Hc". apply advance_credits_mono. lia. }
    iIntros "[HSn [En1 Hc1]]". unfold cumulative_time_receipt.
    iMod (own_update with "Hn'") as "[HSn' Hcu]".
    { apply auth_update_alloc, nat_local_update. by rewrite -plus_n_O. }
    iDestruct "HSn" as "[[En2 HSn]|[En2 HSn]]".
    { iDestruct (enable_agree with "En1 En2") as "%X". discriminate. }
    iMod (enable_upd _ _ _ true with "En1 En2") as "[En1 En2]".
    iDestruct (own_mono _ _ (mono_nat_lb _) with "[HSn En2]") as "#H'Sn".
    { apply mono_nat_included. } { iFrame "HSn". }
    
    iMod ("Hclose" with "[Hglob Hm' Hc1 HSn' En2]"). 
      + iExists (n' + 1)%nat, m'. iFrame.
        iSplitR "Hc1 Hglob".
        - iApply (own_mono with "H'Sn"). apply mono_nat_lb_mono. lia.
        - iNext. iApply lc_weaken; last by iFrame "Hc1". apply advance_credits_mono. lia.
      + iSplitL "HSn En1".
        - iModIntro. iLeft. iFrame. iPureIntro. lia.
        - iMod (cumulative_persistent_time_receipt with "TIME Hcu H⧖") as "X"; done.
  Qed.*)

  Lemma time_receipt_le `{!invGS Σ} E n m m' :
    ↑advN ∪ ↑timeN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖m -∗ ⧗m' ={E}=∗
    ⌜m+m' ≤ 2 ^ S n⌝%nat ∗ time_interp n ∗ ⧗m'.
  Proof.
    iIntros (?) "[#TIME #ADV] Hn Hm Hm'".
    iInv "TIME" as (m'0 m0) ">(Hglob & Hm'0 & Hm0 & Hc & Sum)".
    iInv "ADV" as (nm) ">(En & Sum' & ⧗)".
    iDestruct "Hn" as "[[En2 [Hn %Hge1 ]]|[En2 Hn]]".
    2: { iDestruct (enable_agree with "En En2") as "%X". discriminate. }
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm0 Hm") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm'0 Hm'")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. iModIntro. iSplitR. {
      iPureIntro.
      cbn [Nat.pow] in *.
      nia. }
    iLeft. iFrame.
    iPureIntro. trivial.
  Qed.

  Lemma time_receipt_le' `{!invGS Σ} E n m m' :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖m -∗ ⧗m' ={E}=∗
    ⌜m+m' ≤ 2 ^ (S (S n)) ⌝%nat ∗ time_interp n ∗ ⧗m'.
    (* ⌜m+m' ≤ 2 ^ S n⌝%nat ∗ time_interp n ∗ ⧗m'. *)
  Proof.
    iIntros (?) "[#TIME #ADV] Hn Hm Hm'".
    iInv "TIME" as (m'0 m0) ">(Hglob & Hm'0 & Hm0 & Hc & Sum )".
    iDestruct "Hn" as "[[En2 [Hn %Hge1]]|[En2 Hn]]".
    {
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm0 Hm") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm'0 Hm'")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. iModIntro. iSplitR. {
      cbn [Nat.pow] in *. iPureIntro. nia. }
    iLeft. iFrame.
    iPureIntro. trivial.
    }
    {
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm0 Hm") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm'0 Hm'")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. iModIntro. iSplitR. {
      simpl in *. iPureIntro. cbn [Nat.pow] in H0. 
      nia.
    } iRight. iFrame.
    }
  Qed.
End time.

Lemma time_init `{!invGS Σ, !timePreG Σ} E : ↑timeN ⊆ E →
  £(advance_credits 4) ⊢ |={E}=> ∃ _ : timeGS Σ, time_ctx ∗ time_interp 1.
Proof.
  intros ?. iIntros "Hc".
  iMod (own_alloc (●MN 2 ⋅ mono_nat_lb 2)) as (time_global_name) "[A B]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (time_persistent_name) "p";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 2%nat ⋅ ◯ 2%nat)) as (time_cumulative_name) "[c ⧗]"; [by apply auth_both_valid|].
  iMod (own_alloc (to_frac_agree (A:=leibnizO bool) (1 / 2) true ⋅ to_frac_agree (A:=leibnizO bool) (1 / 2) true)) as (time_bool_name) "[Ho Ho2]".
      { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  iMod (own_alloc (to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat ⋅ to_frac_agree (A:=leibnizO nat) (1 / 2) 2%nat)) as (time_cur_sum_name) "[Hx Hx2]".
      { rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial. }
  iExists (TimeG _ _ _ _ _ time_global_name time_persistent_name time_cumulative_name time_bool_name time_cur_sum_name).
  iSplitR "A Ho"; last first.
  - iModIntro. iLeft. eauto with iFrame lia.
  - iMod (inv_alloc with "[Ho2 Hx2 ⧗]") as "I1"; last first.
    iMod (inv_alloc with "[Hc Hx B p c]") as "I2"; last first.
    iModIntro. iSplit. 
    { iFrame "I2". } 
    { iFrame "I1". } 
    { iFrame. 
      iApply (lc_weaken with "Hc"). rewrite /advance_credits. nia. }
    { iFrame. iNext. iExists 0%nat. by  iFrame. }
Qed.
