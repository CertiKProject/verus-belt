From lrust.typing Require Export type.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_util.
  Context `{!typeG Σ}.
  
  Definition uniq_body_pers_component {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
  (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
    &{κ, idx} (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ 
      ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid).

  Definition uniq_body {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
      (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
    .VO[ξ] x (d, g) ∗ ⧗1 ∗
    idx_bor_tok idx ∗
    &{κ, idx} (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ 
      ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid).
      
  Lemma uniq_body_pers_component_impl {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc)
    : uniq_body ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof.
    unfold uniq_body. iIntros "[A [B [C D]]]". iFrame "D".
  Qed.
  
  Lemma alloc_uniq_body
      {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (d: nat) (g: nat)
      (κ: lft) (tid: thread_id) (l: cloc) E
   :
    (↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E) →
    ⊢ llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗ ⧖(S d `max` g) -∗
      (▷ ty.(ty_gho) x d g tid) -∗
      l #↦!∗ ty.(ty_phys) x tid -∗
      ⧗1
      ={E}=∗
      ∃ ξi ζi idx,
        let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
        let ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))) ζi in
        uniq_body ty x ξi d g idx κ tid l ∗
        ⟨π, π ζ = (l.1, π ξ)⟩ ∗
        ([†κ] ={↑Nllft}=∗
           ▷ ∃ x' (d' g' : nat), ⧖ (S d' `max` g') ∗
               .PC[ξ] x' (vπ x') (d', g') ∗
               ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid).
  Proof.
    intros Hmask. iIntros "#LFT #PROPH #UNIQ #time gho pt £".
    iMod (uniq_intro x (vπ x) (d, g) with "PROPH UNIQ") as (ξi) "[ξVo ξPc]". { set_solver. }
    iMod (@uniq_intro _ _ _ _ (at_locₛ 𝔄) (l.1, x) (@vπ (at_locₛ 𝔄) (l.1, x)) (d, g) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]". { set_solver. }
    
    iDestruct (uniq_proph_tok with "ξVo ξPc") as "(ξVo & ξtok & ξPc)".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ζPc)".
    set ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))) ζi.
    set ξ := PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi.
    iMod (proph_resolve_toks _ ζ (λ π, (l.1, π ξ)) [ξ] with "PROPH ζtok [ξtok]") as "[ζObs ξtok]".
      { set_solver. } { intros π π' asn. rewrite asn; trivial. apply elem_of_list_here. }
      { rewrite big_sepL_singleton. iFrame "ξtok". } rewrite big_sepL_singleton.
    iSpecialize ("ξPc" with "ξtok").
    
    iMod (llftl_borrow E κ (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid)%I with "LFT [gho pt ξPc]") as "[Bor Back]". { set_solver. }
    { iModIntro. iExists x, d, g. iFrame. iFrame "time". }
    iDestruct (llftl_bor_idx with "Bor") as (idx) "[Bor Tok]".
    iModIntro.
    iExists ξi, ζi, idx. iFrame.
  Qed.
 
  (*Lemma ty_share_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    &{κ'} (uniq_body ty vπ ξi d κ tid l) -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      &{κ'} 1:[PrVar (𝔄 ↾ prval_to_inh vπ) ξi] ∗ ty.(ty_shr) vπ d κ' tid l ∗ q.[κ'].
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #In #In' Bor κ'".
    iMod (bor_sep with "LFT Bor") as "[BorVo Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. iIntros "!>!>!>".
    iMod (bor_shorten with "[] Bor") as "Bor".
    { iApply lft_incl_glb; [done|iApply lft_incl_refl]. }
    do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorPc Borty]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[[Vo Pc] ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod ("ToBor" with "[Vo ToPc] ξ") as "[Borξ κ']".
    { iIntros "!> >ξ !>!>". iFrame "Vo". by iApply "ToPc". }
    iMod (ty_share with "LFT [] Borty κ'") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). by iIntros "!> >[$$]".
  Qed.*)

  (*Lemma ty_own_proph_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    uniq_body ty vπ ξi d κ tid l -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in
      ∃ζl q', ⌜vπ ./ ζl⌝ ∗ q':+[ζl ++ [ξ]] ∗
        (q':+[ζl ++ [ξ]] ={E}=∗ uniq_body ty vπ ξi d κ tid l ∗ q.[κ']).
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #Inκ #? [Vo Bor] [κ' κ'₊]".
    iMod (lft_incl_acc with "Inκ κ'") as (?) "[κ' Toκ']"; [done|].
    iMod (bor_acc with "LFT Bor κ'") as "[Big ToBor]"; [done|].
    iIntros "!>!>!>". iDestruct "Big" as (??) "(#⧖ & Pc & %vl & ↦ & ty)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod (ty_own_proph with "LFT [] ty κ'₊") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ζl & Toty) !>".
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl ξ") as (?) "[ζlξ Toζlξ]".
    iExists _, _. iSplit; [done|]. iIntros "{$ζlξ}ζlξ".
    iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[ty $]". iDestruct ("ToPc" with "ξ") as "Pc".
    iMod ("ToBor" with "[Pc ↦ ty]") as "[Bor κ']".
    { iNext. iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iMod ("Toκ'" with "κ'") as "$". by iFrame.
  Qed.*)
  
  
  Lemma guards_exist_eq {A B C} (a' : A) (b' : B) (c' : C) (P Q : iProp Σ) (X : A → B → C → iProp Σ) E n1 n2 n :
    (∀ a b c , ((Q ∧ X a b c)%I ⊢ ⌜a = a' ∧ b = b' ∧ c = c'⌝)%I) →
    (n1 ≤ n) →
    (n2 ≤ n) →
    (P &&{E;n1}&&> Q) -∗
    (P &&{E;n2}&&> (∃ a b c , X a b c))
    -∗
    P &&{E;n}&&> (X a' b' c').
  Proof.
    intros Hent He1 He2. iIntros "PguardsQ PguardsBig".
    assert ((∃ (a : A) (b : B) (c : C), X a b c)
        ⊣⊢ (∃ (abc : A * B * C), X (abc.1.1) (abc.1.2) (abc.2))) as Hequiv1.
      { iSplit. { iDestruct 1 as (a b c) "X". iExists (a, b, c). iFrame. }
        iDestruct 1 as (abc) "X". iFrame. }
    assert ((∃ x : A * B * C, X x.1.1 x.1.2 x.2 ∗ ⌜x = (a', b', c')⌝) ⊣⊢ X a' b' c') as Hequiv2.
      { iSplit. { iDestruct 1 as (x) "[A %Heqs]". subst x. iFrame "A". }
        iIntros "X". iExists (a', b', c'). iFrame. done. }
    setoid_rewrite Hequiv1.
    leaf_hyp "PguardsQ" laters to n as "PguardsQ'"; first by trivial.
    leaf_hyp "PguardsBig" laters to n as "PguardsBig'"; first by trivial.
    iDestruct (guards_strengthen_exists _ _ _ (λ x, ⌜x = (a', b', c')⌝)%I with "PguardsQ' PguardsBig'") as "T".
      { intros x. simpl. iIntros "A". iDestruct (Hent with "A") as "%Heqs".
        destruct Heqs as [Heq1 [Heq2 Heq3]]. iPureIntro. subst a'. subst b'. subst c'.
        destruct x as [[a b] c]; trivial.
      }
    setoid_rewrite Hequiv2. iFrame.
  Qed.
  
  (*Lemma uniq_body_freeze {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
      ↑Nllft ⊆ E →
      llft_ctx -∗ 
      (G &&{↑NllftG}&&> @[κ]) -∗
      uniq_body ty x ξi d g idx κ tid l -∗
      G
      ={E}=∗
        G
        ∗ .VO[PrVar ( 𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g)
        ∗ £ (2 * d * (g + 1) + 2)
        ∗ &{κ} (⧖(S d `max` g) ∗
                .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (vπ x) (d, g) ∗
                ty_gho ty x d g tid ∗ l ↦∗ ty_phys ty x tid).
  Proof.
    intros Hmask. iIntros "#LFT Uniq". iDestruct "Uniq" as "(ξVo & £ & Tok & ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor Tok") as "ξBor".
    iMod (llftl_bor_freeze with "LFT ξBor") as (x2) "ξBor". { solve_ndisj. }
      Unshelve. 2: { split. apply x. }
    iMod (llftl_bor_freeze with "LFT ξBor") as (d2) "ξBor". { solve_ndisj. }
    iMod (llftl_bor_freeze with "LFT ξBor") as (g2) "ξBor". { solve_ndisj. }
    iModIntro. iFrame. iFrame "#".
    "ξVo" : .VO[PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi] (l1, x1) (d', g')
  "£saved" : £ (2 * d' * (g' + 1) + 2)
  "Tok" : idx_bor_tok idx
  "ξBor" : &{κ,idx}
             (∃ (x' : ~~ (`(pv_ty (PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi)))) 
                (d'0 g'0 : nat), ⧖(S d'0 `max` g'0) ∗
                .PC[PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi] x' (vπ x') (d'0, g'0) ∗
                ty_gho (own_ptr n ty) x' d'0 g'0 tid ∗ l ↦∗ ty_phys (own_ptr n ty) x' tid)*)

  
  Lemma shr_bor_from_finalized_uniq_bor {𝔄} (ty: type 𝔄) x ξi d g κ tid l F :
    ↑Nllft ⊆ F →
    llft_ctx -∗ 
    (&{κ} (⧖(S d `max` g) ∗
          .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (vπ x) (d, g) ∗
          ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid))
    ={F}=∗
   @[κ] &&{↑NllftG; 1}&&> (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid).
  Proof.
    intros Hmask. iIntros "#LFT Bor".
    iDestruct (llftl_bor_idx with "Bor") as (idx) "[#Bor Tok]".
    iMod (llftl_borrow_shared F κ (idx_bor_tok idx) with "Tok") as "[#Glat _]". { set_solver. }
    iDestruct (guards_remove_later_rhs with "Glat") as "G".
    iDestruct (llftl_idx_bor_guard' κ idx _ (@[κ])%I with "LFT Bor [] G") as "GBor".
      { iApply guards_refl. }
    iDestruct (guards_weaken_rhs_sep_r with "GBor") as "GBor2".
    iDestruct (guards_later_absorb_1 with "GBor2") as "GBor3".
   iModIntro.
   iDestruct (guards_weaken_rhs_sep_r with "GBor3") as "GBor4".
   iDestruct (guards_weaken_rhs_sep_r with "GBor4") as "GBor5".
   iFrame "GBor5".
  Qed.
  
  Lemma resolve_uniq_body {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E L G F :
    Timeless G →
    lctx_lft_alive E L κ → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={F}=∗
      ⟨π, π (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) = (vπ x π)⟩ ∗ G
      ∗ (@[κ] &&{↑NllftG; 1}&&> (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid)).
  Proof.
    intro Ti.
    iIntros (Alv ?) "#LFT #PROPH #UNIQ #TIME #In E #Guard G [Vo [⧗ Bor]] /=".
    (*
    replace ((d + (d + 0)) * (g + 1) + 2) with
        (d * (g + 1) + d * (g + 1) + 1 + 1) by lia.
    iDestruct "Credits" as "[[[Creditk Creditk'] Credit1] Credit1']".
    *)
    
    leaf_open "Guard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alv with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    
    iDestruct (guards_transitive with "Guard Alv") as "#Guard_K".
    iMod (fractional.frac_split_guard_in_half with "G Guard_K") as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]". { solve_ndisj. }
    
    (*iDestruct (llftl_bor_idx with "Bor") as (idx) "[#Bor Tok]".*)
    
    (*iDestruct (llftl_idx_bor_guard' κ idx _ (fractional.half γ2 ∗ idx_bor_tok idx ∗ .VO[PrVar (𝔄 ↾ prval_to_inh vπ) ξi] vπ d) with "LFT Bor [] []") as "BorGuard".
      { iApply guards_weaken_lhs_sep_l. iFrame "#". }
      { leaf_by_sep. iIntros "(A & B & C)". iFrame. iIntros. iFrame. }*)
      
      
    (*iAssert (fractional.half γ2 ∗ idx_bor_tok idx ∗ .VO[PrVar (𝔄 ↾ prval_to_inh vπ) ξi] vπ d &&{
               ↑NllftG }&&> ▷ ty_gho ty vπ d d tid)%I as "BorGuard'".
    2: {*)
      
    
    iMod (llftl_begin with "LFT") as (κ') "[κ' #κ'end]". { solve_ndisj. }
    iMod (llftl_borrow_shared _ κ' with "H2") as "[#Guards2Lat InhH2]". { solve_ndisj. }
    iDestruct (guards_remove_later_rhs with "Guards2Lat") as "Guard2". iClear "Guards2Lat".
    iDestruct (guards_transitive with "Guard2 Ghalf2") as "Incl".
    
    iDestruct (lft_bor_idx1 with "Bor") as "Bor".
    iMod (llftl_bor_freeze with "LFT Bor") as (x') "Bor". { set_solver. }
      Unshelve. 2: { split. apply x. }
    iMod (llftl_bor_freeze with "LFT Bor") as (d') "Bor". { set_solver. }
    iMod (llftl_bor_freeze with "LFT Bor") as (g') "Bor". { set_solver. }
    
    iMod (llftl_reborrow with "LFT Incl Bor") as "[Bor OriginalBor]". { solve_ndisj. }
    iMod (llftl_bor_acc with "LFT Bor κ'") as "[Inner ForallQ]". { solve_ndisj. }
    iDestruct "Inner" as "(>#⧖ & Pc & Gho & >PT)".
    iMod (uniq_strip_later with "Vo Pc") as "(%agree1 & %agree2 & Vo & Pc)".
    subst x'. inversion agree2. subst d'. subst g'.
    
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[⧖S £]"; first by solve_ndisj.
    iDestruct (lc_weaken (d * (g + 1) + d * (g + 1) + 1 + 1) with "£") as "£". {
      unfold advance_credits. nia. }
    iDestruct "£" as "[[[Creditk Creditk'] Credit1] Credit1']".
    
    iMod (lc_fupd_elim_later with "Credit1' Gho") as "Gho".
    
    have ty_indep := syn_indep x.
    
    iAssert (▷^(d*(g+1)) (∀ ζ : proph_var, ⌜ζ ∈ ξl x⌝ -∗ fractional.half γ2 ∗ ty_gho ty x d g tid &&{ ↑NllftG; d*(g+1) }&&> 1:[ζ]))%I as "#Hallζlater". {
      iIntros (ζ) "%HIn".
      replace (d * (g+1)) with (0 + d * (g+1)); last by lia.
      iDestruct (ty_gho_pers_impl with "Gho") as "#GhoPers".
      iDestruct (ty_guard_proph with "LFT In GhoPers") as "X". { apply HIn. }
      iNext. iApply "X".
      { iApply guards_weaken_lhs_sep_l. iApply "Ghalf2". }
      { iApply guards_weaken_sep_r. }
    }
    iMod (lc_fupd_elim_laterN with "Creditk' Hallζlater") as "#Hallζ".
    
    iMod (uniq_resolve_guarded with "Hallζ UNIQ PROPH Vo Pc [H3 Gho]") as "X". { solve_ndisj. }
    { apply ty_indep. }
    { iFrame. }
    iMod (lc_fupd_elim_laterN with "Creditk X") as "X". iMod "X". 
    iDestruct "X" as "[Obs [Pc [H3 gho]]]".
    
    iDestruct ("ForallQ" $! (⧖ (S d `max` g) ∗ .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (vπ x) (d, g) ∗ ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid)%I with "[Pc gho PT ⧖]") as "ForallQ".
    { iSplitR. { iNext. iIntros "[A d]". iModIntro. iFrame "A". }
      { iNext. iFrame. iFrame "⧖". } }
    iMod (fupd_mask_mono with "ForallQ") as "[Borrow Al]". { solve_ndisj. }
    iDestruct ("κ'end" with "Al") as "κ'ended".
    iDestruct (lc_step_fupd_elim_later with "Credit1 κ'ended") as "κ'ended".
    iMod (fupd_mask_mono with "κ'ended") as "#κ'ended". { solve_ndisj. }
    iMod ("InhH2" with "κ'ended") as ">H2".
    iDestruct ("Halfback2" with "H2 H3") as "G".
    iMod (fupd_mask_mono with "G") as "G". { solve_ndisj. }
    
    iDestruct ("OriginalBor" with "κ'ended") as "OriginalBor".
    iMod (fupd_mask_mono with "OriginalBor") as "OriginalBor". { solve_ndisj. }
    iMod (shr_bor_from_finalized_uniq_bor with "LFT OriginalBor") as "ShrBor". { solve_ndisj. }
    
    iModIntro. iFrame.
  Qed.
  
  Lemma incl_uniq_body_pers_component {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho) x d tid vl ↔ ty'.(ty_gho) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys Pc". unfold uniq_body_pers_component.
    unfold prval_to_inh.
    iApply (llftl_idx_shorten with "InLft").
    iApply llftl_idx_bor_iff; [|done]. iIntros "!>!>".
    iSplit.
      - iDestruct 1 as (x' d'' g'') "(⧖ & Pc & gho & phys)". iExists x', d'', g''.
        iFrame "⧖".
        iSplitL "Pc". { iDestruct (proph_ctrl_proper with "Pc") as "Pc"; last by iFrame "Pc".
          + trivial.
          + intros y. trivial.
          + trivial.
        }
        rewrite EqPhys. iFrame "phys".
        iApply "EqOwn". iFrame "gho".
     - iDestruct 1 as (vπ' d'' g'') "(⧖ & Pc & gho & phys)". iExists vπ', d'', g''.
        iFrame "⧖".
        iSplitL "Pc". { iDestruct (proph_ctrl_proper with "Pc") as "Pc"; last by iFrame "Pc".
          + trivial.
          + intros y. trivial.
          + trivial.
        }
        rewrite EqPhys. iFrame "phys".
        iApply "EqOwn". iFrame "gho".
  Qed.
  
  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho) x d tid vl ↔ ty'.(ty_gho) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ uniq_body ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys (A & B & Tok & Pc)".
    iFrame "B".
    iFrame "A". iFrame "Tok".
    iApply (incl_uniq_body_pers_component ty ty' x ξi d g idx κ κ' tid l with "InLft EqOwn");
      done.
  Qed.
  
    Lemma uniq_guards_get_guards_pt {𝔄} (ty: type 𝔄) (P Q R : iProp Σ) x d g ξi tid l :
    ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R) &&{ ↑NllftG }&&> (Q ∗
            ▷ ∃ x' (d' g' : nat), ⧖(S d' `max` g') ∗
                .PC[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x' (vπ x') (d', g') ∗ ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid))
    ⊢ ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R) &&{ ↑NllftG; 1 }&&> l #↦!∗ ty_phys ty x tid)%I.
  Proof.
    iIntros "#G".
    iDestruct (guards_weaken_rhs_sep_r with "G") as "G2".
    iClear "G".
    iDestruct (guards_later_absorb_1 with "G2") as "G3". iClear "G2".
    iDestruct (guards_exist_eq x d g
      (P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R)%I
      (.VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g))%I
      _ _ 0 1 1
      with "[] G3") as "G4".
      - intros x0 d0 g0. iIntros "And".
        iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) with "[And]") as "%Heq".
        + iSplit. { iDestruct "And" as "[And _]". iFrame "And". }
          iDestruct "And" as "[_ (? & T & ?)]". iFrame "T".
        + iPureIntro. destruct Heq as [Heq1 Heq2]. inversion Heq2. intuition.
      - lia. - lia.
      - leaf_by_sep. iIntros "(? & ? & ?)". iFrame. iIntros. done.
      - iApply (guards_transitive_left with "G4 []").
        leaf_by_sep. iIntros "(? & ? & ? & ?)". iFrame. iIntros. done.
  Qed.
  
    
  Lemma uniq_body_transform {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      (▷ ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid
        ={E}=∗ ▷ ty_gho ty' x' d g tid ∗ l' #↦!∗ ty_phys ty' x' tid ∗ 
        (∀ x'1 d1 g1 , ▷ ty_gho ty' x'1 d1 g1 tid ∗ l' #↦!∗ ty_phys ty' x'1 tid ∗ ⧖(S d1 `max` g1)
          ={↑NllftUsr}=∗ ∃ d2 g2, ▷ ty_gho ty (f ~~$ₛ x'1) d2 g2 tid ∗ l #↦!∗ ty_phys ty (f ~~$ₛ x'1) tid ∗ ⧖(S d2 `max` g2))
        ) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
      let ζ := PrVar (𝔅 ↾ prval_to_inh (vπ x')) ζi in
      ⟨π, π ξ = (!ₛ) f (π ζ)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask. iIntros "#LFT #PROPH #UNIQ wand #GuardsK G UniqBody".
    iDestruct "UniqBody" as "(ξVo & £saved & ξTok & ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor ξTok") as "ξBor".
    iMod (llftl_bor_acc_guarded with "LFT ξBor GuardsK G") as "[P ToBor]". { set_solver. }
    

    iMod (bi.later_exist_except_0 with "P") as (x1 d1 g1) "(>#⧖ & ξPc & Gho & >Pt)".
    
    iMod (uniq_strip_later with "ξVo ξPc") as (Hineq1 Hineq2) "[ξVo ξPc]".
    subst x1. inversion Hineq2. subst d1. subst g1.
    
    iMod (uniq_intro x' (vπ x') (d, g) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [set_solver|].
    
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    rewrite proph_tok_singleton. set ξ := PrVar _ ξi. set ζ := PrVar _ ζi.
    
    iMod (uniq_preresolve ξ _ (λ π, f $ₛ (π ζ)) with "UNIQ PROPH ξVo ξPc ζ") as "(#EqObs & ζ & ToξPc)".
      { set_solver. } { apply proph_dep_constr. apply (proph_dep_one ζ). }
    
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    
    iCombine "Gho Pt" as "GhoPt". iMod ("wand" with "GhoPt") as "[Gho [Pt R]]".
    
    iDestruct ("ToBor" with "[Pt ToξPc R Gho ζPc]") as "A"; last first.
      - iMod (fupd_mask_mono with "A") as "[Bor G]". { set_solver. }
        iModIntro. iDestruct (llftl_bor_idx with "Bor") as (ζidx) "[ζBor ζTok]".
        iExists ζi. iExists ζidx. iFrame "G". iFrame "ζTok". iFrame "ζVo". iFrame "£saved".
        iFrame "ζBor". iFrame "EqObs".
      - iSplitL "ToξPc R". {
        iNext. iIntros "A".
        iMod (bi.later_exist_except_0 with "A") as (x1 d1 g1) "(>⧖2 & ζPc & Gho2 & >Pt2)".
        iCombine "Gho2 Pt2 ⧖2" as "GhoPt2".
        iMod ("R" with "GhoPt2") as (d2 g2) "[Gho1 [Pt1 ⧖1]]".
        iModIntro. iNext. iFrame "Gho1". iFrame "Pt1". iFrame "⧖1". 
        iApply "ToξPc".
        iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
        iDestruct (proph_eqz_constr ((!ₛ) f) with "Eqz") as "Eqz".
        iApply (proph_eqz_eq with "Eqz").
        + done.
        + fun_ext. intros x0. simpl. rewrite syn_type_morphism_commutes. done.
     } {
        iFrame "ζPc". iFrame "Gho". iFrame "Pt". iFrame "⧖".
     }
  Qed.
  
  (* Verus: probably not needed *)
  Lemma split_mt_uniq_bor l' P Φ Ψ :
    (l' ↦∗: (λ vl, P ∗ [loc[l] := vl]
      ∃(d: nat) (ξi: positive), ⌜Ψ d ξi⌝ ∗ Φ l d ξi)) ⊣⊢
    P ∗ ∃(l: loc) d ξi, ⌜Ψ d ξi⌝ ∗ l' ↦ #l ∗ Φ l d ξi.
  Proof.
    iSplit.
    - iDestruct 1 as ([|[[]|][]]) "(↦ &$& big)"=>//. iDestruct "big" as (???) "?".
      iExists _, _, _. rewrite heap_mapsto_vec_singleton. by iFrame.
    - iIntros "($&%&%&%&%& ↦ &?)". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "↦". iExists _, _. by iFrame.
  Qed.
  
  (* Similar to [†κ] but we can apply the basically_dead_incl rule immediately instead of
     performing an update.
     TODO should this have been the definition of [†κ'] to begin with?
     It might simplify a lot but has the disadvantage of not being timeless. *)
  Definition basically_dead (κ: lft) : iProp Σ := ∃ κ' , κ ⊑ κ' ∗ [†κ'].
  
  Definition basically_dead_incl κ κ' :
    κ' ⊑ κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl bd". iDestruct "bd" as (κ'') "[#Incl2 #Dead]".
    iExists κ''. iFrame "Dead". iApply (guards_transitive with "Incl Incl2").
  Qed.

  Lemma guard_inner_from_guard_uniq_body {𝔄} (ty: type 𝔄) x ξi d g ξidx κ tid l G n :
      llft_ctx -∗
      uniq_body_pers_component ty x ξi d g ξidx κ tid l -∗
      (G &&{↑NllftG; n}&&> uniq_body ty x ξi d g ξidx κ tid l) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      (G &&{↑NllftG; n+1}&&> ((ty.(ty_gho) x d g tid) ∗ l #↦!∗ ty.(ty_phys) x tid)).
  Proof.
    iIntros "LFT #Bor #Guniq #Gk". unfold uniq_body.
    iDestruct (guards_weaken_rhs_sep_l with "Guniq") as "Gvo".
    iDestruct (guards_weaken_rhs_sep_r with "Guniq") as "Guniq2".
    iDestruct (guards_weaken_rhs_sep_r with "Guniq2") as "#G2".
    iDestruct (guards_weaken_rhs_sep_l with "G2") as "Gtok".
    iClear "G2". iClear "Guniq". iClear "Guniq2".
    iDestruct (llftl_idx_bor_guard' with "LFT Bor [] Gtok") as "Ginner".
      { leaf_goal laters to 0. { lia. } iFrame "Gk". }
    iDestruct (guards_weaken_rhs_sep_r with "Ginner") as "Ginner".
    iDestruct (guards_later_absorb_1 with "Ginner") as "Ginner".
    iDestruct (guards_exist_eq x d g _ _ _ _ _ _ (n+1) with "Gvo Ginner") as "G".
     - intros x0 d0 g0. iIntros "And".
        iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) with "[And]") as "%Heq".
        + iSplit. { iDestruct "And" as "[And _]". iFrame "And". }
          iDestruct "And" as "[_ (? & T & ?)]". iFrame "T".
        + iPureIntro. destruct Heq as [Heq1 Heq2]. inversion Heq2. intuition.
     - lia. - lia.
     - iApply (guards_transitive_left with "G []"). leaf_by_sep.
        iIntros "(A & B & C & D)". iFrame. iIntros. done.
  Qed.
  
  Lemma uniq_body_mono_upd {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d g d' g': nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) E G :
    Timeless G →
    ↑Nllft ∪ ↑uniqN ⊆ E →
    d ≤ d' →
    g ≤ g' →
    llft_ctx -∗
    uniq_ctx -∗
    ⧖(S d' `max` g') -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗ 
    G ∗ uniq_body ty x ξi d' g' idx κ tid l.
  Proof.
    iIntros (Gtimeless Hmask Hle1 Hle2) "LFT UNIQ #⧖ #guards G UniqBody".
    iDestruct "UniqBody" as "(ξVo & £saved & ξTok & #ξBor)".
    iMod (llftl_bor_idx_acc_guarded with "LFT ξBor ξTok guards G") as "[Inner Back]";
        first by solve_ndisj.
        
    iMod (bi.later_exist_except_0 with "Inner") as (x'' d'' g'') "(⧖1 & ξPc & Gho & Phys)".
    iMod (uniq_strip_later with "ξVo ξPc") as "(%agree0 & %agree1 & ξVo & ξPc)".
    inversion agree1. subst x''. subst d''. subst g''.
    
    iMod (uniq_update (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) x _ (d', g') with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; first by solve_ndisj.
    iDestruct ("Back" with "[Gho Phys ξPc]") as "B".
      { iFrame. iFrame "⧖". iDestruct (ty_gho_depth_mono with "Gho") as "[$ _]"; trivial. }
    iMod (fupd_mask_mono with "B") as "[idx G]"; first by set_solver.
    iModIntro. iFrame. iFrame "ξBor".
  Qed.
End uniq_util.
