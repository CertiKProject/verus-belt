From lrust.typing Require Export uniq_bor shr_bor own uniq_util.
From lrust.typing Require Import lft_contexts type_context programs programs_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeG Σ}.
  
  Lemma type_uniqbor_instr {𝔄} E L I p n (ty: type 𝔄) κ :
    lctx_lft_alive E L κ →
    elctx_sat E L (ty_outlives_E ty κ) →
    typed_instr E L I
        +[p ◁ own_ptr n ty]
        UniqBor
        (const +[p ◁ &uniq{κ} ty; p ◁{κ} blocked_type_ctor _ (own_ptr n ty)])
      (λ post '-[a], λ mask π, ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (at_locₛ 𝔄))),
        of_cloc (uniq_bor_loc m) = a.1 →
        uniq_bor_current m = a.2 →
        (blockedπ b π).2 = (vπ m π).2 →
        (blockedπ b π).1 = a.1 →
        post -[m; b] mask π).
  Proof.
    intros Alv Out.
    apply typed_instr_of_skip.
    iIntros (x v d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ E L $ #P own #Obs #⧖ ⧗ ⧗' £".
    destruct x as [l x].
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#?".
    iDestruct "own" as "[gho %phys]". 
    destruct d as [|d']. { done. }
    iDestruct "gho" as "(pt & freeable & gho)".
    iDestruct (ty_gho_pers_impl _ ty with "gho") as "#Pers".
    iMod (alloc_uniq_body _ _ d' (S d') κ _ (l, repeat [] (length (ty_phys ty x tid))) with "LFT PROPH UNIQ [⧖] gho [pt] ⧗") as (ξi ζi idx) "[UniqBody [#Obsξζ Back]]".
      { set_solver. }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      { rewrite <- heap_cloc_mapsto_fancy_empty. iFrame "pt". }
    set ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi.
    set ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l, x))) ζi.
    iModIntro.
    iExists -[
      ((l, repeat [] (length (ty_phys ty x tid))), x, ξi, d', S d', idx);
      ((l, x), ζi, ζi)
    ].
    iFrame "L".
    unfold tctx_interp, tctx_elt_interp.
    iSplit. {
      iSplitL "UniqBody". {
        iExists v, (S (S d')). iFrame "#". iFrame.
        iSplit; last by done. iSplit; first by iPureIntro; lia.
        rewrite <- heap_cloc_mapsto_empty. iApply guards_true.
      }
      unfold blocked_type_elim. iSplit; [|done].
      iExists v. iFrame "#". iIntros "†κ".
      iDestruct ("Back" with "†κ") as "Back". iMod (fupd_mask_mono with "Back") as "Back". { set_solver. }
      iMod (bi.later_exist_except_0 with "Back") as (x'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (d'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (g'') "Back".
      iDestruct "Back" as "(>⧖'' & pc & gho & >pt)".
      iModIntro. iExists (l, x''), (S d'' `max` g'').
      destruct (S d'' `max` g'') as [|d1] eqn:Hd1; first by lia.
      iFrame.
      iSplitL "pc". {
        iDestruct (proph_ctrl_eqz with "PROPH pc") as "Eqz".
        iNext.
        iApply proph_eqz_modify.
         2: { iApply (proph_eqz_constr (λ t, (l, t)) with "Eqz"). }
        iApply (proph_obs_impl with "Obsξζ"). intros π Ha.
        simpl. simpl in Ha. rewrite <- Ha.  trivial.
      }
      rewrite heap_cloc_mapsto_fancy_empty. repeat rewrite ty_size_eq. iFrame.
      iSplitL. { iDestruct (ty_gho_depth_mono with "gho") as "[gho _]"; last by iFrame "gho". { lia. } { lia. } }
      done.
    }
    iCombine "Obs Obsξζ" as "Obs1".
    iApply (proph_obs_impl with "Obs1"). intros π [Hm Hk]. apply Hm; trivial.
     - simpl. rewrite Hk. trivial.
     - simpl. rewrite Hk. trivial.
  Qed.

  (* VerusBelt: we needed to make UniqBor an instruction so we can generate credits. This
     was the old lemma: *)
  (*Lemma tctx_borrow {𝔄} E L p n (ty: type 𝔄) κ:
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_incl E L +[p ◁ own_ptr n ty] +[p ◁ &uniq{κ} ty; p ◁{κ} blocked_type_ctor _ (own_ptr n ty)]
      (λ post '-[a], λ π, ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ 𝔄)),
        uniq_ref_loc m = a.1 →
        uniq_ref_current m = a.2 →
        vπ b π = (vπ m π).2 →
        post -[m; b] π).
  *)

  (*Lemma tctx_extract_hasty_borrow {𝔄 𝔅 ℭl} E L p n
      (ty : type 𝔄) (ty' : type 𝔅) κ (T : tctx ℭl) f:
    subtype E L ty' ty f →
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_extract_elt E L (p ◁ &uniq{κ}ty) (p ◁ own_ptr n ty' +:: T)
      (p ◁{κ} blocked_type_ctor _ (own_ptr n ty) +:: T)
      (λ post '(b -:: bs), ∀b': 𝔄, post ((f b, b') -:: b' -:: bs)).
  Proof.
    intros. eapply tctx_incl_impl.
    - eapply tctx_incl_trans; [by eapply subtype_tctx_incl, own_subtype|].
      eapply (tctx_incl_frame_r +[_] +[_; _]). by eapply tctx_borrow.
    - done.
    - intros ??? [??]. by apply forall_proper.
  Qed.*)

  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[m], λ mask π, (vπ m π).1 = (vπ m π).2 -> post -[(uniq_bor_loc m, uniq_bor_current m)] mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_skip.
    intros x v d tid post mask iκs. iIntros "#LFT #TIME #PROPH #UNIQ #E L $ #P Own #Obs ⧖ ⧗ ⧗' £".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Own" as "[[#Incl [%Ineqs [UniqBody [#PtBase #Pers]]]] #Phys]".
    
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Ghalf Alv") as "G2".
      iDestruct (guards_transitive with "G2 Incl'") as "G3".
      leaf_open "G3" with "H1" as "[Alive _]". { set_solver. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l with "LFT PROPH UNIQ TIME Incl E Ghalf H1 UniqBody") as "(#Obs2 & H1 & #ShrGuard)". { trivial. } { set_solver. }
    iDestruct ("Halfback" with "H1 H2") as "Halfback'". iMod (fupd_mask_mono with "Halfback'") as "L". { set_solver. }
    iModIntro. iExists -[(l, x0)]. iFrame.
    iSplit. {
      iExists v. iSplit. { done. } iSplit; last by done.
      iSplit. {
        iApply guard_cloc_combine_fancy.
         - leaf_goal laters to (d + 1); first by lia. iFrame "PtBase".
         - leaf_goal laters to 1. { lia. } iApply (guards_weaken_rhs_sep_r with "ShrGuard").
      }
      iSplit. { leaf_goal laters to 1. { lia. } iApply (guards_transitive_left with "ShrGuard []").
        leaf_by_sep. iIntros "[G pt]".
        iDestruct (ty_gho_depth_mono _ _ _ d (S d) with "G") as "[G back]". { lia. } { lia. }
        iFrame "G". iIntros "G". iFrame. iApply "back". iFrame.
      }
      iNext. iApply (ty_gho_pers_depth_mono _ _ _ d (S d)); last by iFrame "Pers".
      { lia. } { lia. }
    }
    iCombine "Obs Obs2" as "Obs3".
    iApply proph_obs_impl; [|done]=>/= π.
    intros [Himpl1 Heq]. apply Himpl1. symmetry. apply Heq.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
    trx tr e E L I (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L I C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L I C T (Share;; e) (trx ∘
      (λ post '(m -:: bl), λ mask π, (vπ m π).1 = (vπ m π).2 -> tr post ((uniq_bor_loc m, uniq_bor_current m) -:: bl) mask π)
      )%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.
  
  Lemma tctx_reborrow_uniq {𝔄} E L I p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    typed_instr E L I
        +[p ◁ &uniq{κ} ty]
        ReBor
        (const +[p ◁ &uniq{κ'} ty; p ◁{κ'} blocked_type_ctor _ (&uniq{κ} ty)])
        (λ post '-[bor], λ mask π, ∀ (re_bor: ~~ (uniq_borₛ 𝔄)) (b: ~~(blockedₛ (uniq_borₛ 𝔄))),
            uniq_bor_loc re_bor = uniq_bor_loc bor →
            uniq_bor_current re_bor = uniq_bor_current bor →
            (blockedπ b π) = (uniq_bor_future re_bor π, uniq_bor_future bor π) →
            post -[re_bor; b] mask π).
  Proof.
    intros LftIncl.
    apply typed_instr_of_skip.
    iIntros (x v d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ E L $ #P own Obs #⧖ ⧗ ⧗' £".
    iDestruct (LftIncl with "L E") as "#κ'⊑κ".
    iDestruct "own" as "[gho %phys]". 
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "gho" as "(#Incl2 & %Hineq & UniqBody & #PtBase & #InnerPers)".
    iDestruct "UniqBody" as "(ξVo & ⧗'' & Tok & ξBor)".
    
    iMod (uniq_intro x0 (vπ x0) (d', g') with "PROPH UNIQ") as (ζi) "(ζVo & ζPc)"; [done|].
    set ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi.
    set ζ := PrVar _ ζi.
    
    (*iMod (@uniq_intro _ _ _ _ (uniq_borₛ 𝔄) (l, x0, ξi, d', g', idx) (@vπ (uniq_borₛ 𝔄) (l, x0, ξi, d', g', idx)) (d, d) with "PROPH UNIQ") as (ξζi) "[ξζVo ξζPc]". { set_solver. }*)
    
    iDestruct (guards_transitive with "κ'⊑κ Incl2") as "Inclκ'".
     
    iDestruct "InnerPers" as "[Dead|InnerPers]". {
        (* case where κ is already dead *)
        iDestruct "Dead" as (κ3) "[#Incl3 Dead3]".
        iMod (llftl_incl_dead_implies_dead with "LFT Incl3 Dead3") as "#†κ". { set_solver. }
        iMod (llftl_incl_dead_implies_dead with "LFT κ'⊑κ †κ") as "#†κ'". { set_solver. }
        
        iMod (llftl_bor_fake with "LFT †κ'") as "FakeBor". { set_solver. }
        iDestruct (llftl_bor_idx with "FakeBor") as (fake_idx) "[FakeBor FakeTok]".
        
        iModIntro. 
        iExists -[(l, x0, ζi, d', g', fake_idx);
            ((l, x0, ζi, d', g', idx), ζi, ξi)
        ].
        iFrame "L". 
        
        unfold tctx_interp, tctx_elt_interp.
        iSplitL "⧗ ⧗' ⧗'' FakeBor ζVo ζPc FakeTok ξVo ξBor Tok".
        {
          iSplitL "⧗ FakeBor ζVo FakeTok". {
            iExists v. iExists (S d). iFrame "P". iFrame "⧖".
            iSplit. {
              iSplit. { iFrame "Inclκ'". }
              iSplit. { iPureIntro. lia. }
              iSplit. { iFrame "FakeTok". iFrame " ζVo". iFrame "⧗". iApply "FakeBor". }
              iSplit. {
                leaf_goal laters to (d + 1); first by lia.
                iApply (guards_transitive_right with "κ'⊑κ PtBase").
              }
              iLeft. iExists κ. iFrame "#".
            }
            done.
          }
          {
            iSplit; last by done.
            iExists v. iSplit; first by done.
            iIntros "_". iModIntro.
            iExists (l, x0, ξi, d', g', idx), (S d).
            iSplitL "ζPc". {
              iNext. iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
              iApply (proph_eqz_prod with "[Eqz]").
                - iFrame "Eqz".
                - iApply proph_eqz_refl.
            }
            iFrame "⧖".
            iFrame. iSplit; last by done.
              iSplit. { iFrame "#". } iSplit. { iPureIntro. lia. }
              iSplit. {
                leaf_goal laters to (d + 1); first by lia. iFrame "PtBase".
              }
              iLeft. iExists κ. iFrame "#". iApply guards_refl.
          }
        }
        iApply (proph_obs_impl with "Obs") => /= π.
        intros Ha. apply Ha; done.
    }
    
    (* normal case *)
    
    iDestruct (llftl_bor_idx_to_full with "ξBor Tok") as "ξBor".
    iMod (llftl_reborrow with "LFT κ'⊑κ ξBor") as "[ξBor ToξBor]". { set_solver. }
    
    iMod (llftl_borrow _ κ' (∃x' d' g', .VO[ξ] x' (d', g') ∗ ⧖(S d' `max` g') ∗ .PC[ζ] x' (vπ x') (d', g'))%I with "LFT [⧖ ξVo ζPc]") as "[ζBor ToζBig]"; [done| |].
      { iFrame. iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (llftl_sep_join with "LFT ξBor ζBor") as "Bor"; [done|].
    
    iAssert (|={↑Nllft}=> &{κ'} (∃ x' (d'0 g'0 : nat),
       ⧖(S d'0 `max` g'0) ∗ .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi] x' (vπ x') (d'0, g'0) ∗
       ty_gho ty x' d'0 g'0 tid ∗ l #↦!∗ ty_phys ty x' tid))%I with "[Bor]" as "Bor". {
      iMod (llftl_bor_acc_atomic with "LFT Bor") as "[[[H1 H2] Back']|[Dead Back']]".
      - 
        iMod (bi.later_exist_except_0 with "H1") as (x1) "H1".
        iMod (bi.later_exist_except_0 with "H1") as (d1) "H1".
        iMod (bi.later_exist_except_0 with "H1") as (g1) "(#T1 & Pc1 & Gho1 & Pt1)".
        iMod (bi.later_exist_except_0 with "H2") as (x2) "H2".
        iMod (bi.later_exist_except_0 with "H2") as (d2) "H2".
        iMod (bi.later_exist_except_0 with "H2") as (g2) "(Vo2 & #T2 & Pc2)".
        iDestruct (uniq_agree with "Vo2 Pc1") as "#>[%agree1 %agree2]". inversion agree2.
          subst x2. subst d2. subst g2.
        iApply ("Back'" with "[Vo2 Pc1 T2] [T1 Pc2 Gho1 Pt1]").
        + iNext. iIntros "[H3 DeadK']".
            iMod (bi.later_exist_except_0 with "H3") as (x3) "H3".
            iMod (bi.later_exist_except_0 with "H3") as (d3) "H3".
            iMod (bi.later_exist_except_0 with "H3") as (g3) "(#T3 & Pc3 & Gho3)".
            iMod (uniq_update ξ x3 (vπ x3) (d3, g3) with "UNIQ Vo2 Pc1") as "[Vo4 Pc4]".
            { solve_ndisj. }
            iModIntro. iNext. iFrame. iFrame "#".
        + iExists x1, d1, g1. iFrame. iFrame "#".
     - iMod "Back'". iApply (llftl_bor_fake with "LFT Dead"). { set_solver. } 
    }
    iMod (fupd_mask_mono with "Bor") as "Bor". { set_solver. }
    
    iDestruct (llftl_bor_idx with "Bor") as (ζidx) "[#Bor Tok]".
    
    iModIntro. iExists -[(l, x0, ζi, d', g', ζidx); 
        ((l, x0, ζi, d', g', idx), ζi, ξi)
    ].
    iFrame "L". 
    unfold tctx_interp, tctx_elt_interp.
    iSplit. {
      iSplitL "Tok ζVo ⧗'". {
        iExists v, (S d). iFrame "P". iFrame "⧖". unfold ty_own.
        iSplit. {
          iSplit. { iApply (guards_transitive with "κ'⊑κ Incl2"). }
          iSplit. { iPureIntro. lia. }
          iSplit. { iFrame "Tok". iFrame "ζVo". iFrame "⧗'". iFrame "Bor". }
          iFrame "InnerPers".
          leaf_goal laters to (d + 1); first by lia.
          iApply (guards_transitive_right with "κ'⊑κ PtBase").
        } {
          iPureIntro. apply phys.
        }
      } {
        iSplit; last by done. iExists v. iFrame "P". iIntros "#†κ".
        iDestruct ("ToξBor" with "†κ") as "B". iMod (fupd_mask_mono with "B") as "ξBor".
          { set_solver. }
        iDestruct ("ToζBig" with "†κ") as "B".
        iMod (fupd_mask_mono with "B") as "Back". { set_solver. }
        iMod (bi.later_exist_except_0 with "Back") as (x'') "Back".
        iMod (bi.later_exist_except_0 with "Back") as (d'') "Back".
        iMod (bi.later_exist_except_0 with "Back") as (g'') "(>Vo & >#⧖'' & Pc)".
        
        iMod (llftl_bor_pers_from_wand2 _ _ _ (ty_gho_pers ty x'' d'' g'' tid)%I with "LFT ξBor [] Vo") as "[ξBor [Pers'' Vo]]". { set_solver. } { iIntros "Vo". iDestruct 1 as (x''' d''' g''') "(_ & pc''' & gho''' & _)".
          iDestruct (uniq_agree with "Vo pc'''") as "[%Agree %Agree2]". inversion Agree2.
          subst x'''. subst d'''. subst g'''.
          iApply (ty_gho_pers_impl with "gho'''").
        }
        
        iDestruct (llftl_bor_idx with "ξBor") as (idx'') "[ξBor Tok]".
        iModIntro. iExists (l, x'', ξi, d'', g'', idx'').
        iExists (d `max` S d'' `max` g'').
        iSplitL "Pc". {
          iNext. iDestruct (proph_ctrl_eqz with "PROPH Pc") as "Eqz".
          iApply (proph_eqz_prod with "[Eqz]").
            - iFrame "Eqz".
            - unfold "∘". simpl.
              rewrite (proof_irrel (to_inh_syn_type (vπ x'' inhabitant)) (prval_to_inh (vπ x0))).
              iApply proph_eqz_refl.
        } {
          iCombine "⧖'' ⧖" as "⧖max".
          iSplit. { iApply (persistent_time_receipt_mono with "⧖max"). lia. }
          iFrame "⧗''".
          iSplit; last by done. iSplit. { iFrame "Incl2". }
          iSplit. { iPureIntro. nia. }
          iSplit. { iFrame "Tok".
            rewrite (proof_irrel (prval_to_inh (vπ x'')) (prval_to_inh (vπ x0))).
            iFrame "Vo". iFrame "ξBor". iFrame "⧗".
          }
          iSplit. { leaf_goal laters to (d + 1); first by lia. iFrame "PtBase". }
          iDestruct "Pers''" as "[Pers''|Deadκ]". { iRight. iFrame "Pers''". }
            { iLeft. iExists κ. iFrame "Deadκ". iApply guards_refl. }
        }
      }
    }
        
    iApply (proph_obs_impl with "Obs") => /= π.
    intros Ha. apply Ha; done.
  Qed.
    

(* also can't use this one, we need to take a step
  Lemma tctx_reborrow_uniq {𝔄} E L p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L +[p ◁ &uniq{κ} ty] +[p ◁ &uniq{κ'} ty; p ◁{κ'} blocked_type_ctor _ (&uniq{κ} ty)]
      (λ post '-[bor], λ π, ∀ (re_bor: ~~ (uniq_borₛ 𝔄)),
          uniq_bor_loc re_bor = uniq_bor_loc bor →
          uniq_bor_current re_bor = uniq_bor_current bor →
          post -[re_bor; (λ π, (uniq_bor_future re_bor π, uniq_bor_future bor π))] π).
  *)

  (*Lemma tctx_extract_hasty_reborrow {𝔄 𝔅l} (ty ty': type 𝔄) κ κ' (T: tctx 𝔅l) E L p :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    tctx_extract_elt E L (p ◁ &uniq{κ'} ty) (p ◁ &uniq{κ} ty' +:: T)
      (p ◁{κ'} &uniq{κ} ty' +:: T) (λ post '((a, a') -:: bl),
        ∀a'': 𝔄, post ((a, a'') -:: (a'', a') -:: bl)).
  Proof.
    move=> ??. eapply tctx_incl_impl.
    - apply (tctx_incl_frame_r +[_] +[_;_]).
      eapply tctx_incl_trans; [by apply tctx_reborrow_uniq|].
      by apply subtype_tctx_incl, uniq_subtype, eqtype_symm.
    - by move=>/= ?[[??]?].
    - intros ??? [[??]?]. by apply forall_proper.
  Qed.*)
  

  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I
        +[p ◁ &uniq{κ} (own_ptr n ty)]
        (!p)
        (&uniq{κ} ty)
        (λ post '-[bor], λ mask π, ∀ bor',
            uniq_bor_current bor' = snd (uniq_bor_current bor) →
            uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
            post bor' mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_memload_with_cumutime1.
    intros x v d tid post mask.
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    destruct x0 as [l1 x1].
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs ⧗ #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "own" as "[[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]] %Phys]".
    inversion Phys. subst v.
    
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iDestruct "UniqBody" as "(ξVo & £saved & ξTok & #ξBor)".
    (*
    iDestruct (llftl_bor_idx_to_full with "ξBor Tok") as "ξBor".
    iMod (llftl_bor_freeze with "LFT ξBor") as (x2) "ξBor". { solve_ndisj. }
      Unshelve. 2: { split. apply (l1, x1). }
    iMod (llftl_bor_freeze with "LFT ξBor") as (d2) "ξBor". { solve_ndisj. }
    iMod (llftl_bor_freeze with "LFT ξBor") as (g2) "ξBor". { solve_ndisj. }
    iDestruct (llftl_bor_idx with "ξBor") as (ξidx) "[#ξBor ξTok]".*)
    
    set ξ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l1, x1))) ξi.
    iModIntro. iExists l, l1, (llctx_interp L ∗ .VO[ξ] (l1, x1) (d', g') ∗ idx_bor_tok ξidx)%I.
    iSplit; first by done.
    iFrame "L". iFrame "ξVo". iFrame "ξTok".
    iSplit. {
      iDestruct (llftl_idx_bor_guard' _ _ _ (llctx_interp L ∗ .VO[ξ] (l1, x1) (d', g') ∗ idx_bor_tok ξidx)%I with "LFT ξBor [] []") as "Gexists".
        - iApply (guards_weaken_lhs_sep_l with "Alv").
        - leaf_by_sep. iIntros "(?&?&?)". iFrame. iIntros. done.
        - iDestruct (uniq_guards_get_guards_pt with "Gexists") as "G2".
          iApply guard_cloc_combine.
           + iApply (guards_transitive_right with "[] PtBase").
             iApply (guards_transitive with "[] Alv").
             leaf_by_sep; iIntros "(?&?&?)"; iFrame; iIntros; done.
           + leaf_goal laters to 1. { lia. }
             rewrite <- heap_complete_mapsto_fancy_fmap_eq.
             iFrame "G2".
    }
    
    iIntros "[L [ξVo ξTok]]".
    
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    iDestruct "£" as "[£ [£1' £1]]".
    iMod (uniq_body_transform (own_ptr n ty) ty (l1, x1) x1 d' g' ξi ξidx κ tid l (l1, repeat [] (length (ty_phys ty x1 tid))) _ _ (pair_with_locₛ l1) with "LFT PROPH UNIQ [⧗ £1'] HguardsK H1 [ξTok ξVo £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
     { iIntros "[gho pt]".  iMod (lc_fupd_elim_later with "£1' gho") as "gho".
       destruct d'. { done. } iDestruct "gho" as "[phys [free gho]]".
       iModIntro. iDestruct (ty_gho_depth_mono _ _ _ (S d') g' with "gho") as "[gho _]". { lia. } { lia. }
       iFrame "gho".
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame "phys". iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
       iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖2") as "⧖2'". { solve_ndisj. }
       iModIntro. iFrame "pt". iExists (S d2), g2.
       replace (length (ty_phys ty x1 tid)) with (length (ty_phys ty x2 tid)).
        2: { repeat rewrite ty_size_eq. done. }
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
       
     }
     { iFrame. iFrame "ξBor". }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
    iModIntro. iExists ((l1, repeat [] (length (ty_phys ty x1 tid))), x1, ζi, d', g', ζidx).
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. {
      iSplit. {
        iSplit. { iPureIntro. lia. }
        iSplit. { rewrite <- heap_cloc_mapsto_empty. iApply guards_true. }
        iRight. destruct d'; [done|]. iNext.
        iApply (ty_gho_pers_depth_mono _ d' g' with "Pers'"). { lia. } { lia. }
      }
      iPureIntro. done.
    }
    iCombine "Obs Obs2" as "Obs3".
    iApply (proph_obs_impl with "Obs3"). intros π [Ha Hb]. apply Ha; intuition.
      - unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      - unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
  Qed.
    
  Lemma type_deref_uniq_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '(bor -:: bl), λ mask π, forall bor',
            uniq_bor_current bor' = snd (uniq_bor_current bor) →
            uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
            tr post (bor' -:: bl) mask π)
    ).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_uniq_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed. 

  Lemma type_deref_shr_own_instr {𝔅} {E L I} κ p n (ty : type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I
      +[p ◁ &shr{κ} (own_ptr n ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l1, (l2, a))], λ mask π, ∀ l2', of_cloc l2' = l2 → post (l2', a) mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_memload.
    intros x v d tid post mask.
    destruct x as [l1 [l2 x2]].
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "£" as "[£ [£1 £1']]".
    
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#Gp [#Ggho #pers]]".
    
    iModIntro. iExists l1, l2, (llctx_interp L).
    inversion phys. subst v.
    iSplit; first by done.
    iFrame "L".
    iSplit. {
      rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      iApply (guards_transitive_right with "Alv Gp").
    }
    iIntros "L".
    iModIntro.
    iExists ((l2, repeat [] (length (ty_phys ty x2 tid))), x2). iFrame "L".
    iDestruct (proph_obs_impl with "Obs") as "$". { intros π Ha. apply Ha. done. }
    iSplit; last by done.
    iSplit. {
       leaf_goal laters to (S d' + 1). { lia. }
       iApply (guards_transitive_left with "Ggho []").
       leaf_by_sep. iIntros "g". destruct d' as [|d'']; first by done. simpl.
       rewrite <- heap_mapsto_cells_fancy_empty.
       iDestruct "g" as "[pt [free gho]]". iFrame. iIntros. done.
    }
    iSplit. {
       leaf_goal laters to ((S d' + 1) + 1). { lia. }
       iApply (guards_transitive_additive _ _ _ _ _ 1 with "Ggho []").
       leaf_by_sep. iIntros "g". destruct d' as [|d'']; first by done.
          iDestruct "g" as "[pt [free gho]]". iNext.
          iDestruct (ty_gho_depth_mono with "gho") as "[gho back]"; last first.
          - iSplitL "gho". { iFrame "gho". }
            iIntros "A". iSpecialize ("back" with "A"). iFrame.
          - lia. - lia.
    }
    rewrite (bi.laterN_add (S (S d'))). iNext.
    destruct d' as [|d'']; first by done.
    iApply (ty_gho_pers_depth_mono ty with "pers"). { lia. } { lia. }
  Qed.

  Lemma type_deref_shr_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E I L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '((l1, (l2, a)) -:: bl), λ mask π, forall l2', of_cloc l2' = l2 → tr post ((l2', a) -:: bl) mask π)
    ).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_shr_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.
 
  Lemma type_deref_uniq_uniq_instr {𝔄 E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I +[p ◁ &uniq{κ} (&uniq{κ'}ty)] (!p) (&uniq{κ} ty)
      (λ post '-[bor], λ mask π, ∀ bor',
        uniq_bor_loc bor'      = uniq_bor_loc (uniq_bor_current bor) →
        uniq_bor_current bor'  = uniq_bor_current (uniq_bor_current bor) →
        uniq_bor_future bor' π = fst (uniq_bor_future bor π) →
        uniq_bor_future (uniq_bor_current bor) π = snd (uniq_bor_future bor π) →
        post bor' mask π).
  Proof.
    intros Alv. apply typed_instr_of_memload_with_cumutime1.
    intros x v d tid post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs ⧗ #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "£" as "[£ [£1 £1']]".
    
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HalfGuardsK".
    
    destruct x as [[[[[l x0] ξi] d0] g0] ξidx].
    destruct x0 as [[[[[l1 x1] ωi] d1] g1] ωidx].
    iDestruct "own" as "[[#Incl [%Ineqs [UniqBody [#PtBase #Pers]]]] %Phys]".
    iDestruct "UniqBody" as "(ξVo & ⧗' & ξTok & ξBor)".
     
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "HalfGuardsK Incl'") as "G2".
      leaf_open "G2" with "H1" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iDestruct (llftl_bor_idx_to_full with "ξBor ξTok") as "ξBor".
    iMod (llftl_bor_acc_guarded with "LFT ξBor HalfGuardsK H1") as "[big Hclose']"; first by solve_ndisj.
    
    iMod (bi.later_exist_except_0 with "big") as (x'' d'' g'') "(>#⧖' & ξPc & Gho' & >Pt')".
    iMod (uniq_strip_later with "ξVo ξPc") as "(%agree1 & %agree2 & ξVo & ξPc)".
    inversion agree2. subst x''. subst d''. subst g''.
    iMod (lc_fupd_elim_later with "£1 Gho'") as "Gho'".
    
    iAssert (κ ⊑ κ')%I as "#Hκ⊑κ'". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_l.
    }
    iAssert (fractional.half γ &&{ ↑NllftG }&&> @[κ'])%I as "#HalfGuardsK'". {
      iApply (guards_transitive with "HalfGuardsK Hκ⊑κ'").
    }
    
    iDestruct "Gho'" as "[#Incl2 [%Ineqs2 [UniqBody2 [#PtBase2 #Pers2]]]]".
    iMod (uniq_body_mono_upd _ _ _ _ _ d1 g0 with "LFT UNIQ [] HalfGuardsK' H2 UniqBody2") as "[H2 UniqBody2]".
      { solve_ndisj. } { lia. } { lia. } { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
    iDestruct "UniqBody2" as "(ωVo & ⧗'' & ωTok & #ωBor)".
    
    set ξ := PrVar _ ξi. set ω := PrVar _ ωi.
    iMod (uniq_update ξ with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
    
    iDestruct ("Hclose'" $! (l #↦!∗ [FVal #(l1.1)] ∗
       (∃ x' d' g', .VO[ω] x' (d', g') ∗ .PC[ξ] (l1, x', ωi, d', g', ωidx) (@vπ (uniq_borₛ 𝔄) (l1, x', ωi, d', g', ωidx)) (S d', g') ∗ ⧖ (S (S d') `max` g') ∗ ⧗1 ∗ (@[κ'] &&{↑NllftG; g'+1}&&> l1 #↦∗_) ∗ (basically_dead κ' ∨ ▷ ty_gho_pers ty x' d' g' tid)) ∗
       idx_bor_tok ωidx)%I with "[ωTok Pt' ωVo ξPc ⧗'']") as "A".
    { iSplitR.
      - iNext. iIntros "A". iModIntro. iNext. iDestruct "A" as "[pt [A tok]]".
        iDestruct "A" as (x' d' g') "[Vo [Pc [⧖2 [⧗2 [ptbase pers]]]]]".
        iExists (l1, x', ωi, d', g', ωidx), (S d'), g'.
        iFrame "Pc". simpl.
        iFrame "pt". iFrame "tok".
        iSplit. { iApply (persistent_time_receipt_mono with "⧖2"). lia. }
        iSplit. { iFrame "Incl2". }
        iSplit. { iPureIntro. lia. }
        rewrite (proof_irrel (prval_to_inh _) (prval_to_inh (vπ x1))).
        iFrame "Vo". iFrame "ωBor". iFrame "⧗2".
        (*iDestruct "pers" as "[?|?]". { iLeft. iFrame. } iRight. iNext. iFrame.*)
        iFrame "ptbase". iFrame "pers".
     - iNext.
        iFrame "Pt'".
        iFrame "ωTok". iExists x1, d1, g0. iFrame "ωVo". iFrame "ξPc".
        iSplit. { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
        iFrame "⧗''". iFrame "PtBase2".
        iDestruct "Pers2" as "[?|?]".
        { iLeft. iFrame "#". } iRight.
        iApply (ty_gho_pers_depth_mono); last by iFrame "#". { lia. } { lia. }
   }
   
   iDestruct (lc_step_fupd_elim_later with "£1' A") as "A".
   iMod (fupd_mask_mono with "A") as "[Hbor H1]". { solve_ndisj. }
   
    iMod (llftl_sep_split with "LFT Hbor") as "[H↦ Hbor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Hbor") as "[BorVoPc Hbor]"; [solve_ndisj|].
    iMod (llftl_idx_bor_unnest with "LFT ωBor Hbor") as "HBor"; [solve_ndisj|].
    iDestruct (llftl_bor_idx with "H↦") as (idxpt) "[#Bor↦ Tok↦]".
    
    inversion Phys. subst v.
    
    iModIntro. iExists l, (l1.1), (fractional.half γ ∗ idx_bor_tok idxpt)%I. iSplit; [done|].
    iFrame "H1". iFrame "Tok↦".
    iSplit. {
      iApply guard_cloc_combine.
      - iApply (guards_transitive_right with "[] PtBase").
        iApply guards_weaken_lhs_sep_l. done.
      - iApply guards_later_absorb_1.
        iApply guards_weaken_rhs_sep_r.
        rewrite <- heap_cloc_mapsto_fancy_fmap_eq.
        iApply (llftl_idx_bor_guard' with "LFT Bor↦ [] []"). {
            leaf_goal laters to 0; first by lia.
            iApply guards_weaken_lhs_sep_l. done.
        }
        iApply guards_weaken_sep_r. 
    }
    
    iIntros "[H1 Tok↦]".
    
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "#Hκ⊑rest". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_r.
    }
    iMod (llftl_sep_join with "LFT BorVoPc [HBor]") as "HBor"; first by solve_ndisj.
      { iApply (llftl_bor_shorten with "[] HBor").
        iApply llftl_incl_glb; [|iApply lft_incl_refl].
        iFrame "Hκ⊑κ'".
      }
      
    iMod (llftl_bor_acc_guarded with "LFT HBor HalfGuardsK H1") as "[[VoPc Hown] Hclose']"; first by solve_ndisj.
    iMod (bi.later_exist_except_0 with "VoPc") as (x'' d'' g'') "(ωVo & ξPc & ⧖3 & >£3 & pers3)".
    iMod (bi.later_exist_except_0 with "Hown") as (x''' d''' g''') "(#⧖4 & ωPc & gho & pt)".
    
    iMod (uniq_strip_later with "ξVo ξPc") as "(%agree3 & %agree4 & ξVo & ξPc)".
    inversion agree3. inversion agree4. subst x''. subst d''. subst g''.
    iMod (uniq_strip_later with "ωVo ωPc") as "(%agree5 & %agree6 & ωVo & ωPc)".
    inversion agree6. subst x'''. subst d'''. subst g'''.
    
    iMod (uniq_intro x1 (vπ x1) (d1, g0) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set ζ := PrVar _ ζi.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ω & ToωPc)".
    iMod (uniq_preresolve ξ [ζ; ω] (λ π, (π ζ, π ω)) with "UNIQ PROPH ξVo ξPc [$ζ $ω]")
      as "(Hobs & (ζ & ω &_) & Heqz)"; [done| |done|].
    { apply (proph_dep_prod [_] [_]); apply proph_dep_one. }
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iDestruct ("ToωPc" with "ω") as "ωPc".

    iDestruct ("Hclose'" $! (∃x' d' g', ⧖ (S d' `max` g') ∗ .PC[ζ] x' (vπ x') (d', g') ∗
      ty.(ty_gho) x' d' g' tid ∗ l1 #↦!∗ ty.(ty_phys) x' tid)%I
       with "[Heqz ωVo ωPc ⧗ ⧗' ζPc gho pt]"
      ) as "A".
    { iSplitL "Heqz ωVo ωPc ⧗ ⧗'". {
      iNext. iIntros "A".
      iMod (bi.later_exist_except_0 with "A") as (x'' d'' g'') "(>⧖'' & ζPc & Gho & Pt)".
      iMod (uniq_update with "UNIQ ωVo ωPc") as "[ωVo ωPc]". { solve_ndisj. }
      iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖''") as "#⧖21". { solve_ndisj. }
      iCombine "⧖21 ⧖4" as "⧖max".
      iDestruct (ty_gho_pers_impl with "Gho") as "#GhoPers".
      iModIntro. iSplitR "Gho ωPc Pt".
      - iNext. iExists x'', d'', (g0 `max` g''). iFrame "ωVo". iSplitL "Heqz ζPc".
        + iApply "Heqz".  iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
          iApply (proph_eqz_prod with "[Eqz] []").
          * unfold "∘". simpl. iApply "Eqz".
          * unfold "∘". simpl. 
            rewrite (proof_irrel (to_inh_syn_type _) (prval_to_inh (vπ x1))).
            iApply proph_eqz_refl.
        + iSplit. {
          iApply (persistent_time_receipt_mono with "⧖max"). lia.
         }
         iFrame "⧗'".
          iSplit. { iApply (lguards_weaken_later with "PtBase2"); lia. }
          iRight.
          iApply (ty_gho_pers_depth_mono with "GhoPers"); lia.
      - iExists x'', d'', (g0 `max` g'').
        iDestruct (ty_gho_depth_mono with "Gho") as "[$ _]". { lia. } { lia. }
        iFrame "ωPc". iFrame "Pt".
        iApply (persistent_time_receipt_mono with "⧖max"). lia.
     }
     iFrame. iFrame "⧖4".
   }
   
   iDestruct "Pers2" as "[Dead|Pers2]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "HalfGuardsK Hκ⊑κ'") as "G1".
      iDestruct (guards_transitive with "G1 Incl'") as "G2".
      leaf_open "G2" with "H2" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
   
   iMod (fupd_mask_mono with "A") as "[A H1]". { solve_ndisj. }
   iDestruct (llftl_bor_idx with "A") as (ζidx) "[#ζBor ζTok]".
   iDestruct ("Halfback" with "H1 H2") as "A".
   iMod (fupd_mask_mono with "A") as "L". { solve_ndisj. }
  
   
   iModIntro.
   iExists (l1, x1, ζi, d1, g0, ζidx).
   iFrame "L". iFrame.
   iSplit.
    - iSplit; last by done. iSplit; first by iFrame "#". iSplit; first by iPureIntro; lia.
      iFrame "ζBor".
      iSplit. {
        iApply (guards_transitive_right with "Hκ⊑κ' []").
        iApply (lguards_weaken_later with "PtBase2"). lia.
      }
      iRight. iApply (ty_gho_pers_depth_mono with "Pers2"); lia.
    - iCombine "Obs Hobs" as "Obs".
      iApply (proph_obs_impl with "Obs"). intros π [Ha Hb]. 
      apply Ha; trivial.
        + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
        + simpl. unfold uniq_bor_future. simpl.
          rewrite Hb. trivial.
   Qed.

  Lemma type_deref_uniq_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '(bor -:: bl), λ mask π, ∀ bor',
        uniq_bor_loc bor'      = uniq_bor_loc (uniq_bor_current bor) →
        uniq_bor_current bor'  = uniq_bor_current (uniq_bor_current bor) →
        uniq_bor_future bor' π = fst (uniq_bor_future bor π) →
        uniq_bor_future (uniq_bor_current bor) π = snd (uniq_bor_future bor π) →
        tr post (bor' -:: bl) mask π))%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    by iApply type_let; [by eapply type_deref_uniq_uniq_instr|solve_typing| |done].
  Qed.

  Lemma type_deref_shr_uniq_instr {𝔄} {E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    lctx_lft_incl E L κ κ' →
    typed_instr_ty E L I +[p ◁ &shr{κ} (&uniq{κ'} ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l, bor)], post (uniq_bor_loc bor, uniq_bor_current bor)).
  Proof.
    intros Alv Incl. apply typed_instr_of_memload.
    intros x v d tid post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (Incl with "L E") as "#Incl".
    iDestruct (guards_transitive with "Alv Incl") as "Alv'".
    destruct x as [l [[[[[l1 x0] ξi] d1] g1] ξidx]].
    iDestruct "own" as "[gho %phys]". inversion phys. subst v.
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#G↦ [#Ggho #Pers]]".
    
    iDestruct (guards_transitive_right with "Alv Ggho") as "Lgho".
    leaf_open_laters "Lgho" with "L" as "H". { solve_ndisj. }
    iMod (lc_fupd_elim_laterN with "[£] H") as "H".
      { iApply (lc_weaken with "£"). nia. }
    iMod "H" as "[H Lback]".
    iDestruct (ty_gho_pers_impl with "H") as "[%Hineq [#InnerInnerPers #UniqBodyPers]]".
    iAssert (@[κ'] &&{ ↑NllftG; S d' + 1 }&&> l1 #↦∗_) as "#InnerPtBase".
      { iDestruct "H" as "(? & ? & ? & ? & ?)". iFrame. }
    iMod ("Lback" with "H") as "L".
    
    iModIntro. iExists l, l1.1, (llctx_interp L). iSplit; first by done. iFrame "L".
    
    iSplit. {
      rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      iApply (guards_transitive_right with "Alv G↦").
    }
    iIntros "L".
    
    iDestruct "InnerInnerPers" as "[Dead|InnerInnerPers]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv' Incl'") as "G2".
      leaf_open "G2" with "L" as "[Alive _]". { set_solver. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iDestruct (guard_inner_from_guard_uniq_body with "LFT UniqBodyPers [] Incl") as "Gghopt".
      { iApply (guards_transitive_left with "Ggho []").
        leaf_by_sep. iIntros "[A [B [C D]]]". iFrame. iIntros. done.
      }
    iDestruct (guards_weaken_rhs_sep_l with "Gghopt") as "Ggho1".
    iDestruct (guards_weaken_rhs_sep_r with "Gghopt") as "Gpt1".
    
    iModIntro. iExists (l1, x0). iFrame.
    iSplit; last by done.
    iSplit. { iApply guard_cloc_combine_fancy.
      - leaf_goal laters to (S d' + 1). { lia. }
        iApply (guards_transitive_right with "Incl InnerPtBase").
      - leaf_goal laters to (S d' + 1 + 1). { lia. } iFrame "Gpt1".
    }
    iSplit. { leaf_goal laters to (S d' + 1 + 1). { lia. }
      iApply (guards_transitive_left with "Ggho1 []").
      leaf_by_sep. iApply ty_gho_depth_mono; lia.
    }
    iNext. iApply (ty_gho_pers_depth_mono with "InnerInnerPers"); lia.
  Qed.

  Lemma type_deref_shr_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e)
      (trx ∘
        (λ post '((l, bor) -:: bl), λ mask π,
            tr post ((uniq_bor_loc bor, uniq_bor_current bor) -:: bl) mask π)
      )%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    iApply type_let; [by eapply type_deref_shr_uniq_instr|apply tctx_incl_refl| |done].
    by move=>/= ?[[??]?].
  Qed.
End borrow.

(*
Global Hint Resolve tctx_extract_hasty_borrow tctx_extract_hasty_reborrow
  | 10 : lrust_typing.*)
