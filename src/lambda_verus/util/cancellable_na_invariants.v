(* forked from iris/iris/base_logic/lib/na_invariants.v *)

From iris.algebra Require Import gset coPset dfrac_agree auth gmultiset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
From iris.algebra Require Import excl.
From lrust.util Require Import update.
Import uPred.

(* Non-atomic ("thread-local") invariants. *)

Definition na_inv_pool_name := gname.

(* primary purpose of the fork is to make it use this namespace *)
Definition nainvN       : namespace := nroot .@ "non_atomic_inv".

Class na_invG Σ := {
  #[local] na_inv_inG :: inG Σ (prodR coPset_disjR (gset_disjR positive)) ;
  #[local] na_inv_exclG :: inG Σ (exclR unitO) ;
  #[local] na_inv_authG :: inG Σ (authR (gmultisetUR lft)) ;
  #[local] na_inv_lftG :: inG Σ (dfrac_agreeR (leibnizO (option lft)))
}.
Local Existing Instance na_inv_exclG.

Definition na_invΣ : gFunctors :=
  #[ GFunctor (constRF (prodR coPset_disjR (gset_disjR positive)));
     GFunctor (exclR unitO);
     GFunctor (authR (gmultisetUR lft));
     GFunctor (dfrac_agreeR (leibnizO (option lft)))
   ].
Global Instance subG_na_invG {Σ} : subG na_invΣ Σ → na_invG Σ.
Proof. solve_inG. Qed.

Section na_gmultiset_util.
  Context `{!na_invG Σ}.
  
  Local Definition na_lfts_own_gmultiset (γ: gname) (κs: gmultiset lft) : iProp Σ := own γ (● κs).
  Local Definition na_lfts_own_single (γ: gname) (κ: lft) : iProp Σ :=
    own γ (◯ {[+ κ +]}).
  Local Lemma na_lfts_elem_of γ κ κs :
      na_lfts_own_gmultiset γ κs -∗ na_lfts_own_single γ κ -∗ ⌜κ ∈ κs⌝. 
  Proof.
    iIntros "H H1".
    iCombine "H H1" as "H".
    iDestruct (own_valid with "H") as "%H".
    apply auth_both_valid_discrete in H as [?%gmultiset_included _].
    iPureIntro.
    multiset_solver.
  Qed.

  Local Lemma na_lfts_insert γ κ κs :
      na_lfts_own_gmultiset γ κs ==∗
      na_lfts_own_gmultiset γ ({[+ κ +]} ⊎ κs) ∗ na_lfts_own_single γ κ. 
  Proof.
    iIntros "H".
    iMod (own_update with "H") as "[H1 H2]".
    { apply (auth_update_alloc _ ({[+ κ +]} ⊎ κs) {[+ κ +]}).
      apply gmultiset_local_update.
      multiset_solver. }
    by iFrame.
  Qed.

  Local Lemma na_lfts_delete γ κ κs :
      na_lfts_own_gmultiset γ κs -∗ na_lfts_own_single γ κ ==∗ ∃ κs',
      na_lfts_own_gmultiset γ κs' ∗ ⌜κs = ({[+ κ +]} ⊎ κs')⌝. 
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [H%gmultiset_included _].
    iMod (own_update with "H") as "H".
    { apply (auth_update_dealloc _ _ (κs ∖ {[+ κ +]})).
      apply gmultiset_local_update; by multiset_solver. }
    iModIntro.
    iFrame.
    iPureIntro.
    multiset_solver.
  Qed.

  Local Lemma na_lfts_own_gmultiset_alloc :
    ⊢ |==> ∃ γ, na_lfts_own_gmultiset γ ∅. 
  Proof. iApply own_alloc. apply auth_auth_valid. done. Qed.
  
End na_gmultiset_util.

Section na_lft_agree_util.
  Context `{!na_invG Σ}.
  
  Local Definition lft_tok γ (κ: option lft) : iProp Σ :=
      own γ (to_frac_agree (A:=leibnizO (option lft)) (1/2)%Qp κ).
  
  Local Lemma lft_tok_alloc κ :
      ⊢ |==> ∃ γ, lft_tok γ κ ∗ lft_tok γ κ.
  Proof.
      unfold lft_tok.
      iMod (own_alloc
          (to_frac_agree (A:=leibnizO (option lft)) (1 / 2) κ ⋅ to_frac_agree (A:=leibnizO (option lft)) (1 / 2) κ)) as (γ) "[Ho Ho2]".
        - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
        - iModIntro. iExists γ. iFrame.
  Qed.
      
  Local Lemma lft_tok_agree γ κ1 κ2 :
      lft_tok γ κ1 -∗ lft_tok γ κ2 -∗ ⌜κ1 = κ2⌝.
  Proof.
    unfold lft_tok. iIntros "A B". iCombine "A B" as "H".
    iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
      
  Local Lemma lft_tok_update γ (κ1 κ2 κ : option lft) :
      lft_tok γ κ1 -∗ lft_tok γ κ2 ==∗ lft_tok γ κ ∗ lft_tok γ κ.
  Proof.
    unfold lft_tok. iIntros "A B". iCombine "A B" as "H". rewrite <- own_op.
    iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
End na_lft_agree_util.

Section active_tok_util.
  Context `{!na_invG Σ}.
  
  Local Definition Active (γ: gname) : iProp Σ := own γ (Excl ()).
  
  Local Lemma new_active : ⊢ |==> ∃ γ , Active γ.
  Proof.
    iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold Active. iFrame "H".
  Qed.
    
  Local Lemma active_active_false (γc : gname) : Active γc -∗ Active γc -∗ False.
  Proof. 
    iIntros "X Y". iCombine "X Y" as "X".
    iDestruct (own_valid with "X") as "%J". contradiction.
  Qed.
End active_tok_util.

Section defs.
  Context `{!invGS Σ, !na_invG Σ, !llft_logicGS Σ}.
  
  Local Definition γf1 (γ: gname) : gname := match prod_decode_fst γ with Some x => x | _ => γ end.
  Local Definition γf2 (γ: gname) : gname := match prod_decode_snd γ with Some x => x | _ => γ end.
  Local Definition γa := γf1. (* active tokens *)
  Local Definition γk := γf2. (* lifetime agreement tokens *)
  Local Definition γp := γf1. (* lifetime multiset tokens *)
  Local Definition γm := γf2. (* na_own pool tokens *)

  Definition na_own (p : na_inv_pool_name) (E : coPset) : iProp Σ :=
    own (γp p) (CoPset E, GSet ∅).
    
  Definition na_active (γ : gname) : iProp Σ := Active (γa γ).
  
  Definition guarded_active (γ: gname) (p: na_inv_pool_name) : iProp Σ :=
      ∃ κ d, £(d+1) ∗ (@[κ] &&{↑NllftG;d}&&> na_active γ) ∗ na_lfts_own_single (γm p) κ ∗ lft_tok (γk γ) (Some κ).

  Definition na_inv (γ: gname) (p : na_inv_pool_name) (N : namespace) (P : iProp Σ) : iProp Σ :=
    ∃ i, (⌜i ∈ (↑N:coPset)⌝ ∧ inv nainvN (
        (na_active γ ∗ lft_tok (γk γ) None ∗ lft_tok (γk γ) None)
        ∨ (P ∗ own (γp p) (ε, GSet {[i]}) ∗ lft_tok (γk γ) None ∗ lft_tok (γk γ) None)
        ∨ (na_own p {[i]} ∗ guarded_active γ p)
    )).
End defs.

Global Instance: Params (@na_inv) 3 := {}.
Global Typeclasses Opaque na_own na_inv.

Section proofs.
  Context `{!invGS Σ, !na_invG Σ, !llft_logicGS Σ}.

  Global Instance na_own_timeless p E : Timeless (na_own p E).
  Proof. rewrite /na_own; apply _. Qed.

  Global Instance na_inv_ne γ p N : NonExpansive (na_inv γ p N).
  Proof. rewrite /na_inv. solve_proper. Qed.
  
  Global Instance na_inv_proper γ p N : Proper ((≡) ==> (≡)) (na_inv γ p N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent γ p N P : Persistent (na_inv γ p N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Global Instance na_own_empty_persistent p : Persistent (na_own p ∅).
  Proof. rewrite /na_own; apply _. Qed.

  Lemma na_inv_iff γ p N P Q : na_inv γ p N P -∗ ▷ □ (P ↔ Q) -∗ na_inv γ p N Q.
  Proof.
    rewrite /na_inv. iIntros "(%i & % & HI) #HPQ".
    iExists i. iSplit; first done. iApply (inv_iff with "HI").
    iIntros "!> !>".
    iSplitR; iIntros "[$|[[? Ho]|$]]"; iRight; iLeft; iFrame "Ho"; by iApply "HPQ".
  Qed.

  Lemma na_alloc : ⊢ |==> ∃ p, na_own p ⊤ ∗ na_lfts_own_gmultiset (γm p) ∅.
  Proof. 
    iIntros.
    iMod (own_alloc (CoPset ⊤, GSet ∅)) as (γ1) "A"; first by done.
    iMod (na_lfts_own_gmultiset_alloc) as (γ2) "B".
    iExists (prod_encode γ1 γ2). unfold na_own, γp, γf1, γm, γf2.
    repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    iFrame. done.
  Qed.

  Lemma na_own_disjoint p E1 E2 : na_own p E1 -∗ na_own p E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    iApply wand_intro_r.
    rewrite /na_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.

  Lemma na_own_union p E1 E2 :
    E1 ## E2 → na_own p (E1 ∪ E2) ⊣⊢ na_own p E1 ∗ na_own p E2.
  Proof.
    intros ?. by rewrite /na_own -own_op -pair_op left_id coPset_disj_union.
  Qed.
  
  Lemma na_own_union2 p E1 E2 :
    na_own p E1 -∗ na_own p E2 -∗ na_own p (E1 ∪ E2).
  Proof.
    iIntros "A B". iDestruct (na_own_disjoint with "A B") as "%Hval".
    rewrite na_own_union; trivial. iFrame.
  Qed.

  Lemma na_own_acc E2 E1 tid :
    E2 ⊆ E1 → na_own tid E1 -∗ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1).
  Proof.
    intros HF. assert (E1 = E2 ∪ (E1 ∖ E2)) as -> by exact: union_difference_L.
    rewrite na_own_union; last by set_solver+. iIntros "[$ $]". auto.
  Qed.

  Lemma na_inv_alloc p E N P : ▷ P ={E}=∗ ∃ γ , na_active γ ∗ na_inv γ p N P.
  Proof.
    iIntros "HP".
    iMod (new_active) as (γ1) "Active".
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) (γp p)) as "Hempty".
    iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hown]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (λ i, i ∈ (↑N:coPset)))=> Ef.
        apply fresh_inv_name. }
    iMod (lft_tok_alloc None) as (γ2) "[tok1 tok2]".
    simpl. iDestruct "Hm" as %(<- & i & -> & ?).
    rewrite /na_inv.
    iExists (prod_encode γ1 γ2).
    unfold na_active, γa, γf1, γk, γf2.
    repeat (rewrite prod_decode_encode_fst || rewrite prod_decode_encode_snd).
    iFrame "Active".
    iMod (inv_alloc nainvN with "[-]"); last (iModIntro; iExists i; eauto).
    iNext. iRight. iLeft. iFrame.
  Qed.
  
  Lemma na_inv_destroy E γ p N P κs G :
    ↑nainvN ∪ ↑NllftG ⊆ E →
    na_inv γ p N P -∗
    na_lfts_own_gmultiset (γm p) κs -∗
    na_active γ -∗
    (∀ (κ: lft) , ⌜κ ∈ κs⌝ -∗ (G &&{↑NllftG}&&> @[κ])) -∗
    G
    ={E}=∗
      na_lfts_own_gmultiset (γm p) κs ∗ G ∗ ▷ P.
  Proof.
      iIntros (Hmask) "HInv Lfts Active #Guards G".
      unfold na_inv. iDestruct "HInv" as (i) "[%Hin HInv]".
      iInv "HInv" as "[[>Active2 toks]|[[P [>Hdis toks]]|[>Htoki2 guarded_active]]]" "Hclose".
       - iExFalso. iApply (active_active_false with "Active Active2").
       - iFrame "P Lfts G". iMod ("Hclose" with "[Active toks]"); last by done.
         iLeft. iFrame.
       - iDestruct "guarded_active" as (κ d) "[>[£d £1] guarded_active]".
         iMod (lc_fupd_elim_later with "£1 guarded_active") as "[#guard [κtok κtok2]]".
         iDestruct (na_lfts_elem_of with "Lfts κtok") as "%Hκin".
         iDestruct ("Guards" $! κ Hκin) as "#guard2".
         iDestruct (guards_transitive_right with "guard2 guard") as "guard3".
         leaf_open_laters "guard3" with "G" as "Open"; first by solve_ndisj.
         iMod (lc_fupd_elim_laterN with "£d Open") as "Open".
         iMod "Open" as "[Active2 _]".
         iExFalso. iApply (active_active_false with "Active Active2").
  Qed.
  
  Local Instance na_lfts_own_single_timeless γ κ : Timeless (na_lfts_own_single γ κ).
  Proof. rewrite /na_lfts_own_single; apply _. Qed.

  Lemma na_inv_acc γ p E F N P κs κ G d :
    ↑nainvN ∪ ↑NllftG ⊆ E → ↑N ⊆ F →
    na_inv γ p N P -∗ na_own p F -∗
    na_lfts_own_gmultiset (γm p) κs -∗
    (G &&{↑NllftG;d}&&> na_active γ) -∗
    (@[κ] &&{↑NllftG;d}&&> na_active γ) -∗
    £(d+1) -∗
    G 
    ={E}=∗ ▷ P ∗ G ∗ na_own p (F∖↑N) ∗ na_lfts_own_gmultiset (γm p) ({[+ κ +]} ⊎ κs) ∗
         (∀ F' E' κs', ⌜↑nainvN ⊆ E'⌝ → ▷ P ∗ na_own p F' ∗ na_lfts_own_gmultiset (γm p) κs'
          ={E'}=∗ ∃ κs'', ⌜ κs' = {[+ κ +]} ⊎ κs'' ∧ F' ## ↑N⌝ ∗ na_own p (F' ∪ ↑N) ∗ na_lfts_own_gmultiset (γm p) κs'').
  Proof.
    rewrite /na_inv. iIntros (??) "#(%i & % & Hinv) Htoks Hκs #guard1 #guard2 £ G".
    rewrite [F as X in na_own p X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki Htokj] $]".
    iInv "Hinv" as "[[>Active2 toks]|[[P [>Hdis [>tokκ1 >tokκ2]]]|[>Htoki2 guarded_active]]]" "Hclose".
      - leaf_open_laters "guard1" with "G" as "Open"; first by solve_ndisj.
        iDestruct "£" as "[£d £1]".
        iMod (lc_fupd_elim_laterN with "£d Open") as "Open".
        iMod "Open" as "[Active _]".
        iExFalso. iApply (active_active_false with "Active Active2").
      - iMod (na_lfts_insert _ κ κs with "Hκs") as "[Hκs Hκ]".
        iMod (lft_tok_update _ _ _ (Some κ) with "tokκ1 tokκ2") as "[tokκ1 tokκ2]".
        iMod ("Hclose" with "[Htoki Hκ tokκ1 £]") as "Hclose".
          { iNext. iRight. iRight. iFrame. iFrame "guard2". }
          
        iModIntro. iFrame "G P Hκs". iIntros (E' F' κs' Hmask). iIntros "[P [Hdis2 κs]]".
        
        iInv "Hinv" as "[[>Active2 [>tokκ1' >tokκ2']]|[[P' [>Hdis' [>tokκ1' >tokκ2']]]|[>Htoki2 guarded_active]]]" "Hclose2".
         + iDestruct (lft_tok_agree with "tokκ2 tokκ1'") as "%Hval". discriminate.
         + iDestruct (lft_tok_agree with "tokκ2 tokκ1'") as "%Hval". discriminate.
         + iDestruct "guarded_active" as (κ' d') "[£ [guard [>single >tokκ1]]]".
           iDestruct (lft_tok_agree with "tokκ1 tokκ2") as "%Hval". inversion Hval. subst κ'.
           iMod (lft_tok_update _ _ _ None with "tokκ1 tokκ2") as "[tokκ1 tokκ2]".
           iMod ("Hclose2" with "[P tokκ1 tokκ2 Hdis]"). {
            iNext. iRight. iLeft. iFrame.
           }
           iMod (na_lfts_delete with "κs single") as (κs'') "[single %Hmultiseteq]".
           iModIntro. iFrame.
           iDestruct (na_own_union2 with "Htoki2 Htokj") as "H".
           rewrite <- union_difference_L; last by set_solver.
           iDestruct (na_own_disjoint with "Hdis2 H") as "%Hdisj".
           iDestruct (na_own_union2 with "Hdis2 H") as "H".
           iFrame. done.
      - iDestruct (na_own_disjoint with "Htoki Htoki2") as "%Hval".
        exfalso. set_solver.
  Qed.

  Lemma na_own_empty p : ⊢ |==> na_own p ∅.
  Proof. apply: own_unit. Qed.

  Global Instance into_inv_na γ p N P : IntoInv (na_inv γ p N P) N := {}.
  
  (*Lemma na_inv_alter γ p N P Q :
      na_inv γ p N P -∗
      ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗
      na_inv γ p N Q.
  Proof.
      iIntros "#NaInv #Cons". unfold na_inv. iDestruct "NaInv" as (i) "[Hin Inv]".
      iExists i. iFrame "Hin". iApply (inv_alter with "Inv"). iNext. iModIntro.
      iIntros "[A|[B|C]]".*)

(*
  Global Instance into_acc_na p F E N P :
    IntoAcc (X:=unit) (na_inv p N P)
            (↑N ⊆ E ∧ ↑N ⊆ F) (na_own p F) (fupd E E) (fupd E E)
            (λ _, ▷ P ∗ na_own p (F∖↑N))%I (λ _, ▷ P ∗ na_own p (F∖↑N))%I
              (λ _, Some (na_own p F))%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros ((?&?)) "#Hinv Hown".
    rewrite exist_unit -assoc /=.
    iApply (na_inv_acc with "Hinv"); done.
  Qed.
  *)
End proofs.
