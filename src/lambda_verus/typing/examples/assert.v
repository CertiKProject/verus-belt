From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs bool own cont uninit.
From lrust.lang Require Import lang notation.
Set Default Proof Using "Type".

Section assert.
  Context `{!typeG Σ}.
  
  (* assert takes a bool argument b and performs undefined behavior if !b
     It's more like Rust's `assert_unchecked`.
  *)
  Definition assert : val :=
    fn: ["b"] :=
      let: "b'" := !"b" in
      if: "b'" then
        let: "r" := new [ #0] in
        return: ["r"]
      else
        let: "r" := !(#☠) in (* undefined behavior *)
        return: ["r"]
    .
  
  (* verify `assert(b)` with precondition `b` *)
  Lemma assert_type :
    typed_val
        assert
        ((fn(∅; bool_ty) → ()) (λ (c: ~~ ()) 𝛷 '-[(l, b)] , λ mask π, b ∧ ∀ ret, 𝛷 ret mask π))
        (assert, ()).
  Proof.
    unfold assert. unlock.
    opose proof (@type_fn
        _ _ _
        [boolₛ]
        ()
        ()
        ()
        (λ y: (), FP ∅ +[bool_ty] () AtomicClosed)
        (λ (c: ~~ ()) 𝛷 '-[(l, b)] , λ mask π, b ∧ ∀ ret, 𝛷 ret mask π)
        (_)
        [BNamed "b"] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
    iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := boolₛ) _ (bool_ty)); trivial.
        * apply bool_stack_okay.
        * apply read_own_copy. apply bool_copy.
      }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      { iIntros (v). simpl_subst. iApply type_if.
        * apply tctx_extract_elt_here_exact.
        (* branch 1 *)
        * iApply (type_new_subtype () 0 with "[]"); first by lia.
          { apply uninit_unit_1. }
          iIntros. simpl_subst. iApply type_jump.
           -- rewrite elem_of_list_singleton. reflexivity.
           -- apply tctx_extract_elt_here_exact.
           -- apply resolve_tctx_just.
           -- reflexivity.
        (* branch 2 *)
        * iApply typed_body_vacuous.
      }
    }
    intros post [[l b] []] mask π.
    simpl. unfold trans_upper. simpl.
    intros [Hb Hforall]. intros [l1 b1] Heq. inversion Heq. subst l1. subst b1.
    destruct b; last by done. intros. apply Hforall.
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
    
      
End assert.
