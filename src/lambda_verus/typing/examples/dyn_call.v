(** SCAFFOLD for the dynamic-dispatch call rule.

    ############################################################
    ## THIS FILE CONTAINS `Admitted` LEMMAS -- IT ADDS AXIOMS. ##
    ## Do not depend on it from proved developments.           ##
    ## `dyn_obj.v` is axiom-free; this file is not.            ##
    ############################################################

    Kept separate from `dyn_obj.v` precisely so that the proved material there
    stays clean. Check progress with `Print Assumptions type_call_dyn`.

    Background, established in dyn_obj.v:
      - `dyn_shr_obj` is a well-formed `simple_type`, size 2, laid out as
        [FVal (LitLoc data); FVal code].
      - `dyn_shr_obj_elim` recovers the receiver (as a shared borrow at κ) and
        the code pointer (as an `fn`), correlated at ONE hidden type.
      - A 2-word type cannot be a tctx entry, so the object is used behind a
        `box` (`box_dyn_size` : size 1).
      - `eval_path` has no dereference case, so the code pointer must be loaded
        into a variable before it can be called.
      - The intermediate loaded values cannot be given 𝔄-free types, so the rule
        must be ATOMIC: one judgement about the whole sequence, with the
        existential destructed inside the Iris proof. *)

From lrust.typing Require Import type product int own function shr_bor
                                 type_context cont_context programs borrow uninit.
From lrust.typing.examples Require Import dyn_obj.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import notation.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Section dyn_call.
  Context `{!typeG Σ}.
  Context {𝔅 ℭ : syn_type} (κ: lft).
  Context (mk_fp   : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅).
  Context (mk_spec : ∀ 𝔄, fn_spec  [at_clocₛ 𝔄] 𝔅 ℭ).

  (** The 𝔄-free data a caller reasons with. *)
  Context (oty : type 𝔅).
  Context (ast : invctx_atomic_state).
  Context (abs_spec : (~~ℭ) → pred' (~~(at_locₛ 𝔅)) → Mask → proph_asn → Prop).

  (** ** The uniformity hypotheses

      These are what make a caller able to use the rule without naming the
      hidden type. U0-U2 are consequences of a trait's method signature being
      fixed except for `Self`; I expect them to be `reflexivity` at any real
      instantiation. U3 is the substantive one -- and note it is a REFINEMENT,
      not an equality: impls may have genuinely different specs so long as each
      is implied by a common abstract spec stated over the ghost component ℭ. *)

  (** U0: the method takes `&'κ Self`. This also pins the receiver type, which
      is what the call's argument slot must match. Surfaced by working out what
      `type_call_iris` wants for `box_typel (fp x).(fp_ityl)`. *)
  Hypothesis U0 : ∀ 𝔄 (ty: type 𝔄), (mk_fp 𝔄 ty).(fp_ityl) = +[shr_bor κ ty].
  (** U1: every impl returns the same type. *)
  Hypothesis U1 : ∀ 𝔄 (ty: type 𝔄), (mk_fp 𝔄 ty).(fp_oty) = oty.
  (** U2: every impl has the same mask discipline. *)
  Hypothesis U2 : ∀ 𝔄 (ty: type 𝔄), (mk_fp 𝔄 ty).(fp_atomic_state) = ast.
  (** U3: every impl's spec is refined by the abstract one. *)
  Hypothesis U3 : ∀ 𝔄 (c: ~~ℭ) (arg: ~~(at_locₛ (at_clocₛ 𝔄))) post mask π,
      abs_spec c post mask π → mk_spec 𝔄 c post (arg -:: -[]) mask π.

  (** ** The dispatch sequence

      `p` points at the two-word fat pointer. We load the code word, allocate a
      one-word box for the argument (λRust passes arguments boxed -- see
      `box_typel` in `type_call`), store the data word into it, and call.

      NOTE: the allocation is my reading of the calling convention rather than
      something I have verified. If arguments can be passed unboxed here, this
      collapses to two loads and a call, and STEP 3 below gets simpler. This is
      the first thing worth checking interactively. *)
  Definition dyn_dispatch (p k: expr) : expr :=
    (let: "c" := !(p +ₗ #1) in
     let: "d" := new [ #1 ] in
     "d" <- !(p +ₗ #0) ;;
     call: "c" ["d"] → k)%E.

  (** ** STEP 1 -- open the box

      From the tctx entry for the boxed object, recover:
        - the location `l` that `p` evaluates to,
        - the two words in memory at `l`,
        - the ghost package (hidden type, receiver, code typing).

      Should follow from `own_ptr`'s ghost predicate, which places the pointee's
      `ty_phys` -- here exactly [FVal (LitLoc data); FVal code] -- into memory,
      composed with `dyn_shr_obj_elim`. *)
  Lemma dyn_box_open tid (o : ~~(at_locₛ (xprodₛ [locₛ; exec_funₛ ℭ]))) p :
    tctx_elt_interp tid (p ◁ box (dyn_shr_obj κ mk_fp mk_spec)) o -∗
      ∃ (𝔄: syn_type) (ty: type 𝔄) (v: ~~(at_clocₛ 𝔄)) (d: nat),
          ⌜(v.1).1 = dyn_data (snd o)⌝ ∗
          ty_gho (shr_bor κ ty) v d 0 tid ∗
          ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄))
                 (dyn_code (snd o), dyn_spec (snd o)) 0 0 tid.
  Admitted.

  (** ** STEP 2 -- the loaded code value is a well-typed callee

      After `let: "c" := !(p +ₗ #1)`, the variable is bound to a VALUE, and
      `eval_path_of_val` makes any value a legitimate path. That is what lets us
      hand it to `type_call_iris`, which needs `tctx_elt_interp tid (q ◁ fn ..)`.

      This is where 𝔄 stays local: the statement mentions it, but it is only
      ever used inside the proof of STEP 4. *)
  Lemma dyn_code_hasty tid 𝔄 (ty: type 𝔄) (c: val) (g: ~~ℭ) :
    ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄)) (c, g) 0 0 tid -∗
      tctx_elt_interp tid ((of_val c) ◁ fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄)) (c, g).
  Admitted.

  (** ** STEP 3 -- the argument box holds the receiver

      The receiver word from the fat pointer is the `shr_bor κ ty` value (its
      location component is the data pointer, by the correlation in
      `dyn_shr_obj`). After boxing, it is the `box (shr_bor κ ty)` entry that
      `box_typel (fp 𝔄 ty).(fp_ityl)` demands -- via U0. *)
  Lemma dyn_arg_hasty tid 𝔄 (ty: type 𝔄) (dl: loc) (v: ~~(at_clocₛ 𝔄)) d :
    ⌜(v.1).1 = dl⌝ -∗
    ty_gho (shr_bor κ ty) v d 0 tid -∗
      ∃ (w : ~~(at_locₛ (at_clocₛ 𝔄))),
        tctx_elt_interp tid ((of_val #dl) ◁ box (shr_bor κ ty)) w.
  Admitted.

  (** ** STEP 4 -- the rule

      Composition: STEP 1 to open, destruct the existential (𝔄 becomes local),
      STEP 2 and STEP 3 to build the entries `type_call_iris` needs, then
      `type_call_iris` itself, with U0-U2 rewriting the impl-specific data to the
      abstract data and U3 converting the caller's `abs_spec` obligation into the
      `mk_spec 𝔄` obligation the callee actually requires. *)
  Lemma type_call_dyn {𝔇l 𝔈l 𝔉}
      p k E L Il ϝ' (C: cctx 𝔉)
      (T: tctx (at_locₛ (xprodₛ [locₛ; exec_funₛ ℭ]) :: 𝔇l))
      (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) trx trk tri :
    Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' ast) →
    tctx_extract_ctx E L +[p ◁ box (dyn_shr_obj κ mk_fp mk_spec)] T T' trx →
    k ◁cont{L, (InvCtx Il ϝ' ast), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ box oty +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' ast) C T
        (dyn_dispatch p k)
        (trx ∘ (λ post '(o -:: dl), λ mask π,
           abs_spec (dyn_spec (snd o))
                    (λ b mask' π', tri (trk post) (b -:: dl) mask' π')
                    mask π)).
  Admitted.

End dyn_call.
