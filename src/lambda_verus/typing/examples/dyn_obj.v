(** A trait-object type for VerusBelt, built WITHOUT extending `syn_type`.

    The key observation is that a fat-pointer layout is already denotable by
    existing syn-type formers:

      size_of (xprodₛ [locₛ; exec_funₛ ℭ]) = 2

    and `pt_size_eq2 : size_of 𝔄 = pt_size` together with
    `pt_phys_eq2 : syn_phys x = pt_phys x tid` force both the size and the
    physical layout from that index -- giving exactly

      [FVal (LitLoc data_ptr); FVal code_ptr]

    The only remaining freedom is the ghost predicate, and that is where the
    concrete implementing type is hidden, behind an Iris existential. This is
    the same trick `fn` uses in typing/function.v to hide its closure.

    So no new `syn_type` constructor is needed: this is a derived definition. *)

From lrust.typing Require Import type product int own function shr_bor
                                 type_context cont_context programs.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Section dyn_obj.
  Context `{!typeG Σ}.

  (** The ghost component of the index, spelled out.

      `~~(xprodₛ [locₛ; exec_funₛ ℭ])` reduces to `*[loc; val * ~~ℭ]`. Note the
      outer spine is `cons_prod` (a Record with fields `phd`/`ptl`, fancy_lists.v:97),
      NOT Coq's `prod` -- so `.1`/`.2` do not apply there. The inner `val * ~~ℭ`,
      coming from `exec_funₛ`, is a genuine `prod`. *)
  Definition dyn_data {ℭ} (x : ~~(xprodₛ [locₛ; exec_funₛ ℭ])) : loc := phd x.
  Definition dyn_code {ℭ} (x : ~~(xprodₛ [locₛ; exec_funₛ ℭ])) : val := (phd (ptl x)).1.
  Definition dyn_spec {ℭ} (x : ~~(xprodₛ [locₛ; exec_funₛ ℭ])) : ~~ℭ := (phd (ptl x)).2.

  (** A trait object.

      `vt` is the trait's vtable discipline: given a hidden concrete type `𝔄`
      with semantic type `ty`, the data pointer, the code pointer and the ghost
      spec data, it states that the code meets the trait's specification at that
      type. The existential over `(𝔄, ty)` is what erases the concrete type --
      two objects with different implementations inhabit this same type.

      Defined as a `plain_type`, so `pt_gho` must be persistent; `□` supplies
      that. That restricts this to the *shared* reading of a trait object: it
      captures the vtable discipline, not ownership of the pointee. Owning
      `Box<dyn T>` needs a full `type` with a non-persistent `ty_gho`. *)
  (* Program auto-discharges some obligations by typeclass resolution, so the
     remaining ones are not presented in record-field order. A uniform tactic
     avoids depending on that order. *)
  Local Obligation Tactic :=
    try (move => *; first [ by rewrite syn_phys_size_eq | apply _ | done ]).

  Program Definition dyn_obj {ℭ}
      (vt : ∀ 𝔄, type 𝔄 → loc → val → ~~ℭ → thread_id → iProp Σ)
      : plain_type (xprodₛ [locₛ; exec_funₛ ℭ]) :=
    {| pt_size := 2;
       pt_gho x tid :=
         (∃ (𝔄: syn_type) (ty: type 𝔄),
            □ vt 𝔄 ty (dyn_data x) (dyn_code x) (dyn_spec x) tid)%I;
       pt_phys x tid := syn_phys x;
    |}.
  (* pt_concrete: the two words are FVals (a location and a code pointer),
     never FCells, so the physical representation is concrete. *)
  Next Obligation. move => ℭ vt x tid. by destruct x as [l [[f c] []]]. Qed.
  (* pt_non_prophetic: neither locₛ nor exec_funₛ contributes prophecy variables. *)
  Next Obligation. move => ℭ vt x. by destruct x as [l [[f c] []]]. Qed.

  (** ** Instantiating the vtable discipline

      The abstract `vt` above says nothing. Here it is filled in with the real
      thing: the code pointer is a genuine `fn` at the hidden type.

      This is the load-bearing test of the whole design. `fn_spec 𝔄l 𝔅 ℭ` unfolds
      to `(~~ℭ) → predl_trans' (boxl 𝔄l) (at_locₛ 𝔅)`, so the spec's *type*
      mentions the argument syn-types -- and for a method those include `Self`,
      i.e. the hidden type. The question is whether that dependency can be
      expressed at all once `𝔄` is existentially bound.

      It can, because `vt` receives `𝔄` and `ty` as arguments: `mk_fp` and
      `mk_spec` are families indexed by the hidden type, and get instantiated
      inside the existential rather than outside it. *)
  Definition dyn_vt {𝔅 ℭ}
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ)
      : ∀ 𝔄, type 𝔄 → loc → val → ~~ℭ → thread_id → iProp Σ :=
    λ 𝔄 ty l f c tid,
      (* `fn` is already coerced plain_type -> simple_type -> type, and that
         chain defines `st_gho x d g tid := pt_gho x tid` (type.v), i.e. the
         depth/ghost-depth arguments are ignored for plain types. So `0 0` here
         is exactly `fn`'s underlying plain ghost predicate, not a weakening. *)
      ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄)) (f, c) 0 0 tid.

  (** A trait object for a single-method trait, fully instantiated. *)
  Definition dyn_trait_obj {𝔅 ℭ}
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ)
      : plain_type (xprodₛ [locₛ; exec_funₛ ℭ]) :=
    dyn_obj (dyn_vt mk_fp mk_spec).

  (** ** Erasure is reversible: recovering a callable `fn`

      This is the elimination principle dynamic dispatch needs. Holding a trait
      object, we can recover -- for SOME hidden type -- the full `fn` ownership
      of the code pointer, which is what any call rule must consume.

      Note the conclusion still binds `𝔄` existentially. That is the crux for a
      usable call rule: the caller cannot name `𝔄`, so anything it concludes must
      be `𝔄`-free. See the remark below. *)
  Lemma dyn_trait_obj_elim {𝔅 ℭ}
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ) x tid :
    pt_gho (dyn_trait_obj mk_fp mk_spec) x tid -∗
      ∃ (𝔄: syn_type) (ty: type 𝔄),
        ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄))
               (dyn_code x, dyn_spec x) 0 0 tid.
  Proof.
    iIntros "H". iDestruct "H" as (𝔄 ty) "#H".
    iExists 𝔄, ty. iApply "H".
  Qed.

  (** The recovered ownership is persistent, so a trait object may be called
      repeatedly -- unlike a `FnOnce`-style encoding, which consumes itself. *)
  Global Instance dyn_trait_obj_gho_persistent {𝔅 ℭ} mk_fp mk_spec x tid :
    Persistent (pt_gho (@dyn_trait_obj 𝔅 ℭ mk_fp mk_spec) x tid).
  Proof. apply _. Qed.

  (** ** Why the call rule stops here

      `type_call` (function.v:445) requires, via `tctx_extract_ctx`, that the
      context hold

        p ◁ fn fp spec  +::  <the arguments, as separate tctx entries>

      For a trait method the argument list `(fp x).(fp_ityl)` is `[𝔄]` -- the
      RECEIVER, at the hidden type. Two things follow.

      1. `dyn_trait_obj` is a `plain_type`, hence `pt_gho` is persistent, hence
         it owns NOTHING. There is no receiver ownership to hand to `type_call`.
         This is not an incidental gap: persistence and ownership are exclusive
         here, so no instantiation of `vt` can fix it while the type stays plain.

      2. Even given ownership, the receiver's type must be CORRELATED with the
         `𝔄` bound inside the existential. A caller cannot name `𝔄`, so it cannot
         supply the receiver from outside; the correlation has to be established
         inside the object itself.

      The hook for (2) already exists: `vt` receives the data location `l` as an
      argument (see `dyn_obj`), and `dyn_vt` simply ignores it. Making the object
      callable means using it -- asserting that `l` holds a value of the hidden
      `ty`. Two ways, matching Rust's two trait-object forms:

        - `&dyn T`   : assert `ty_shr ty ... l ...`, which is persistent, so the
                       type could stay plain. Needs a lifetime parameter.
        - `Box<dyn T>`: assert owned `l ↦∗: ty_own ...`, which is NOT persistent,
                       so this requires a full `type` with the whole obligation
                       family (ty_shr, resolve, the d/g monotonicity lemmas,
                       the guard laws).

      So the call rule is blocked on the OWNERSHIP story, not on the erasure
      story. Erasure is settled: `dyn_trait_obj_elim` above recovers a callable
      `fn` at the hidden type, and `dyn_vt` shows `fn_spec`'s dependence on `𝔄`
      is expressible. Notably, no spec-uniformity assumption was needed to get
      this far. *)

  (** ** `&dyn T`: the shared form, which DOES carry the receiver

      Now the data pointer is not ignored. The hidden type's contents are held as
      a shared borrow at `κ`, which is persistent, so the type can still be a
      `simple_type` rather than a full `type`.

      Rather than reimplement `shr_bor`'s Leaf-guard structure, this delegates to
      it: the ghost predicate embeds `ty_gho (shr_bor κ ty) v d g tid` for the
      hidden `ty`. `st_gho_depth_mono` then follows from `shr_bor`'s own depth
      monotonicity instead of needing a fresh guard proof.

      `st_guard_proph` is vacuous: its hypothesis is `ξ ∈ ξl x`, and
      `ξl x = []` at this index (proved for `dyn_obj` above). *)
  (* Explicit: no auto-solving, so obligations arrive in record order. *)
  Local Obligation Tactic := idtac.

  Program Definition dyn_shr_obj {𝔅 ℭ} (κ: lft)
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ)
      : simple_type (xprodₛ [locₛ; exec_funₛ ℭ]) :=
    {| st_size := 2;
       st_lfts := [κ];
       st_E := [];
       st_gho x d g tid :=
         (∃ (𝔄: syn_type) (ty: type 𝔄) (v: ~~(at_clocₛ 𝔄)),
            ⌜(v.1).1 = dyn_data x⌝ ∗
            □ ty_gho (shr_bor κ ty) v d g tid ∗
            □ ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄))
                     (dyn_code x, dyn_spec x) 0 0 tid)%I;
       st_phys x tid := syn_phys x;
    |}.
  (* NB: st_gho_persistent never becomes an obligation -- `Persistent` is a
     typeclass, so Coq discharges it during elaboration. Numbering below is the
     obligations Program actually generates. *)
  (* 1. st_size_eq *)
  Next Obligation. intros. by rewrite syn_phys_size_eq. Qed.
  (* 2. st_size_eq2 *)
  Next Obligation. intros. done. Qed.
  (* 3. st_phys_eq2 *)
  Next Obligation. intros. done. Qed.
  (* 4. st_gho_depth_mono -- delegated to shr_bor's own monotonicity. The fn
     component is depth-independent (plain type), so it passes through. *)
  Next Obligation.
    intros 𝔅 ℭ κ mk_fp mk_spec d g d' g' x tid Le Le'.
    iIntros "H". iDestruct "H" as (𝔄 ty v) "(%Eq & #Shr & #Fn)".
    iExists 𝔄, ty, v. iSplit; [done|]. iFrame "Fn".
    (* ty_gho_depth_mono has a borrow/restore shape:
         P d g -∗ P d' g' ∗ (P d' g' -∗ P d g)
       We only need the first conjunct. *)
    iModIntro. iDestruct (ty_gho_depth_mono with "Shr") as "[$ _]"; lia.
  Qed.
  (* 5. st_guard_proph -- vacuous: its hypothesis is ξ ∈ ξl x, and ξl x = []. *)
  Next Obligation.
    intros 𝔅 ℭ κ mk_fp mk_spec κ0 x n d g tid ξ R Hin.
    exfalso. destruct x as [l [[f c] []]]. simpl in Hin. set_solver.
  Qed.
  (* 6. st_concrete *)
  Next Obligation.
    intros 𝔅 ℭ κ mk_fp mk_spec x tid. by destruct x as [l [[f c] []]].
  Qed.

  (** Elimination for the shared form: recovers the RECEIVER and the CODE
      together, correlated at the same hidden type.

      This is what `dyn_trait_obj_elim` could not give. The receiver arrives as
      `shr_bor κ ty`, matching the `at_clocₛ 𝔄` argument type of a `&self`
      method, and the shared borrow is of our own data pointer. *)
  Lemma dyn_shr_obj_elim {𝔅 ℭ} (κ: lft)
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ) x d g tid :
    st_gho (dyn_shr_obj κ mk_fp mk_spec) x d g tid -∗
      ∃ (𝔄: syn_type) (ty: type 𝔄) (v: ~~(at_clocₛ 𝔄)),
        ⌜(v.1).1 = dyn_data x⌝ ∗
        ty_gho (shr_bor κ ty) v d g tid ∗
        ty_gho (fn (A:=unit) (λ _, mk_fp 𝔄 ty) (mk_spec 𝔄))
               (dyn_code x, dyn_spec x) 0 0 tid.
  Proof.
    iIntros "H". iDestruct "H" as (𝔄 ty v) "(%Eq & #Shr & #Fn)".
    iExists 𝔄, ty, v. iSplit; [done|]. iSplit; [iApply "Shr"|iApply "Fn"].
  Qed.

  (** ** What remains for a call rule

      With `dyn_shr_obj_elim` the two ingredients `type_call` needs are now in
      hand and correlated at one hidden type: the callee's `fn` typing, and a
      receiver whose type matches the method's argument slot.

      The remaining step is genuinely a step, not a formality. `type_call`
      consumes its arguments as *type-context entries* via `tctx_extract_ctx`,
      so producing `p +ₗ #0 ◁ shr_bor κ ty` as a tctx entry from the ghost
      predicate above means going through `tctx_interp`, and the resulting
      typing judgement must then be shown `𝔄`-free before a caller can use it.
      That last obligation is the one that has not been discharged anywhere in
      this file. *)

  (** ** A proposed call rule -- STATED, NOT PROVED

      Ended with `Abort`, so this adds NO axiom to the build. Switch to
      `Admitted` only if you want to build on it before proving it, and be aware
      that doing so makes it an axiom visible to `Print Assumptions`.

      Writing the statement is what forces the uniformity question into the
      open, and the answer is more precise than "every impl has the same spec".
      THREE things must be `𝔄`-free for a caller to use this rule, and they are
      exactly the three hypotheses below:

        (U1) the return type,
        (U2) the invariant-mask state,
        (U3) the specification.

      (U1) and (U2) are free in practice -- a trait's method signature fixes the
      return type and the mask discipline; only `Self` varies. (U3) is the real
      condition, and note what it is NOT: it does not demand that all impls share
      one spec. It demands that each impl's spec be REFINED BY a common abstract
      spec stated over the ghost component `ℭ`. That is the standard
      representation-invariant/abstract-state discipline, and it is what lets
      Verus's `d.b()` mean different things per impl while callers still reason
      uniformly. *)
  Lemma type_call_dyn {𝔅 ℭ 𝔇l 𝔈l 𝔉} (κ: lft)
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ)
      (* the 𝔄-free data the caller reasons with *)
      (oty : type 𝔅)
      (ast : invctx_atomic_state)
      (abs_spec : (~~ℭ) → pred' (~~(at_locₛ 𝔅)) → Mask → proph_asn → Prop)
      p k E L Il ϝ' (C: cctx 𝔉) (T: tctx (xprodₛ [locₛ; exec_funₛ ℭ] :: 𝔇l))
      (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) trx trk tri :
    (* U1: every impl returns the same type *)
    (∀ 𝔄 (ty: type 𝔄), (mk_fp 𝔄 ty).(fp_oty) = oty) →
    (* U2: every impl has the same mask discipline *)
    (∀ 𝔄 (ty: type 𝔄), (mk_fp 𝔄 ty).(fp_atomic_state) = ast) →
    (* U3: every impl's spec is refined by the abstract one. NOT equality. *)
    (∀ 𝔄 (c: ~~ℭ) (arg: ~~(at_locₛ (at_clocₛ 𝔄))) post mask π,
        abs_spec c post mask π → mk_spec 𝔄 c post (arg -:: -[]) mask π) →
    (* the usual side conditions, as in type_call *)
    Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' ast) →
    tctx_extract_ctx E L +[p ◁ dyn_shr_obj κ mk_fp mk_spec] T T' trx →
    k ◁cont{L, (InvCtx Il ϝ' ast), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ box oty +:: T') (Tk [#ret]) tri) →
    (* the call: code pointer is the second word, receiver the first *)
    ⊢ typed_body E L (InvCtx Il ϝ' ast) C T
        (call: (p +ₗ #1) [p +ₗ #0] → k)
        (trx ∘ (λ post '(o -:: dl), λ mask π,
           abs_spec (dyn_spec o)
                    (λ b mask' π', tri (trk post) (b -:: dl) mask' π')
                    mask π)).
  Abort.

  (** Is the premise above even satisfiable? *)
  Lemma dyn_shr_obj_not_a_tctx_entry {𝔅 ℭ} (κ: lft)
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ) p x tid :
    tctx_elt_interp tid (p ◁ (dyn_shr_obj κ mk_fp mk_spec : type _)) x ⊢ False.
  Proof.
    iIntros "H". iDestruct "H" as (v d) "(_ & _ & [_ %Heq])".
    iPureIntro. move: (f_equal length Heq).
    by rewrite syn_phys_size_eq.
  Qed.

  (** ** Corrected shape

      NON-VACUITY CHECK FIRST. The previous attempt failed because a 2-word type
      cannot be a tctx entry. Behind a `box` the size is 1, which is what an
      entry can hold, so the premise is no longer refutable on size grounds. *)
  Lemma box_dyn_size {𝔅 ℭ} (κ: lft)
      (mk_fp : ∀ 𝔄, type 𝔄 → fn_params [at_clocₛ 𝔄] 𝔅)
      (mk_spec : ∀ 𝔄, fn_spec [at_clocₛ 𝔄] 𝔅 ℭ) :
    ty_size (box (dyn_shr_obj κ mk_fp mk_spec : type _)) = 1%nat.
  Proof. done. Qed.

  (** Dispatch cannot be a single `call:`. `eval_path` (type_context.v) handles
      only pointer offsets and values -- there is NO dereference case -- so a
      function value sitting in memory cannot be named by a path. It must be
      loaded into a variable first, at which point `eval_path_of_val` makes it a
      path. Hence dispatch is a three-step sequence:

        let: "c" := !(p +ₗ #1) in     (* code pointer  *)
        let: "d" := !(p +ₗ #0) in     (* data pointer  *)
        call: "c" ["d"] → k

      The two loads are justified by `own_ptr`'s ghost predicate, which puts the
      pointee's `ty_phys` -- here exactly [FVal data; FVal code] -- into memory. *)

End dyn_obj.
