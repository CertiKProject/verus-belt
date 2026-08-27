(** Toy: casting a pointer between two one-field structs.

    struct A { x: usize }   ~>   struct B { y: usize }

    NOTE: this development has no fixed-width integers (see typing/int.v); `usize`
    is modelled by `int : type Zₛ`, which is unbounded Z. *)

From lrust.typing Require Import type product int own product_split type_context mod_ty
                                 pcell tracked shr_bor programs.
Set Default Proof Using "Type".

Section cast_toy.
  Context `{!typeG Σ}.

  (** ** The two struct types *)

  Definition A_ty : type (xprodₛ [Zₛ]) := xprod_ty +[int].
  Definition B_ty : type (xprodₛ [Zₛ]) := xprod_ty +[int].

  (** Syn-types are *structural*, not nominal: A and B are the same term. *)
  Lemma A_ty_eq_B_ty : A_ty = B_ty.
  Proof. reflexivity. Qed.

  (** ** The layout obligation, discharged *)

  (** This is the equation that `type_incl` really demands (via ty_phys_eq2).
      For a name-only cast the morphism is idₛ, so it is a triviality --
      but this is the lemma that does the work in a non-trivial cast. *)
  Lemma A_B_layout_compat (x : ~~(xprodₛ [Zₛ])) :
    syn_phys x = syn_phys (idₛ ~~$ₛ x).
  Proof. reflexivity. Qed.

  (** ** The cast on the pointee *)

  Lemma cast_A_to_B E L : subtype E L A_ty B_ty idₛ.
  Proof. apply subtype_refl. Qed.

  (** ** The cast lifted through a pointer *)

  Lemma cast_ptr_A_to_B E L n :
    subtype E L (own_ptr n A_ty) (own_ptr n B_ty) (at_loc_mapₛ idₛ).
  Proof. by apply own_subtype, cast_A_to_B. Qed.

  (** Both directions, i.e. the types are interchangeable under a pointer. *)
  Lemma eqcast_ptr_A_B E L n :
    eqtype E L (own_ptr n A_ty) (own_ptr n B_ty) (at_loc_mapₛ idₛ) (at_loc_mapₛ idₛ).
  Proof. split; by apply cast_ptr_A_to_B. Qed.

  (** ** Two usizes -> one usize: NOT a cast *)

  (** struct C { x: usize, y: usize } *)
  Definition C_ty : type (Zₛ * Zₛ) := (int * int)%T.

  (** There is no `subtype E L C_ty A_ty f` for any f, and this is not a matter of
      proof effort. `type_incl` demands ty_size equality, and:
        size_of (Zₛ * Zₛ) = 2   but   size_of (xprodₛ [Zₛ]) = 1.
      The ty_phys equation is likewise unsatisfiable: the two sides are lists of
      different lengths (2 vs 1), so no f can relate them.

      There is a second, independent reason. own_ptr carries
      `freeable_sz n ty.(ty_size)` -- the deallocation size. A cast that silently
      shrank the pointee would corrupt the free obligation. *)
  Lemma sizes_differ : size_of (Zₛ * Zₛ) ≠ size_of (xprodₛ [Zₛ]).
  Proof. done. Qed.

  (** What you want instead is to SPLIT the pointer into its fields. This is a
      tctx_incl, not a subtype: it changes the number of context entries, so it
      cannot live at the level of a single type. Note both results keep the same
      allocation size `n`, which is what preserves the freeable accounting. *)
  Definition split_C_ptr E L n p := tctx_split_own_prod n int int p E L.

  (** ...and the inverse, to put the struct back together. *)
  Definition merge_C_ptr E L n p := tctx_merge_own_prod n int int p E L.

  (** ** Prefix shrink on a 3-field struct, using ONLY existing lemmas.

      struct D { a: usize, b: usize, c: usize }

      No extension to the logic is needed for head/tail prefix shrinking:
      `Π! (𝔄 :: 𝔄l)` is *definitionally* `mod_ty to_cons_prodₛ of_cons_prodₛ
      (ty * Π! tyl)` (see product.v:99), so peeling the head off is just
      `mod_ty_out` -- a layout-preserving subtype -- and the resulting binary
      product is then split by the existing `tctx_split_own_prod`. *)

  Definition D_ty : type (xprodₛ [Zₛ; Zₛ; Zₛ]) := xprod_ty +[int; int; int].

  (** Step 1: regard the 3-field struct as head * tail. A pure subtype. *)
  Definition D_head_tail E L
    : subtype E L D_ty (int * xprod_ty +[int; int])%T of_cons_prodₛ
    := mod_ty_out E L to_cons_prodₛ of_cons_prodₛ _.

  (** Step 2: lift it through the pointer. *)
  Definition D_ptr_head_tail E L n
    : subtype E L (own_ptr n D_ty) (own_ptr n (int * xprod_ty +[int; int])%T)
        (at_loc_mapₛ of_cons_prodₛ)
    := own_subtype E L n of_cons_prodₛ _ _ (D_head_tail E L).

  (** Step 3: split off the prefix. Both entries keep the allocation size n,
      so the freeable accounting survives and the merge can restore it. *)
  Definition D_split E L n p :=
    tctx_split_own_prod n int (xprod_ty +[int; int]) p E L.

  Definition D_merge E L n p :=
    tctx_merge_own_prod n int (xprod_ty +[int; int]) p E L.

  (** ** Fields that are cells

      struct F { a: PCell<usize>, b: PCell<usize>, c: PCell<usize> }

      Two facts shape this (pcell.v:15, pcell.v:50):
        - `pcell_ty n : type (pcellₛ n)` has ty_size = n, so cells sit INLINE in
          the struct, exactly where the usizes were. Its physical content is
          `pad (FCell <$> cell_ids) n` -- FCell values, not FVal.
        - `cell_points_to_ty ty : type (trackedₛ (pcellₛ ty.(ty_size) * 𝔄))` has
          ty_size = 0. The permission is ZERO-SIZED and is a separate context
          entry; it is not part of the struct's layout at all.

      Consequence: the shrink machinery is generic in the field type, so it
      applies to cell fields verbatim. But splitting the struct pointer says
      nothing about the permissions -- those travel independently. *)

  Definition F_ty : type (xprodₛ [pcellₛ 1; pcellₛ 1; pcellₛ 1]) :=
    xprod_ty +[pcell_ty 1; pcell_ty 1; pcell_ty 1].

  (** The cells occupy the same space three usizes would. *)
  Lemma F_ty_size : size_of (xprodₛ [pcellₛ 1; pcellₛ 1; pcellₛ 1]) = 3%nat.
  Proof. done. Qed.

  (** ...while the permission for one field is zero-sized. *)
  Lemma cell_perm_size : size_of (trackedₛ (pcellₛ 1 * Zₛ)) = 0%nat.
  Proof. done. Qed.

  (** Prefix shrink, identical in shape to the plain-usize case. *)
  Definition F_head_tail E L
    : subtype E L F_ty (pcell_ty 1 * xprod_ty +[pcell_ty 1; pcell_ty 1])%T
        of_cons_prodₛ
    := mod_ty_out E L to_cons_prodₛ of_cons_prodₛ _.

  Definition F_ptr_head_tail E L n
    : subtype E L (own_ptr n F_ty)
        (own_ptr n (pcell_ty 1 * xprod_ty +[pcell_ty 1; pcell_ty 1])%T)
        (at_loc_mapₛ of_cons_prodₛ)
    := own_subtype E L n of_cons_prodₛ _ _ (F_head_tail E L).

  Definition F_split E L n p :=
    tctx_split_own_prod n (pcell_ty 1) (xprod_ty +[pcell_ty 1; pcell_ty 1]) p E L.

  Definition F_merge E L n p :=
    tctx_merge_own_prod n (pcell_ty 1) (xprod_ty +[pcell_ty 1; pcell_ty 1]) p E L.

  (** NB: a struct of cells and a struct of plain usizes have the SAME size
      (size_of (pcellₛ 1) = 1 = size_of Zₛ), so unlike the 2->1 case the cast is
      not rejected on size. It is rejected on the ty_phys equation instead:
      `pad (FCell <$> _) 1` versus `[FVal (LitInt _)]` are different fancy_vals.
      Same size, incompatible representation. *)

  (** ** Bringing in the PointsTo permissions

      The permission for one `PCell<usize>` field. Note the index: the FIRST
      component of `trackedₛ (pcellₛ _ * 𝔄)` is the cell-id list, the second is
      the value. `pcell_ty` is indexed by that same cell-id list -- that shared
      component is the entire link between a cell and its permission. *)

  Definition F_perm : type (trackedₛ (pcellₛ 1 * Zₛ)) := cell_points_to_ty int.

  (** The field type and the permission agree on the cell size, definitionally. *)
  Lemma int_size : ty_size int = 1%nat.
  Proof. done. Qed.

  (** *** The split carries the permissions, untouched

      The permissions are keyed by cell id, not by location, so splitting the
      struct pointer leaves them alone: they are simply framed. This is the
      precise sense in which "shrinking" and "distributing permissions" are
      independent operations for cells. *)

  Definition F_split_with_perms E L n p pa pb pc :=
    tctx_incl_frame_r _ _ +[pa ◁ F_perm; pb ◁ F_perm; pc ◁ F_perm] _ E L
      (F_split E L n p).

  Definition F_merge_with_perms E L n p pa pb pc :=
    tctx_incl_frame_r _ _ +[pa ◁ F_perm; pb ◁ F_perm; pc ◁ F_perm] _ E L
      (F_merge E L n p).

  (** *** Actually using a permission

      `typed_pcell_borrow` consumes shared borrows of BOTH the cell and its
      permission and yields a shared borrow of the contents. Its postcondition
      carries the side condition `γs = γs'`: the permission's cell-id component
      must equal the cell's. That equation is what stops you from opening one
      field's cell with another field's PointsTo. *)

  Definition F_borrow_field κ pcell_ref perm_ref E L I :=
    typed_pcell_borrow κ pcell_ref perm_ref int E L I.

  Definition F_borrow_mut_field κ pcell_ref perm_ref E L I :=
    typed_pcell_borrow_mut κ pcell_ref perm_ref int E L I.

  (** ** Correspondence: vstd's PCell::borrow_mut axiom vs. the proved rule

      vstd 0.2026.06.21 (vstd/cell/pcell.rs:159) axiomatizes, via
      #[verifier::external_body]:

        pub fn borrow_mut<'a>(&'a self, Tracked(perm): Tracked<&'a mut PointsTo<T>>)
              -> (v: &'a mut T)
            requires self.id() == perm.id(),
            ensures  &*v == old(perm).value(),
                     &*final(v) == final(perm).value(),
                     final(perm).id() == self.id(),
            opens_invariants none
            no_unwind

      `typed_pcell_borrow_mut` is the *proved* rule for the same operation. Every
      vstd clause has a counterpart; specialised below to a single usize cell:

      | vstd clause                       | typed_pcell_borrow_mut condition                     |
      |-----------------------------------|------------------------------------------------------|
      | requires self.id() == perm.id()   | γs = γs'                                             |
      | &*v == old(perm).value()          | uniq_bor_current bor' = x                            |
      | &*final(v) == final(perm).value() | uniq_bor_future bor' π = snd (uniq_bor_future bor π) |
      | final(perm).id() == self.id()     | (uniq_bor_future bor π).1 = γs                       |
      | (no counterpart)                  | uniq_bor_loc bor' = cloc_flat_insert cl γs           |
      | opens_invariants none / no_unwind | (no counterpart; masks live in the InvCtx)           |

      The THIRD ensures is the load-bearing one. It is exactly what the
      FIXME[SOUNDNESS] on `ReprPtr::borrow_mut` in certik-vostd's
      verified_libs/vstd_extra/src/cast_ptr.rs cannot justify for a general
      `Repr`. Here it is not assumed: the permission is taken as a UNIQUE borrow
      `&uniq{κ} (cell_points_to_ty ty)`, and the prophesied final value of that
      borrow has its cell-id component pinned to γs. Only the value component is
      free to change. Contrast `typed_pcell_borrow` (the shared-borrow rule),
      whose only side condition is `γs = γs'` -- no prophecy is needed there
      because nothing can change.

      Note the shape difference that stops this transferring to `Repr` directly:
      `cell_points_to_ty` is indexed by `trackedₛ (pcellₛ n * 𝔄)`, a FIXED shape
      in which only 𝔄 varies, whereas `Repr::to_repr_spec : (self, Perm) ->
      (R, Perm)` may return a different permission entirely. *)

  (** The rule specialised to exactly the cell type `F` uses, i.e. the
      justification for `F::borrow_mut_a` in the Verus library. *)
  Definition F_borrow_mut_a_spec κ pcell_ref perm_mut_ref E L I
      (Alv : lctx_lft_alive E L κ) :=
    typed_pcell_borrow_mut κ pcell_ref perm_mut_ref int E L I Alv.

End cast_toy.
