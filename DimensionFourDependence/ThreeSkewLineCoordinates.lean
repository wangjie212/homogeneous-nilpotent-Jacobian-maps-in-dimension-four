import DimensionFourDependence.Basic

/-! # Coordinates for three pairwise skew projective lines

Three mutually complementary vector subspaces admit coordinates in which
they become the two axes and the diagonal. For two-dimensional subspaces
this is the elementary coordinate step used at the end of Section 3.2.
No existence or genericity assertion about a family of lines is assumed proved here.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- Identify two complements using their common quotient. -/
noncomputable def complementChange (P U W : Submodule F A)
    (hPU : IsCompl P U) (hPW : IsCompl P W) : U ≃ₗ[F] W :=
  (P.quotientEquivOfIsCompl U hPU).symm.trans (P.quotientEquivOfIsCompl W hPW)

/-- Changing a complement commutes with projection along the common subspace. -/
theorem complementChange_projection (P U W : Submodule F A)
    (hPU : IsCompl P U) (hPW : IsCompl P W) (x : A) :
    complementChange P U W hPU hPW (U.projectionOnto P hPU.symm x) =
      W.projectionOnto P hPW.symm x := by
  change (P.quotientEquivOfIsCompl W hPW)
    ((P.quotientEquivOfIsCompl U hPU).symm
      ((P.quotientEquivOfIsCompl U hPU) (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Coordinates in which three mutually complementary subspaces are
the first axis, the second axis, and the diagonal. -/
noncomputable def threeComplementCoordinates (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) :
    A ≃ₗ[F] (W × W) :=
  (U.prodEquivOfIsCompl V hUV).symm.trans
    ((complementChange V U W hUV.symm hVW).prodCongr
      (complementChange U V W hUV hUW))

/-- The coordinate formula is a pair of projections onto the third subspace. -/
theorem threeComplementCoordinates_apply (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) (x : A) :
    threeComplementCoordinates U V W hUV hUW hVW x =
      (W.projectionOnto V hVW.symm x, W.projectionOnto U hUW.symm x) := by
  simp only [threeComplementCoordinates, LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply, LinearEquiv.prodCongr_apply,
    complementChange_projection]

/-- The first original subspace is exactly the first coordinate axis. -/
theorem threeComplementCoordinates_mem_first (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) (x : A) :
    (threeComplementCoordinates U V W hUV hUW hVW x).2 = 0 ↔ x ∈ U := by
  rw [threeComplementCoordinates_apply]
  exact Submodule.projectionOnto_apply_eq_zero_iff hUW.symm

/-- The second original subspace is exactly the second coordinate axis. -/
theorem threeComplementCoordinates_mem_second (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) (x : A) :
    (threeComplementCoordinates U V W hUV hUW hVW x).1 = 0 ↔ x ∈ V := by
  rw [threeComplementCoordinates_apply]
  exact Submodule.projectionOnto_apply_eq_zero_iff hVW.symm

/-- The third original subspace maps to the diagonal, point by point. -/
theorem threeComplementCoordinates_diagonal (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) (w : W) :
    threeComplementCoordinates U V W hUV hUW hVW w = (w, w) := by
  rw [threeComplementCoordinates_apply]
  simp only [Submodule.projectionOnto_apply_left]

/-- Membership in the third subspace is equivalent to equality of the two coordinates. -/
theorem threeComplementCoordinates_mem_diagonal (U V W : Submodule F A)
    (hUV : IsCompl U V) (hUW : IsCompl U W) (hVW : IsCompl V W) (x : A) :
    (threeComplementCoordinates U V W hUV hUW hVW x).1 =
      (threeComplementCoordinates U V W hUV hUW hVW x).2 ↔ x ∈ W := by
  constructor
  · intro hx
    let w := (threeComplementCoordinates U V W hUV hUW hVW x).1
    have he : threeComplementCoordinates U V W hUV hUW hVW x =
        threeComplementCoordinates U V W hUV hUW hVW (w : A) := by
      rw [threeComplementCoordinates_diagonal]
      exact Prod.ext rfl hx.symm
    exact ((threeComplementCoordinates U V W hUV hUW hVW).injective he) ▸ w.property
  · intro hx
    have he := threeComplementCoordinates_diagonal U V W hUV hUW hVW ⟨x, hx⟩
    exact congrArg Prod.fst he |>.trans (congrArg Prod.snd he).symm

/-- Three two-dimensional mutually complementary subspaces have the usual
axis/axis/diagonal normal form in four scalar coordinates. -/
theorem three_skew_lines_coordinate_normal_form [FiniteDimensional F A]
    (U V W : Submodule F A) (hUV : IsCompl U V) (hUW : IsCompl U W)
    (hVW : IsCompl V W) (hW : Module.finrank F W = 2) :
    ∃ e : A ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      (∀ x, (e x).2 = 0 ↔ x ∈ U) ∧
      (∀ x, (e x).1 = 0 ↔ x ∈ V) ∧
      (∀ x, (e x).1 = (e x).2 ↔ x ∈ W) := by
  let b := (Module.finBasisOfFinrankEq F W hW).equivFun
  let c := threeComplementCoordinates U V W hUV hUW hVW
  refine ⟨c.trans (b.prodCongr b), ?_, ?_, ?_⟩
  · intro x
    change b (c x).2 = 0 ↔ x ∈ U
    rw [map_eq_zero_iff b b.injective]
    exact threeComplementCoordinates_mem_first U V W hUV hUW hVW x
  · intro x
    change b (c x).1 = 0 ↔ x ∈ V
    rw [map_eq_zero_iff b b.injective]
    exact threeComplementCoordinates_mem_second U V W hUV hUW hVW x
  · intro x
    change b (c x).1 = b (c x).2 ↔ x ∈ W
    rw [b.injective.eq_iff]
    exact threeComplementCoordinates_mem_diagonal U V W hUV hUW hVW x

end DimensionFourDependence
