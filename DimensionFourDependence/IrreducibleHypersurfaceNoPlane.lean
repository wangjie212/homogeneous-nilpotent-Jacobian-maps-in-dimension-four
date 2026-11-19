import DimensionFourDependence.LinearPolynomialCoordinates
import DimensionFourDependence.ImageHypersurface

/-! # An irreducible nonlinear hypersurface contains no projective plane

A plane projection gives a rank-three linear polynomial map. Its relation
prime has height one. If the irreducible hypersurface equation vanished
on the plane, it would generate that prime and divide the plane's nonzero
linear equation. The degree comparison excludes every degree at least two.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F] [CharZero F]

/-- A homogeneous irreducible equation containing a projective plane must be linear. -/
theorem irreducible_homogeneous_equation_containing_plane_degree_le_one
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hR : R.IsHomogeneous d) (hirred : Irreducible R)
    (T : Submodule F (Fin 4 → F)) (hT : finrank F T = 3)
    (hcontain : ∀ x ∈ T, aeval x R = 0) : d ≤ 1 := by
  classical
  obtain ⟨N, hTN⟩ := Submodule.exists_isCompl T
  let π := T.projection N hTN
  let A := LinearMap.toMatrix' π
  let H := linearPolynomialMap A
  have hArank : A.rank = 3 := by
    change finrank F (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' π))) = 3
    rw [Matrix.toLin'_toMatrix', Submodule.range_projection]
    exact hT
  have hHrank : polyRank (jac H) = 3 := by
    rw [polyRank_jac_linearPolynomialMap]
    exact hArank
  have hHeval (x : Fin 4 → F) : (fun i => aeval x (H i)) = π x := by
    rw [linearPolynomialMap_aeval]
    change (Matrix.toLin' (LinearMap.toMatrix' π)) x = π x
    rw [Matrix.toLin'_toMatrix']
  have hrestriction (P : MvPolynomial (Fin 4) F) (hP : ∀ x ∈ T, aeval x P = 0) : aeval H P = 0 := by
    apply MvPolynomial.funext
    intro x
    change aeval x (aeval H P) = aeval x (0 : MvPolynomial (Fin 4) F)
    rw [comp_aeval_apply, hHeval, map_zero]
    exact hP _ (T.projection_apply_mem hTN x)
  have hRmem : R ∈ imageRelationIdeal H := hrestriction R hcontain
  have hheight : (imageRelationIdeal H).height = 1 := by
    apply le_antisymm (imageRelationIdeal_height_le_one H hHrank)
    apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have hbot := Ideal.height_eq_zero_iff_eq_bot.mp hz
    rw [hbot, Ideal.mem_bot] at hRmem
    exact hirred.ne_zero hRmem
  have hideal : imageRelationIdeal H = Ideal.span {R} :=
    Ideal.eq_span_singleton_of_height_eq_one hheight hRmem hirred.prime
  have hTproper : T < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro hz
    rw [hz, finrank_top, Module.finrank_pi, Fintype.card_fin] at hT
    omega
  obtain ⟨f, hf, hTf⟩ := T.exists_dual_map_eq_bot_of_lt_top hTproper inferInstance
  let f₁ : (Fin 4 → F) →ₗ[F] (Fin 1 → F) := LinearMap.pi (fun _ => f)
  let B := LinearMap.toMatrix' f₁
  let L := linearPolynomialMap B 0
  have hLeval (x : Fin 4 → F) : aeval x L = f x := by
    have he := congrFun (linearPolynomialMap_aeval B x) 0
    have hB : B *ᵥ x = f₁ x := by
      change (Matrix.toLin' (LinearMap.toMatrix' f₁)) x = f₁ x
      rw [Matrix.toLin'_toMatrix']
    rw [hB] at he
    exact he
  have hL0 : L ≠ 0 := by
    intro hz
    apply hf
    apply LinearMap.ext
    intro x
    have he := hLeval x
    rw [hz, map_zero] at he
    exact he.symm
  have hLhom : L.IsHomogeneous 1 := linearPolynomialMap_homogeneous B 0
  have hLmem : L ∈ imageRelationIdeal H := by
    apply hrestriction L
    intro x hx
    rw [hLeval]
    have hm : f x ∈ T.map f := ⟨x, hx, rfl⟩
    rw [hTf, Submodule.mem_bot] at hm
    exact hm
  rw [hideal, Ideal.mem_span_singleton] at hLmem
  obtain ⟨q, hq⟩ := hLmem
  have hq0 : q ≠ 0 := by
    intro hz
    exact hL0 (by rw [hq, hz, mul_zero])
  have hdeg := congrArg MvPolynomial.totalDegree hq
  rw [hLhom.totalDegree hL0, totalDegree_mul_of_isDomain hirred.ne_zero hq0,
    hR.totalDegree hirred.ne_zero] at hdeg
  omega

/-- An irreducible homogeneous hypersurface of degree at least two contains no plane. -/
theorem irreducible_homogeneous_hypersurface_contains_no_plane
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 2 ≤ d)
    (hR : R.IsHomogeneous d) (hirred : Irreducible R)
    (T : Submodule F (Fin 4 → F)) (hT : finrank F T = 3) :
    ¬ ∀ x ∈ T, aeval x R = 0 := by
  intro hcontain
  have he := irreducible_homogeneous_equation_containing_plane_degree_le_one R hR hirred T hT hcontain
  omega

end DimensionFourDependence
