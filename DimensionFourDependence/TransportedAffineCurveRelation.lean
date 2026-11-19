import DimensionFourDependence.AffineLeadingComponentPolynomialIdentity
import DimensionFourDependence.FiberCoordinateRing
import DimensionFourDependence.LinearMonicProjectionChoice

/-! # Exact transport of the top relation under an affine chart change -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1850000

variable {L M F : Type u} [Field L] [Field M] [Field F] [Algebra L F] [Algebra M F]

/-- A relation in a new chart is a relation in the old chart after
pulling back its coefficients and its affine coordinates. -/
theorem pullback_affine_curve_relation_vanishes
    (α : L ≃+* M) (φ : F ≃+* F)
    (hα : ∀ c, φ (algebraMap L F c) = algebraMap M F (α c))
    (x y : Fin 2 → F) (g : Fin 2 → MvPolynomial (Fin 2) L)
    (hg : ∀ i, φ (aeval x (g i)) = y i)
    (Q : MvPolynomial (Fin 2) M) (hQ : aeval y Q = 0) :
    aeval x (aeval g (MvPolynomial.map α.symm.toRingHom Q)) = 0 := by
  let e : MvPolynomial (Fin 2) M →+* F := φ.toRingHom.comp
    ((aeval x : MvPolynomial (Fin 2) L →ₐ[L] F).toRingHom.comp
      ((aeval g : MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L).toRingHom.comp
        (MvPolynomial.map α.symm.toRingHom)))
  have he : e = (aeval y : MvPolynomial (Fin 2) M →ₐ[M] F).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hgc : aeval g (C (α.symm c)) = C (α.symm c) := (aeval g).commutes _
      change φ (aeval x (aeval g (MvPolynomial.map α.symm.toRingHom (C c)))) = aeval y (C c)
      rw [MvPolynomial.map_C]
      change φ (aeval x (aeval g (C (α.symm c)))) = aeval y (C c)
      rw [hgc, aeval_C, aeval_C, hα, α.apply_symm_apply]
    · intro i
      change φ (aeval x (aeval g (MvPolynomial.map α.symm.toRingHom (X i)))) = aeval y (X i)
      simpa only [MvPolynomial.map_X, aeval_X] using hg i
  apply φ.injective
  change e Q = φ 0
  rw [he, map_zero]
  exact hQ

/-- When both relations have degree two and the affine change has
injective linear part, their top forms agree up to a nonzero scalar
under that linear part. This retains the multiplicities at infinity. -/
theorem affine_chart_change_quadratic_leading_relation_associated
    (α : L ≃+* M) (φ : F ≃+* F)
    (hα : ∀ c, φ (algebraMap L F c) = algebraMap M F (α c))
    (x y : Fin 2 → F) (g : Fin 2 → MvPolynomial (Fin 2) L)
    (hg : ∀ i, φ (aeval x (g i)) = y i) (hd : ∀ i, (g i).totalDegree ≤ 1)
    (hLinear : Function.Injective (aeval (fun i => homogeneousComponent 1 (g i)) :
      MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L))
    (P : MvPolynomial (Fin 2) L) (hP : Irreducible P) (hdegP : P.totalDegree = 2)
    (hI : fiberVanishingIdeal (L := L) x = Ideal.span {P})
    (Q : MvPolynomial (Fin 2) M) (hQ : aeval y Q = 0) (hdegQ : Q.totalDegree = 2) :
    ∃ c : L, c ≠ 0 ∧
      aeval (fun i => homogeneousComponent 1 (g i))
        (homogeneousComponent 2 (MvPolynomial.map α.symm.toRingHom Q)) =
      C c * homogeneousComponent 2 P := by
  let Q₀ := MvPolynomial.map α.symm.toRingHom Q
  let B := aeval g Q₀
  have hQ₀ : Q₀.totalDegree = 2 := by
    unfold totalDegree at hdegQ ⊢
    change (MvPolynomial.map α.symm.toRingHom Q).support.sup _ = _
    rw [support_map_of_injective Q α.symm.injective]
    exact hdegQ
  have hBdeg : B.totalDegree ≤ 2 :=
    (totalDegree_aeval_le_of_affine g hd Q₀).trans hQ₀.le
  have hB : aeval x B = 0 := pullback_affine_curve_relation_vanishes α φ hα x y g hg Q hQ
  have hTop : homogeneousComponent 2 B =
      aeval (fun i => homogeneousComponent 1 (g i)) (homogeneousComponent 2 Q₀) :=
    homogeneousComponent_affine_substitution g hd Q₀ hQ₀.le
  have hB0 : B ≠ 0 := by
    intro h
    have hne : homogeneousComponent 2 Q₀ ≠ 0 := by
      have hEq := congrArg (fun d => homogeneousComponent d Q₀) hQ₀
      rw [← hEq]
      apply top_homogeneousComponent_ne_zero
      intro hz
      rw [hz, totalDegree_zero] at hQ₀
      omega
    apply hne
    apply hLinear
    rw [← hTop, h, map_zero, map_zero]
  change B ∈ fiberVanishingIdeal (L := L) x at hB
  rw [hI] at hB
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton.mp hB
  have hD0 : D ≠ 0 := by
    intro h
    exact hB0 (by rw [hD, h, mul_zero])
  have hBdeg' : B.totalDegree = 2 + D.totalDegree := by
    rw [hD, totalDegree_mul_of_isDomain hP.ne_zero hD0, hdegP]
  have hDdeg : D.totalDegree = 0 := by omega
  have hC := totalDegree_eq_zero_iff_eq_C.mp hDdeg
  have hc0 : D.coeff 0 ≠ 0 := fun h => hD0 (by rw [hC, h, map_zero])
  have he : B = C (D.coeff 0) * P :=
    hD.trans ((congrArg (fun Z => P * Z) hC).trans (mul_comm _ _))
  refine ⟨D.coeff 0, hc0, ?_⟩
  rw [← hTop, he, homogeneousComponent_C_mul]

end DimensionFourDependence
