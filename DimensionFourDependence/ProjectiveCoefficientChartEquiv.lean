import DimensionFourDependence.DehomogenizedBaseChange
import DimensionFourDependence.ComponentGenericPoint

/-! # The actual projective chart after coefficient extension is the tensor chart

For a homogeneous principal source relation whose extended ideal is
prime, the actual extended projective ratio chart is exactly the
coefficient extension of the original ratio chart. The identification
uses the same original equation and its actual dehomogenizations.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E F : Type u} [Field C] [Field E] [Field F] [Algebra C E] [Algebra C F]
  (x : Fin 4 → F) (G : MvPolynomial (Fin 4) C)
  {D : ℕ} (hG : G.IsHomogeneous D)
  (hker : RingHom.ker (aeval x).toRingHom = Ideal.span {G})

local notation "J" => extendCoefficientIdeal E (fiberVanishingIdeal (L := C) x)

variable [(extendCoefficientIdeal E (fiberVanishingIdeal (L := C) x)).IsPrime]

/-- The quotient by the three actual ratio relations is identified with
the original full chart, through evaluation of those same ratios. -/
noncomputable def projectiveRatioQuotientEquiv
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) C))
    (hI : fiberVanishingIdeal (L := C)
      (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) = I) :
    (MvPolynomial (Fin 3) C ⧸ I) ≃ₐ[C]
      projectiveCoordinateChartAlgebra (C := C) x (s.symm none) :=
  (Ideal.quotientEquivAlgOfEq C hI.symm).trans
    ((fiberCoordinateQuotientEquiv _).trans
      (Subalgebra.equivOfEq _ _ (projective_three_ratio_algebra_eq_full x s ha)))

/-- The quotient chart identification evaluates each original polynomial
at the actual ratios, including its original coefficients. -/
theorem projectiveRatioQuotientEquiv_mk
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) C))
    (hI : fiberVanishingIdeal (L := C)
      (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) = I)
    (P : MvPolynomial (Fin 3) C) :
    ((projectiveRatioQuotientEquiv x s ha I hI (Ideal.Quotient.mk I P)) : F) =
      aeval (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) P := by
  simp [projectiveRatioQuotientEquiv, fiberCoordinateQuotientEquiv, fiberVanishingIdeal,
    Ideal.quotientKerEquivRange, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The original ratio has precisely its original variable class in the
quotient presentation. -/
theorem projectiveRatioQuotientEquiv_symm_ratio
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) C))
    (hI : fiberVanishingIdeal (L := C)
      (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) = I)
    (i : Fin 3) :
    (projectiveRatioQuotientEquiv x s ha I hI).symm
      (projectiveChartTransition (C := C) x (s.symm none) (s.symm (some i))) =
      Ideal.Quotient.mk I (X i) := by
  apply (projectiveRatioQuotientEquiv x s ha I hI).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [projectiveRatioQuotientEquiv_mk, aeval_X]
  rfl

/-- A source coordinate outside the actual extended prime is nonzero
on its canonical fraction-field generic point. -/
theorem extended_prime_quotient_coordinate_ne_zero (a : Fin 4) (ha : X a ∉ J) :
    primeQuotientCoordinate J a ≠ 0 := by
  intro hz
  apply ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (MvPolynomial (Fin 4) E ⧸ J) (FractionRing (MvPolynomial (Fin 4) E ⧸ J))
  simpa only [primeQuotientCoordinate, map_zero] using hz

include hker in
/-- The extended generic point has exactly the original extended principal equation. -/
theorem extended_prime_quotient_coordinate_principal_kernel :
    RingHom.ker (aeval (primeQuotientCoordinate J)).toRingHom =
      Ideal.span {MvPolynomial.map (algebraMap C E) G} := by
  change fiberVanishingIdeal (L := E) (primeQuotientCoordinate J) = _
  rw [primeQuotientCoordinate_relations]
  change extendCoefficientIdeal E (RingHom.ker (aeval x).toRingHom) = _
  simp only [extendCoefficientIdeal, hker, Ideal.map_span, Set.image_singleton]

/-- The canonical extended projective ratio ring is the actual scalar
extension of the original ratio ring. -/
noncomputable def projectiveCoefficientChartEquiv
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0) (haE : X (s.symm none) ∉ J) :
    E ⊗[C] projectiveCoordinateChartAlgebra (C := C) x (s.symm none) ≃ₐ[E]
      projectiveCoordinateChartAlgebra (C := E) (primeQuotientCoordinate J) (s.symm none) := by
  let δ := projectiveDehomogenize (rename s G)
  let δE := projectiveDehomogenize (rename s (MvPolynomial.map (algebraMap C E) G))
  let z := primeQuotientCoordinate J
  have hz : z (s.symm none) ≠ 0 := extended_prime_quotient_coordinate_ne_zero x (s.symm none) haE
  have horig : fiberVanishingIdeal (L := C)
      (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) = Ideal.span {δ} :=
    homogeneous_principal_source_chart_relation_ideal (fun j => x (s.symm j)) ha
      (rename s G) hG.rename_isHomogeneous (reindexed_source_principal_kernel x G hker s)
  have hnew : fiberVanishingIdeal (L := E)
      (fun i : Fin 3 => z (s.symm (some i)) / z (s.symm none)) = Ideal.span {δE} :=
    homogeneous_principal_source_chart_relation_ideal (fun j => z (s.symm j)) hz
      (rename s (MvPolynomial.map (algebraMap C E) G))
      (hG.map (algebraMap C E)).rename_isHomogeneous
      (reindexed_source_principal_kernel z _ (extended_prime_quotient_coordinate_principal_kernel x G hker) s)
  let b : (MvPolynomial (Fin 3) C ⧸ Ideal.span {δ}) ≃ₐ[C]
      projectiveCoordinateChartAlgebra (C := C) x (s.symm none) :=
    projectiveRatioQuotientEquiv x s ha _ horig
  let bE : (MvPolynomial (Fin 3) E ⧸ Ideal.span {δE}) ≃ₐ[E]
      projectiveCoordinateChartAlgebra (C := E) z (s.symm none) :=
    projectiveRatioQuotientEquiv z s hz _ hnew
  have hid : extendCoefficientIdeal E (Ideal.span {δ}) = Ideal.span {δE} := by
    simp only [extendCoefficientIdeal, Ideal.map_span, Set.image_singleton]
    congr 1
    dsimp only [δ, δE]
    rw [← projectiveDehomogenize_map_coefficients, MvPolynomial.map_rename]
  let t : E ⊗[C] projectiveCoordinateChartAlgebra (C := C) x (s.symm none) ≃ₐ[E]
      E ⊗[C] (MvPolynomial (Fin 3) C ⧸ Ideal.span {δ}) :=
    { (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[C] E) b.symm).toRingEquiv with
      commutes' := fun c => by simp }
  exact t.trans
    ((polynomialQuotientBaseChangeEquiv E (Ideal.span {δ})).trans
      ((Ideal.quotientEquivAlgOfEq E hid).trans bE))

/-- Coefficient extension sends each of the three nontrivial original
coordinate ratios to the same ratio at the extended generic point. -/
theorem projectiveCoefficientChartEquiv_tmul_ratio_some
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0)
    (haE : X (s.symm none) ∉ J) (i : Fin 3) :
    projectiveCoefficientChartEquiv x G hG hker s ha haE
      ((1 : E) ⊗ₜ[C]
        projectiveChartTransition (C := C) x (s.symm none) (s.symm (some i))) =
      projectiveChartTransition (C := E) (primeQuotientCoordinate J)
        (s.symm none) (s.symm (some i)) := by
  apply Subtype.ext
  simp only [projectiveCoefficientChartEquiv, AlgEquiv.trans_apply,
    AlgEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
    AlgEquiv.coe_toEquiv, AlgEquiv.coe_toAlgHom,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_refl, id_eq,
    projectiveRatioQuotientEquiv_symm_ratio,
    polynomialQuotientBaseChangeEquiv_tmul, one_smul,
    Ideal.quotientEquivAlgOfEq_mk, projectiveRatioQuotientEquiv_mk,
    MvPolynomial.map_X, aeval_X]
  rfl

/-- The actual coefficient-extension chart map preserves every original
ratio, including the distinguished coordinate equal to one. -/
theorem projectiveCoefficientChartEquiv_tmul_ratio
    (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0)
    (haE : X (s.symm none) ∉ J) (i : Fin 4) :
    projectiveCoefficientChartEquiv x G hG hker s ha haE
      ((1 : E) ⊗ₜ[C] projectiveChartTransition (C := C) x (s.symm none) i) =
      projectiveChartTransition (C := E) (primeQuotientCoordinate J) (s.symm none) i := by
  rcases hsi : s i with _ | j
  · have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
    subst i
    have hr : projectiveChartTransition (C := C) x (s.symm none) (s.symm none) = 1 := by
      apply Subtype.ext
      exact div_self ha
    have hrE : projectiveChartTransition (C := E) (primeQuotientCoordinate J)
        (s.symm none) (s.symm none) = 1 := by
      apply Subtype.ext
      exact div_self (extended_prime_quotient_coordinate_ne_zero x _ haE)
    simp [hr, hrE, ← Algebra.TensorProduct.one_def]
  · have hi : i = s.symm (some j) := by rw [← hsi, s.symm_apply_apply]
    rw [hi]
    exact projectiveCoefficientChartEquiv_tmul_ratio_some x G hG hker s ha haE j

end DimensionFourDependence
