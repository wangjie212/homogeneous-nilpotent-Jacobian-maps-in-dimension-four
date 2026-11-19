import DimensionFourDependence.Defs

/-! # Original projection relations become univariate equations with nonzero constant term -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable (K : Type*) [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "A₀" => MvPolynomial (Fin 2) K

/-- The fixed source coefficient ring uses exactly coordinates zero
and three of the original four-variable source. -/
noncomputable def fixedPlaneCoefficientMap : A₀ →ₐ[K] R₀ :=
  rename (![0, 3] : Fin 2 → Fin 4)

theorem fixedPlaneCoefficientMap_injective : Function.Injective (fixedPlaneCoefficientMap K) :=
  rename_injective _ (by decide : Function.Injective (![0, 3] : Fin 2 → Fin 4))

/-- The actual source polynomial obtained by inserting the active
output in a polynomial over the two fixed source-coordinate functions. -/
noncomputable def fixedPlaneProjectionEvaluate (F : R₀) : Polynomial A₀ →ₐ[K] R₀ :=
  ((Polynomial.aeval F).restrictScalars K).comp (Polynomial.mapAlgHom (fixedPlaneCoefficientMap K))

theorem fixedPlaneProjectionEvaluate_C (F : R₀) (a : A₀) :
    fixedPlaneProjectionEvaluate K F (Polynomial.C a) = fixedPlaneCoefficientMap K a := by
  simp [fixedPlaneProjectionEvaluate]

theorem fixedPlaneProjectionEvaluate_X (F : R₀) :
    fixedPlaneProjectionEvaluate K F Polynomial.X = F := by
  simp [fixedPlaneProjectionEvaluate]

/-- Separating the active variable of the original three-variable
relation preserves its full original-source evaluation. -/
theorem fixedPlaneProjectionEvaluate_finSuccEquiv (F : R₀) (R : MvPolynomial (Fin 3) K) :
    fixedPlaneProjectionEvaluate K F (finSuccEquiv K 2 R) = aeval ![F, X 0, X 3] R := by
  have he : (fixedPlaneProjectionEvaluate K F).comp (finSuccEquiv K 2).toAlgHom =
      aeval (![F, X 0, X 3] : Fin 3 → R₀) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [fixedPlaneProjectionEvaluate, finSuccEquiv_X_zero]
    · simp only [AlgHom.comp_apply, aeval_X, Matrix.cons_val_succ]
      change fixedPlaneProjectionEvaluate K F (finSuccEquiv K 2 (X j.succ)) = ![X 0, X 3] j
      rw [finSuccEquiv_X_succ, fixedPlaneProjectionEvaluate_C]
      fin_cases j <;> simp [fixedPlaneCoefficientMap]
  exact AlgHom.congr_fun he R

/-- Evaluating at the active output differs from the actual constant
coefficient by a multiple of that original output. -/
theorem active_output_divides_projection_value_sub_constant
    (F : R₀) (P : Polynomial A₀) :
    F ∣ fixedPlaneProjectionEvaluate K F P - fixedPlaneCoefficientMap K (P.coeff 0) := by
  have hX : (Polynomial.X : Polynomial A₀) ∣ P - Polynomial.C (P.coeff 0) :=
    Polynomial.X_dvd_iff.mpr (by simp)
  have he := map_dvd (fixedPlaneProjectionEvaluate K F) hX
  simpa only [map_sub, fixedPlaneProjectionEvaluate_X, fixedPlaneProjectionEvaluate_C] using he

/-- Removing the actual active-variable root multiplicity constructs
a nonzero constant coefficient, while primeness and nondivisibility of
the active output preserve the original prime equation. -/
theorem prime_projection_relation_constructs_polynomial_with_nonzero_constant
    (δ F : R₀) (hδ : Prime δ) (hδF : ¬δ ∣ F)
    (R : MvPolynomial (Fin 3) K) (hR : R ≠ 0)
    (hrelation : δ ∣ aeval ![F, X 0, X 3] R) :
    ∃ P : Polynomial A₀, P.coeff 0 ≠ 0 ∧ δ ∣ fixedPlaneProjectionEvaluate K F P := by
  let P := finSuccEquiv K 2 R
  have hP : P ≠ 0 := by
    intro hz
    apply hR
    apply (finSuccEquiv K 2).injective
    exact hz.trans (map_zero _).symm
  obtain ⟨Q, hfactor, hnot⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  simp only [map_zero, sub_zero] at hfactor hnot
  have hQ0 : Q.coeff 0 ≠ 0 := fun hz => hnot (Polynomial.X_dvd_iff.mpr hz)
  have hdiv : δ ∣ fixedPlaneProjectionEvaluate K F P := by
    change δ ∣ fixedPlaneProjectionEvaluate K F (finSuccEquiv K 2 R)
    rw [fixedPlaneProjectionEvaluate_finSuccEquiv]
    exact hrelation
  rw [hfactor, map_mul, map_pow, fixedPlaneProjectionEvaluate_X] at hdiv
  have hvalue : δ ∣ fixedPlaneProjectionEvaluate K F Q :=
    (hδ.dvd_mul.mp hdiv).resolve_left (fun h => hδF (hδ.dvd_of_dvd_pow h))
  exact ⟨Q, hQ0, hvalue⟩

/-- The active output's membership in an actual source ideal turns
the prime equation into a nonzero equation in the two fixed original
source coordinates. No radical or pointwise replacement is used. -/
theorem prime_projection_polynomial_constructs_nonzero_fixed_plane_ideal_equation
    (δ F : R₀) (P : Polynomial A₀) (hP0 : P.coeff 0 ≠ 0)
    (hdiv : δ ∣ fixedPlaneProjectionEvaluate K F P)
    (I : Ideal R₀) (hδI : δ ∈ I) (hFI : F ∈ I) :
    fixedPlaneCoefficientMap K (P.coeff 0) ≠ 0 ∧
      fixedPlaneCoefficientMap K (P.coeff 0) ∈ I := by
  have hnonzero : fixedPlaneCoefficientMap K (P.coeff 0) ≠ 0 :=
    fun hz => hP0 (fixedPlaneCoefficientMap_injective K (hz.trans (map_zero _).symm))
  obtain ⟨a, ha⟩ := hdiv
  have hvalue : fixedPlaneProjectionEvaluate K F P ∈ I := by rw [ha]; exact I.mul_mem_right a hδI
  obtain ⟨b, hb⟩ := active_output_divides_projection_value_sub_constant K F P
  have hsub : fixedPlaneProjectionEvaluate K F P - fixedPlaneCoefficientMap K (P.coeff 0) ∈ I := by
    rw [hb]
    exact I.mul_mem_right b hFI
  have he := I.sub_mem hvalue hsub
  exact ⟨hnonzero, by simpa only [sub_sub_cancel] using he⟩

end DimensionFourDependence
