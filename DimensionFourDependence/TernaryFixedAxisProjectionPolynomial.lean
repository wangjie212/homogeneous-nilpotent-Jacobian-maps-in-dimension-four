import DimensionFourDependence.Defs

/-! # Original projection relations become univariate equations with nonzero constant term -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable (K : Type*) [Field K]
local notation "R₀" => MvPolynomial (Fin 3) K
local notation "A₀" => MvPolynomial (Fin 1) K

/-- The fixed source coefficient ring uses exactly coordinate zero of the original three-variable source. -/
noncomputable def ternaryFixedAxisCoefficientMap : A₀ →ₐ[K] R₀ :=
  rename (![0] : Fin 1 → Fin 3)

theorem ternaryFixedAxisCoefficientMap_injective : Function.Injective (ternaryFixedAxisCoefficientMap K) :=
  rename_injective _ (by decide : Function.Injective (![0] : Fin 1 → Fin 3))

/-- The actual source polynomial obtained by inserting the active
output in a polynomial over the one fixed source-coordinate function. -/
noncomputable def ternaryFixedAxisProjectionEvaluate (F : R₀) : Polynomial A₀ →ₐ[K] R₀ :=
  ((Polynomial.aeval F).restrictScalars K).comp (Polynomial.mapAlgHom (ternaryFixedAxisCoefficientMap K))

theorem ternaryFixedAxisProjectionEvaluate_C (F : R₀) (a : A₀) :
    ternaryFixedAxisProjectionEvaluate K F (Polynomial.C a) = ternaryFixedAxisCoefficientMap K a := by
  simp [ternaryFixedAxisProjectionEvaluate]

theorem ternaryFixedAxisProjectionEvaluate_X (F : R₀) :
    ternaryFixedAxisProjectionEvaluate K F Polynomial.X = F := by
  simp [ternaryFixedAxisProjectionEvaluate]

/-- Separating the active variable of the original three-variable
relation preserves its full original-source evaluation. -/
theorem ternaryFixedAxisProjectionEvaluate_finSuccEquiv (F : R₀) (R : MvPolynomial (Fin 2) K) :
    ternaryFixedAxisProjectionEvaluate K F (finSuccEquiv K 1 R) = aeval ![F, X 0] R := by
  have he : (ternaryFixedAxisProjectionEvaluate K F).comp (finSuccEquiv K 1).toAlgHom =
      aeval (![F, X 0] : Fin 2 → R₀) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ternaryFixedAxisProjectionEvaluate, finSuccEquiv_X_zero]
    · simp only [AlgHom.comp_apply, aeval_X, Matrix.cons_val_succ]
      change ternaryFixedAxisProjectionEvaluate K F (finSuccEquiv K 1 (X j.succ)) = ![X 0] j
      rw [finSuccEquiv_X_succ, ternaryFixedAxisProjectionEvaluate_C]
      fin_cases j <;> simp [ternaryFixedAxisCoefficientMap]
  exact AlgHom.congr_fun he R

/-- Evaluating at the active output differs from the actual constant
coefficient by a multiple of that original output. -/
theorem ternary_active_output_divides_projection_value_sub_constant
    (F : R₀) (P : Polynomial A₀) :
    F ∣ ternaryFixedAxisProjectionEvaluate K F P - ternaryFixedAxisCoefficientMap K (P.coeff 0) := by
  have hX : (Polynomial.X : Polynomial A₀) ∣ P - Polynomial.C (P.coeff 0) :=
    Polynomial.X_dvd_iff.mpr (by simp)
  have he := map_dvd (ternaryFixedAxisProjectionEvaluate K F) hX
  simpa only [map_sub, ternaryFixedAxisProjectionEvaluate_X, ternaryFixedAxisProjectionEvaluate_C] using he

/-- Removing the actual active-variable root multiplicity constructs
a nonzero constant coefficient, while primeness and nondivisibility of
the active output preserve the original prime equation. -/
theorem ternary_prime_projection_relation_constructs_polynomial_with_nonzero_constant
    (δ F : R₀) (hδ : Prime δ) (hδF : ¬δ ∣ F)
    (R : MvPolynomial (Fin 2) K) (hR : R ≠ 0)
    (hrelation : δ ∣ aeval ![F, X 0] R) :
    ∃ P : Polynomial A₀, P.coeff 0 ≠ 0 ∧ δ ∣ ternaryFixedAxisProjectionEvaluate K F P := by
  let P := finSuccEquiv K 1 R
  have hP : P ≠ 0 := by
    intro hz
    apply hR
    apply (finSuccEquiv K 1).injective
    exact hz.trans (map_zero _).symm
  obtain ⟨Q, hfactor, hnot⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  simp only [map_zero, sub_zero] at hfactor hnot
  have hQ0 : Q.coeff 0 ≠ 0 := fun hz => hnot (Polynomial.X_dvd_iff.mpr hz)
  have hdiv : δ ∣ ternaryFixedAxisProjectionEvaluate K F P := by
    change δ ∣ ternaryFixedAxisProjectionEvaluate K F (finSuccEquiv K 1 R)
    rw [ternaryFixedAxisProjectionEvaluate_finSuccEquiv]
    exact hrelation
  rw [hfactor, map_mul, map_pow, ternaryFixedAxisProjectionEvaluate_X] at hdiv
  have hvalue : δ ∣ ternaryFixedAxisProjectionEvaluate K F Q :=
    (hδ.dvd_mul.mp hdiv).resolve_left (fun h => hδF (hδ.dvd_of_dvd_pow h))
  exact ⟨Q, hQ0, hvalue⟩

/-- The active output's membership in an actual source ideal turns
the prime equation into a nonzero equation in the one fixed original
source coordinates. No radical or pointwise replacement is used. -/
theorem ternary_prime_projection_polynomial_constructs_nonzero_fixed_plane_ideal_equation
    (δ F : R₀) (P : Polynomial A₀) (hP0 : P.coeff 0 ≠ 0)
    (hdiv : δ ∣ ternaryFixedAxisProjectionEvaluate K F P)
    (I : Ideal R₀) (hδI : δ ∈ I) (hFI : F ∈ I) :
    ternaryFixedAxisCoefficientMap K (P.coeff 0) ≠ 0 ∧
      ternaryFixedAxisCoefficientMap K (P.coeff 0) ∈ I := by
  have hnonzero : ternaryFixedAxisCoefficientMap K (P.coeff 0) ≠ 0 :=
    fun hz => hP0 (ternaryFixedAxisCoefficientMap_injective K (hz.trans (map_zero _).symm))
  obtain ⟨a, ha⟩ := hdiv
  have hvalue : ternaryFixedAxisProjectionEvaluate K F P ∈ I := by rw [ha]; exact I.mul_mem_right a hδI
  obtain ⟨b, hb⟩ := ternary_active_output_divides_projection_value_sub_constant K F P
  have hsub : ternaryFixedAxisProjectionEvaluate K F P - ternaryFixedAxisCoefficientMap K (P.coeff 0) ∈ I := by
    rw [hb]
    exact I.mul_mem_right b hFI
  have he := I.sub_mem hvalue hsub
  exact ⟨hnonzero, by simpa only [sub_sub_cancel] using he⟩

end DimensionFourDependence
