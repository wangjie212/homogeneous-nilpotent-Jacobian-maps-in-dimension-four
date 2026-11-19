import DimensionFourDependence.SourcePencilEquation
import DimensionFourDependence.ParameterizedLinearIncidence
import DimensionFourDependence.PrimitiveMapDegree
import DimensionFourDependence.PrimitiveRationalVector

/-! # The actual homogeneous Gauss pencil degree is bounded by the primitive map degree

The independent-parameter normal relation is nonzero because the
primitive map coordinates are independent. The exact rational-parameter
kernel makes the pencil equation divide this relation. Exchanging the
source and parameter variables makes both polynomials homogeneous in
the source coordinates; divisibility then bounds their actual degrees.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- Exchanging source and parameter sends an original source polynomial
to the constant polynomial in the independent parameter. -/
theorem parameterSourceSwap_map_source (P : R) :
    parameterSourceSwap K 4 (MvPolynomial.map Polynomial.C P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C k => rw [MvPolynomial.map_C, parameterSourceSwap_C_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.map_X, map_mul, hp, parameterSourceSwap_X, Polynomial.C_mul]

/-- The actual independent-parameter pairing of a polynomial covector
with the polynomial output coordinates. -/
noncomputable def parametricOutputPairing (v : Fin 4 → Polynomial K) (P : Fin 4 → R) : Polynomial R :=
  ∑ i, Polynomial.map MvPolynomial.C (v i) * Polynomial.C (P i)

/-- Its parameter coefficients are the original constant linear
combinations of the output coordinates. -/
theorem parametricOutputPairing_coeff (v : Fin 4 → Polynomial K) (P : Fin 4 → R) (m : ℕ) :
    (parametricOutputPairing v P).coeff m = ∑ i, (v i).coeff m • P i := by
  simp [parametricOutputPairing, MvPolynomial.smul_eq_C_mul]

/-- Independent output coordinates and a nonzero covector give a
genuinely nonzero independent-parameter pairing. -/
theorem parametricOutputPairing_ne_zero
    (v : Fin 4 → Polynomial K) (hv : v ≠ 0) (P : Fin 4 → R)
    (hP : LinearIndependent K P) : parametricOutputPairing v P ≠ 0 := by
  intro hz
  apply hv
  funext i
  apply Polynomial.ext
  intro m
  have hc := congrArg (fun Q : Polynomial R => Q.coeff m) hz
  rw [parametricOutputPairing_coeff, Polynomial.coeff_zero] at hc
  have hcoef := Fintype.linearIndependent_iff.mp hP (fun j => (v j).coeff m) hc i
  exact hcoef

/-- Evaluation of the parameter pairing in the actual source fraction
field gives its actual covector-output pairing. -/
theorem parametricOutputPairing_eval_fraction
    (v : Fin 4 → Polynomial K) (P : Fin 4 → R) (t : F) :
    Polynomial.eval₂ (algebraMap R F) t (parametricOutputPairing v P) =
      ∑ i, Polynomial.aeval t (v i) * algebraMap R F (P i) := by
  simp only [parametricOutputPairing, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_map, Polynomial.eval₂_C]
  rfl

/-- A reduced homogeneous pencil equation dividing an actual nonzero
normal-output pairing has degree at most the output-map degree. -/
theorem homogeneous_pencil_degree_le_map_degree_of_parameter_relation
    (p q : R) {e : ℕ} (hq : q ≠ 0) (hpH : p.IsHomogeneous e) (hqH : q.IsHomogeneous e)
    (hrel : IsRelPrime p q) (P : Fin 4 → R) {D : ℕ} (hP : IsHomogMap P D)
    (hindP : LinearIndependent K P) (v : Fin 4 → Polynomial K) (hv : v ≠ 0)
    (hsection : (∑ i, Polynomial.aeval (algebraMap R F p / algebraMap R F q) (v i) *
      algebraMap R F (P i)) = 0) : e ≤ D := by
  let L : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.map Polynomial.C p - MvPolynomial.C Polynomial.X * MvPolynomial.map Polynomial.C q
  let G : MvPolynomial (Fin 4) (Polynomial K) :=
    ∑ i, MvPolynomial.C (v i) * MvPolynomial.map Polynomial.C (P i)
  have hL : parameterSourceSwap K 4 L = sourcePencilEquation p q := by
    simp only [L, map_sub, map_mul, parameterSourceSwap_map_source, parameterSourceSwap_C_X,
      sourcePencilEquation, Polynomial.C_neg]
    ring
  have hG : parameterSourceSwap K 4 G = parametricOutputPairing v P := by
    simp only [G, map_sum, map_mul, parameterSourceSwap_C, parameterSourceSwap_map_source,
      parametricOutputPairing]
  have hdiv : sourcePencilEquation p q ∣ parametricOutputPairing v P :=
    (sourcePencilEquation_dvd_iff_eval_fraction_zero p q hq hrel _).mpr
      ((parametricOutputPairing_eval_fraction v P _).trans hsection)
  obtain ⟨Q, hQ⟩ := hdiv
  have hLG : L ∣ G := by
    refine ⟨(parameterSourceSwap K 4).symm Q, ?_⟩
    apply (parameterSourceSwap K 4).injective
    rw [map_mul, hL, hG, AlgEquiv.apply_symm_apply]
    exact hQ
  have hL0 : L ≠ 0 := by
    intro hz
    have hh := congrArg (parameterSourceSwap K 4) hz
    rw [hL, map_zero] at hh
    exact (sourcePencilEquation_irreducible p q hq hrel).ne_zero hh
  have hG0 : G ≠ 0 := by
    intro hz
    have hh := congrArg (parameterSourceSwap K 4) hz
    rw [hG, map_zero] at hh
    exact parametricOutputPairing_ne_zero v hv P hindP hh
  have hLH : L.IsHomogeneous e :=
    (hpH.map Polynomial.C).sub ((hqH.map Polynomial.C).C_mul Polynomial.X)
  have hGH : G.IsHomogeneous D := by
    apply IsHomogeneous.sum
    intro i _
    exact ((hP i).map Polynomial.C).C_mul (v i)
  have hb := totalDegree_le_of_dvd_of_isDomain hLG hG0
  rwa [hLH.totalDegree hL0, hGH.totalDegree hG0] at hb

variable [CharZero K]

/-- The actual Gauss parameter's homogeneous pencil degree is bounded
by every homogeneous scalar-free presentation degree of the original
nonplanar map. Numerator, denominator and the bound are constructed. -/
theorem actual_gauss_parameter_pencil_degree_le_primitive_degree
    (H : Fin 4 → R) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (g : R) (hg : g ≠ 0) (P : Fin 4 → R) {D : ℕ} (hP : IsHomogMap P D)
    (hHP : H = fun i => g * P i) :
    ∃ p q : R, ∃ E : ℕ, 0 < E ∧ E ≤ D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous E ∧ q.IsHomogeneous E ∧ IsRelPrime p q ∧
      gaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q := by
  let f := gaussParameterSourceHom H I e
  let w := gaussParameterNormal H I e
  have ha : rationalImageNormal H I.equation (imageNormalPivot H I) ≠ 0 := imageNormalPivot_ne_zero H I
  have hw0 : w ≠ 0 := by
    intro hz
    have he := gaussParameterSourceHom_normal H I e (imageNormalPivot H I)
    change f (w (imageNormalPivot H I)) = _ at he
    rw [hz, Pi.zero_apply, map_zero, div_self ha] at he
    exact zero_ne_one he
  obtain ⟨v, hv, _, s, hs, hwrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hsF : f s ≠ 0 := by
    intro hz
    apply hs
    have he : f s = f 0 := by rw [hz, map_zero]
    exact f.injective he
  have hrep (i : Fin 4) : f (w i) = f s * Polynomial.aeval (f RatFunc.X) (v i) := by
    rw [hwrep i, map_mul, rational_function_algHom_polynomial_value]
  have hgF : algebraMap R F g ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hg
  have hHEuler := I.normalized_normal_dot_output_eq_zero H hd hH
  have hPEuler : (∑ i, f (w i) * algebraMap R F (P i)) = 0 := by
    have hh : algebraMap R F g * (∑ i, f (w i) * algebraMap R F (P i)) = 0 := by
      calc
        _ = (fun i => rationalImageNormal H I.equation i /
            rationalImageNormal H I.equation (imageNormalPivot H I)) ⬝ᵥ
            (fun i => algebraMap R F (H i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only
          have hi : algebraMap R F (H i) = algebraMap R F g * algebraMap R F (P i) := by
            rw [congrFun hHP i, map_mul]
          rw [hi, show f (w i) = _ from gaussParameterSourceHom_normal H I e i]
          ring
        _ = 0 := hHEuler
    exact (mul_eq_zero.mp hh).resolve_left hgF
  have hsection : (∑ i, Polynomial.aeval (f RatFunc.X) (v i) * algebraMap R F (P i)) = 0 := by
    have hh : f s * (∑ i, Polynomial.aeval (f RatFunc.X) (v i) * algebraMap R F (P i)) = 0 := by
      rw [Finset.mul_sum]
      convert hPEuler using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hrep]
      ring
    exact (mul_eq_zero.mp hh).resolve_left hsF
  have hindP : ¬ ComponentsDependent P := by
    intro hp
    apply hind
    rw [hHP]
    exact componentsDependent_common_factor P g hp
  obtain ⟨p, q, E, hE, hp, hq, hpH, hqH, hrel, he⟩ :=
    actual_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  have hb : E ≤ D := homogeneous_pencil_degree_le_map_degree_of_parameter_relation p q hq hpH hqH hrel P hP
    (linearIndependent_of_componentsIndependent P hindP) v hv (by rw [← he]; exact hsection)
  exact ⟨p, q, E, hE, hb, hp, hq, hpH, hqH, hrel, he⟩

/-- From the original nonplanar homogeneous map and its actual
one-dimensional Gauss image, construct all primitive factorization and
homogeneous pencil data with both degree bounds from Section 4.2. -/
theorem exists_actual_gauss_pencil_and_primitive_degree_bounds
    (H : Fin 4 → R) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (g : R) (P : Fin 4 → R) (c : ℕ)
      (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
        (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (p q : R) (E : ℕ),
      c ≤ d - 2 ∧ g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧
      IsPrimitiveVec P ∧ H = (fun i => g * P i) ∧ 2 ≤ d - c ∧
      0 < E ∧ E ≤ d - c ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous E ∧ q.IsHomogeneous E ∧ IsRelPrime p q ∧
      gaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q := by
  obtain ⟨g, P, c, hc, hg, hgh, hP, hprim, hHP, hD⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  obtain ⟨e⟩ := actual_gauss_curve_rational_function_field H I hGauss
  obtain ⟨p, q, E, hE, hED, hp, hq, hpH, hqH, hrel, he⟩ :=
    actual_gauss_parameter_pencil_degree_le_primitive_degree H hd hH hind I e g hg P hP hHP
  exact ⟨g, P, c, e, p, q, E, hc, hg, hgh, hP, hprim, hHP, hD, hE, hED, hp, hq, hpH, hqH, hrel, he⟩

end DimensionFourDependence
