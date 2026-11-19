import DimensionFourDependence.TernaryConicHessianAssociation
import DimensionFourDependence.ConstantCovectorDirectionSeparation

/-! # Original constant covectors select transverse conic charts -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 2200000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "Out₂" => (ternaryRationalOutputPair (K := K))
local notation "Coeff" => (coefficientField (K := K))

noncomputable abbrev TernaryConicWitness.liftDirection
    {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) {A : Type v} [Field A] [Algebra (Coeff (Out₂ H)) A]
    (e : Fin 2 → A) : Fin 3 → A :=
  ![e 0, e 1, algebraMap (Coeff (Out₂ H)) A (W.gradient 0) * e 0 + algebraMap (Coeff (Out₂ H)) A (W.gradient 1) * e 1]

/-- The first two transformed directions are the evaluations of the
first two original frame rows on the old embedded direction. -/
theorem TernaryConicWitness.restrictedFrame_mulVec_coordinate
    {H : Fin 3 → R₃} {A : Type v} [Field A] [Algebra (Coeff (Out₂ H)) A] [Algebra K A]
    [IsScalarTower K (Coeff (Out₂ H)) A]
    (W : TernaryConicWitness (K := K) H) (S : Matrix (Fin 3) (Fin 3) K)
    (e : Fin 2 → A) (i : Fin 2) :
    ((W.restrictedFrame S).map (algebraMap (Coeff (Out₂ H)) A) *ᵥ e) i =
      aeval (W.liftDirection e) (linearFormPolynomial (S i.castSucc)) := by
  change (∑ j, algebraMap (Coeff (Out₂ H)) A (W.restrictedCovector (S i.castSucc) j) * e j) = _
  rw [Fin.sum_univ_two]
  exact (ternaryGraphRestrictedCovector_direction_value (W.gradient 0) (W.gradient 1)
    (S i.castSucc) e).symm

/-- A separating pair of original constant covectors constructs a
frame that projects the direction plane isomorphically. -/
theorem TernaryConicWitness.separating_covectors_construct_transverse_frame
    {H : Fin 3 → R₃} {A : Type v} [Field A] [Algebra (Coeff (Out₂ H)) A] [Algebra K A]
    [IsScalarTower K (Coeff (Out₂ H)) A]
    (W : TernaryConicWitness (K := K) H) (e : Fin 2 → A)
    (l r : Fin 3 → K) (hl : l ≠ 0)
    (h₀ : aeval (W.liftDirection e) (linearFormPolynomial l) = 0)
    (h₁ : aeval (W.liftDirection e) (linearFormPolynomial r) ≠ 0) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      S 0 = l ∧ S 1 = r ∧ (W.restrictedFrame S).det ≠ 0 := by
  have hev (c : Fin 3 → K) : aeval (W.liftDirection e) (linearFormPolynomial c) =
      ∑ j, algebraMap K A (c j) * W.liftDirection e j := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  have hLI := constant_covectors_independent_of_separating_direction l r hl (W.liftDirection e)
    (by simpa only [hev] using h₀) (by simpa only [hev] using h₁)
  let p : Fin 2 ↪ Fin 3 := ⟨Fin.castSucc, Fin.castSucc_injective 2⟩
  obtain ⟨T, S, hTS, hST, hS⟩ := independent_covector_pair_constructs_specified_rows ![l,r] hLI p
  have hS₀ : S 0 = l := funext (hS 0)
  have hS₁ : S 1 = r := funext (hS 1)
  have hB : W.restrictedFrame S = (![W.restrictedCovector l, W.restrictedCovector r] :
      Matrix (Fin 2) (Fin 2) (Coeff (Out₂ H))) := by
    funext i
    fin_cases i
    · change W.restrictedCovector (S 0) = W.restrictedCovector l
      rw [hS₀]
    · change W.restrictedCovector (S 1) = W.restrictedCovector r
      rw [hS₁]
  refine ⟨T, S, hTS, hST, hS₀, hS₁, ?_⟩
  rw [hB]
  apply binary_row_matrix_det_ne_zero_of_separating_direction
    (W.restrictedCovector l) (W.restrictedCovector r) (W.restrictedCovector_ne_zero l hl) e
  · exact (ternaryGraphRestrictedCovector_direction_value (W.gradient 0) (W.gradient 1) l e).symm.trans h₀
  · intro hz
    exact h₁ ((ternaryGraphRestrictedCovector_direction_value (W.gradient 0) (W.gradient 1) r e).trans hz)

variable [IsAlgClosed K]

/-- Every zero of the Hessian at infinity lies in one of the
constant direction planes of the original leading homogeneous map. -/
theorem TernaryConicWitness.hessian_direction_has_constant_covector
    {H : Fin 3 → R₃} {A : Type v} [Field A] [Algebra (Coeff (Out₂ H)) A] [Algebra K A]
    [IsScalarTower K (Coeff (Out₂ H)) A]
    (W : TernaryConicWitness (K := K) H) (e : Fin 2 → A)
    (hz : aeval e (quadraticFormPolynomial W.hessian) = 0) :
    ∃ l : Fin 3 → K, l ≠ 0 ∧ aeval (W.liftDirection e) (linearFormPolynomial l) = 0 := by
  let Y := ternaryRationalOutputPair (K := K) H
  obtain ⟨C₀, hC, hCover⟩ := ternary_graph_generator_direction_cover.{u, v}
    H W.origin_zero W.components_independent W.nilpotent Y W.independent (fun _ => rfl)
    W.lastOutput W.lastOutput_value W.planeConstant W.planeConstant_value W.equation
    W.relation_irreducible.ne_zero W.relation_ideal
  have h : aeval e (homogeneousComponent W.equation.totalDegree W.equation) = 0 := by
    have hd : W.equation.totalDegree = 2 := W.relation_degree
    rw [hd, W.leading_equation, map_mul, hz, mul_zero]
  obtain ⟨l, hl, hv⟩ := hCover A e h
  exact ⟨l, hC l hl, hv⟩

end DimensionFourDependence
