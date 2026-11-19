import DimensionFourDependence.TernaryGraphConic
import DimensionFourDependence.TernaryConicChartTransport
import DimensionFourDependence.TernaryGraphPairIndependence

/-! # The actual conic data for an independent ternary chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 600000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- The plane and quadratic invariants and the exact principal ideal
of the conic in a chart with two independent components. -/
structure TernaryConicWitness (H : Fin 3 → R₃) where
  origin_zero : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0
  components_independent : ¬ComponentsDependent H
  nilpotent : IsNilpotent (jac H)
  independent : AlgebraicIndependent K (ternaryRationalOutputPair (K := K) H)
  lastOutput : coefficientField (K := K) (ternaryRationalOutputPair (K := K) H)
  planeConstant : coefficientField (K := K) (ternaryRationalOutputPair (K := K) H)
  quadraticConstant : coefficientField (K := K) (ternaryRationalOutputPair (K := K) H)
  lastOutput_value : (lastOutput : F) = ι (H 2)
  planeConstant_value : (planeConstant : F) =
    ternaryGraphPlaneValue (ternaryRationalOutputPair (K := K) H) independent lastOutput
  quadraticConstant_value : (quadraticConstant : F) =
    ternaryGraphQuadraticValue (ternaryRationalOutputPair (K := K) H) independent lastOutput planeConstant
  relation_ideal : fiberVanishingIdeal (L := coefficientField (K := K) (ternaryRationalOutputPair (K := K) H))
      (fun i : Fin 2 => x i.castSucc) =
    Ideal.span {ternaryGraphQuadraticEquation (ternaryRationalOutputPair (K := K) H) independent
      lastOutput planeConstant quadraticConstant}
  relation_irreducible : Irreducible (ternaryGraphQuadraticEquation
    (ternaryRationalOutputPair (K := K) H) independent lastOutput planeConstant quadraticConstant)
  relation_degree : (ternaryGraphQuadraticEquation (ternaryRationalOutputPair (K := K) H) independent
      lastOutput planeConstant quadraticConstant).totalDegree = 2

local notation "Out₂" => (ternaryRationalOutputPair (K := K))
local notation "Coeff" => (coefficientField (K := K))

noncomputable def TernaryConicWitness.equation {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) :
    MvPolynomial (Fin 2) (Coeff (Out₂ H)) :=
  ternaryGraphQuadraticEquation (Out₂ H) W.independent W.lastOutput W.planeConstant W.quadraticConstant

noncomputable def TernaryConicWitness.gradient {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) (i : Fin 2) : (Coeff (Out₂ H)) :=
  coefficientPartial (Out₂ H) W.independent i W.lastOutput

noncomputable def TernaryConicWitness.hessian {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) :
    Matrix (Fin 2) (Fin 2) (Coeff (Out₂ H)) :=
  Matrix.of fun i j => coefficientPartial (Out₂ H) W.independent i (W.gradient j)

theorem TernaryConicWitness.hessian_symmetric {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) (i j : Fin 2) :
    W.hessian i j = W.hessian j i :=
  coefficientPartials_commute (Out₂ H) W.independent i j W.lastOutput

theorem TernaryConicWitness.equation_vanishes {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) :
    aeval (fun i : Fin 2 => x i.castSucc) W.equation = 0 := by
  change W.equation ∈ fiberVanishingIdeal (L := (Coeff (Out₂ H))) (fun i : Fin 2 => x i.castSucc)
  rw [W.relation_ideal]
  exact Ideal.subset_span (by simp [TernaryConicWitness.equation])

noncomputable def TernaryConicWitness.restrictedCovector {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H)
    (l : Fin 3 → K) : Fin 2 → (Coeff (Out₂ H)) :=
  ternaryGraphRestrictedCovector (W.gradient 0) (W.gradient 1) l

noncomputable def TernaryConicWitness.restrictedFrame {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H)
    (S : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) (Coeff (Out₂ H)) :=
  fun i => W.restrictedCovector (S i.castSucc)

theorem TernaryConicWitness.restrictedCovector_ne_zero {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H)
    (l : Fin 3 → K) (hl : l ≠ 0) : W.restrictedCovector l ≠ 0 :=
  normalized_independent_ternary_graph_restricted_covector_ne_zero H W.origin_zero
    W.components_independent (Out₂ H) W.independent (fun _ => rfl) W.lastOutput W.lastOutput_value l hl

variable [IsAlgClosed K]

/-- The exact conic invariants are constructed from the original chart. -/
theorem exists_ternary_conic_witness (H : Fin 3 → R₃)
    (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (hY : AlgebraicIndependent K (ternaryRationalOutputPair (K := K) H)) :
    Nonempty (TernaryConicWitness (K := K) H) := by
  let Y₀ := ternaryRationalOutputPair (K := K) H
  let w : coefficientField (K := K) Y₀ := ⟨ι (H 2), mem_algebraicClosure_iff.mpr
    (ternary_nilpotent_independent_pair_last_output_is_algebraic H hN hY)⟩
  obtain ⟨s, τ, hs, hτ, hI, hQ, hdeg⟩ :=
    normalized_ternary_independent_chart_constructs_invariant_conic H h0 hind hN
      Y₀ hY (fun _ => rfl) w rfl
  exact ⟨⟨h0, hind, hN, hY, w, s, τ, rfl, hs, hτ, hI, hQ, hdeg⟩⟩

/-- A transverse constant change produces a conic witness in the
changed chart, with independence of the new pair proved. -/
theorem TernaryConicWitness.rechart {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H)
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (hA : (W.restrictedFrame S).det ≠ 0) :
    Nonempty (TernaryConicWitness (K := K) (linearPolynomialConjugate T S H)) := by
  have hind := linearPolynomialConjugate_componentsIndependent T S hTS hST H W.components_independent
  have hn := linearPolynomialConjugate_nilpotent T S hTS hST H W.nilpotent
  have h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (linearPolynomialConjugate T S H i) = 0 := by
    have he := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H
      (fun _ : Fin 3 => (0 : K)) W.origin_zero
    have hz : S.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
    rw [hz] at he
    exact he
  have hp := ternary_graph_transverse_frame_first_two_outputs_independent T S hTS hST H
    (Out₂ H) W.independent (fun _ => rfl) W.lastOutput W.lastOutput_value hA
  exact exists_ternary_conic_witness _ h0 hind hn hp

end DimensionFourDependence
