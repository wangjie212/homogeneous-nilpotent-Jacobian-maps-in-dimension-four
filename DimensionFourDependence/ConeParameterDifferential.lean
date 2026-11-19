import DimensionFourDependence.TranscendentalSeparatingDerivation
import DimensionFourDependence.ConeTangentParameterObstruction

/-! # A transcendental cone parameter has a nonzero tangent differential

The separating derivation of the actual cone residue field produces the
tangent vector. No chosen tangent vector or nonzero differential is needed.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {n : ℕ}

/-- The values of an actual residue-field derivation on the original
source coordinates give the full polynomial differential. -/
theorem derivation_mappedPolynomialGradient_pairing
    (f : MvPolynomial (Fin n) K →ₐ[K] κ) (D : Derivation K κ κ)
    (p : MvPolynomial (Fin n) K) :
    D (f p) = mappedPolynomialGradient f.toRingHom p ⬝ᵥ
      (fun j => D (f (X j))) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    change D (f (algebraMap K (MvPolynomial (Fin n) K) c)) =
      ∑ i, f (pderiv i (C c)) * D (f (X i))
    rw [f.commutes, D.map_algebraMap]
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mappedPolynomialGradient, dotProduct,
      add_mul, Finset.sum_add_distrib, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  | mul_X p j hp =>
    have hX : mappedPolynomialGradient f.toRingHom (X j) ⬝ᵥ
        (fun i => D (f (X i))) = D (f (X j)) := by
      simp [mappedPolynomialGradient, dotProduct, pderiv_X, Pi.single_apply]
    rw [map_mul, D.leibniz, mappedPolynomialGradient_product_pairing, hX, ← hp]
    simp only [smul_eq_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring

/-- The original polynomial ratio covector detects the actual
derivative of that rational function in the cone field. -/
theorem derivation_polynomialRatioCovector_pairing
    (f : MvPolynomial (Fin n) K →ₐ[K] κ) (D : Derivation K κ κ)
    (p q : MvPolynomial (Fin n) K) :
    D (f p / f q) = polynomialRatioCovector f.toRingHom p q ⬝ᵥ
      (fun j => D (f (X j))) := by
  rw [D.leibniz_div, polynomialRatioCovector_pairing,
    ← derivation_mappedPolynomialGradient_pairing,
    ← derivation_mappedPolynomialGradient_pairing]
  simp only [smul_eq_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

variable [CharZero K]

/-- A transcendental original rational parameter constructs a tangent
vector on which its actual differential equals one. This is stronger
than nonvanishing of the restriction to the cone tangent hyperplane. -/
theorem transcendental_cone_parameter_constructs_tangent_vector
    (f : MvPolynomial (Fin n) K →ₐ[K] κ) (R p q : MvPolynomial (Fin n) K)
    (hR : f R = 0) (ht : Transcendental K (f p / f q)) :
    ∃ v : Fin n → κ, mappedPolynomialGradient f.toRingHom R ⬝ᵥ v = 0 ∧
      polynomialRatioCovector f.toRingHom p q ⬝ᵥ v = 1 := by
  obtain ⟨D, hD⟩ := exists_derivation_apply_eq_one_of_transcendental (f p / f q) ht
  refine ⟨fun j => D (f (X j)), ?_, ?_⟩
  · rw [← derivation_mappedPolynomialGradient_pairing, hR, map_zero]
  · rw [← derivation_polynomialRatioCovector_pairing, hD]

variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

local notation "S" => MvPolynomial (Fin n) K
local notation "κ₀" => IsLocalRing.ResidueField (Localization.AtPrime Q)

omit [CharZero K] in
/-- The original defining cone equation vanishes in its own local
residue field. -/
theorem source_cone_equation_residue_eq_zero (R : S) (hQ : Q = Ideal.span {R}) :
    algebraMap S κ₀ R = 0 := by
  change IsLocalRing.residue (Localization.AtPrime Q) (algebraMap S (Localization.AtPrime Q) R) = 0
  rw [IsLocalRing.residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal (I := Q)]
  apply Ideal.mem_map_of_mem
  rw [hQ]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- For the actual map, transcendence of the cone parameter derives
the nonzero tangent differential needed by the local nilpotence
contradiction. Only the common-normal and common-kernel geometry remains. -/
theorem actual_image_cone_transcendental_parameter_obstruction
    (H : Fin n → S) (hN : IsNilpotent (jac H)) (I : ImageRelationWitness H)
    (hQ : Q = Ideal.span {I.equation}) (g : S) (hg : g ≠ 0)
    (P : Fin n → S) (hHP : H = fun i => g * P i)
    (p q : S) {d : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (hq₀ : algebraMap S κ₀ q ≠ 0) (hqP : algebraMap S κ₀ (aeval P q) ≠ 0)
    (ht : Transcendental K (algebraMap S κ₀ p / algebraMap S κ₀ q))
    (hpreserve : I.equation ∣ aeval P p * q - p * aeval P q)
    (α : κ₀) (hα : α ≠ 0)
    (hnormal : mappedPolynomialGradient ((algebraMap S κ₀).comp (aeval P).toRingHom) I.equation =
      fun j => α * mappedPolynomialGradient (algebraMap S κ₀) I.equation j)
    (hker : ∀ v : Fin n → κ₀, mappedPolynomialGradient (algebraMap S κ₀) I.equation ⬝ᵥ v = 0 →
      (polynomialRatioCovector (algebraMap S κ₀) p q ⬝ᵥ v = 0 ↔
        polynomialRatioCovector ((algebraMap S κ₀).comp (aeval P).toRingHom) p q ⬝ᵥ v = 0)) :
    False := by
  let f : S →ₐ[K] κ₀ := IsScalarTower.toAlgHom K S κ₀
  obtain ⟨v, hv, htangent⟩ := transcendental_cone_parameter_constructs_tangent_vector f
    I.equation p q (source_cone_equation_residue_eq_zero Q I.equation hQ) ht
  change polynomialRatioCovector (algebraMap S κ₀) p q ⬝ᵥ v = 1 at htangent
  exact actual_image_cone_parameter_preservation_obstruction Q H hN I hQ g hg P hHP
    p q hp hq hq₀ hqP hpreserve α hα hnormal
    ⟨v, hv, by rw [htangent]; exact one_ne_zero⟩ hker

end DimensionFourDependence
