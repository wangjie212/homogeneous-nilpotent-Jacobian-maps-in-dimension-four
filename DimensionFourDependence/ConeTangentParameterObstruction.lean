import DimensionFourDependence.SourceConeParameterObstruction
import DimensionFourDependence.ImageEquationWitness
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # Constructing the tangent data from the original image equation

The image relation for `H = g P` gives the relation for `P` itself.
Equal source and target tangent hyperplanes then supply both tangent
conditions used in the local nilpotence obstruction of Lemma 4.3.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K κ : Type*} [Field K] [Field κ] {n : ℕ}

/-- Removing the actual common scalar preserves the original
homogeneous image equation. -/
theorem ImageRelationWitness.primitive_part_vanishing
    (H : Fin n → MvPolynomial (Fin n) K) (I : ImageRelationWitness H)
    (g : MvPolynomial (Fin n) K) (hg : g ≠ 0)
    (P : Fin n → MvPolynomial (Fin n) K) (hHP : H = fun i => g * P i) :
    aeval P I.equation = 0 := by
  have he : aeval (fun i => g * P i) I.equation = 0 :=
    (congrArg (fun V : Fin n → MvPolynomial (Fin n) K => aeval V I.equation) hHP).symm.trans I.vanishing
  rw [homogeneous_aeval_scale I.equation I.homogeneous P g] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero I.degree hg)

/-- Euler's identity places the actual target point in its cone
tangent hyperplane over the residue field. -/
theorem homogeneous_image_relation_target_radial_tangent
    (f : MvPolynomial (Fin n) K →+* κ)
    (P : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    {e : ℕ} (hR : R.IsHomogeneous e) (hRP : aeval P R = 0) :
    mappedPolynomialGradient (f.comp (aeval P).toRingHom) R ⬝ᵥ
      (fun i => f (P i)) = 0 := by
  have he := congrArg f (congrArg (aeval P) hR.sum_X_mul_pderiv)
  simp only [map_sum, map_mul, aeval_X, map_nsmul, hRP, nsmul_zero, map_zero] at he
  simpa only [mappedPolynomialGradient, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dotProduct, mul_comm] using he

/-- The polynomial chain rule sends every ambient direction under
`JP` into the target tangent hyperplane of the actual image cone. -/
theorem image_relation_target_jacobian_tangent
    (f : MvPolynomial (Fin n) K →+* κ)
    (P : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    (hRP : aeval P R = 0) (v : Fin n → κ) :
    mappedPolynomialGradient (f.comp (aeval P).toRingHom) R ⬝ᵥ
      ((jac P).map f *ᵥ v) = 0 := by
  rw [← mappedPolynomialGradient_composition_pairing, hRP]
  change (∑ i, f (pderiv i (0 : MvPolynomial (Fin n) K)) * v i) = 0
  simp

/-- Proportional nonzero source and target normal covectors derive
both tangent conditions of the original local matrix obstruction. -/
theorem common_cone_normal_constructs_tangent_data
    (f : MvPolynomial (Fin n) K →+* κ)
    (P : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    {e : ℕ} (hR : R.IsHomogeneous e) (hRP : aeval P R = 0)
    (α : κ) (hα : α ≠ 0)
    (hnormal : mappedPolynomialGradient (f.comp (aeval P).toRingHom) R =
      fun j => α * mappedPolynomialGradient f R j) :
    mappedPolynomialGradient f R ⬝ᵥ (fun i => f (P i)) = 0 ∧
      ∀ v : Fin n → κ, mappedPolynomialGradient f R ⬝ᵥ ((jac P).map f *ᵥ v) = 0 := by
  have hscale (v : Fin n → κ) :
      mappedPolynomialGradient (f.comp (aeval P).toRingHom) R ⬝ᵥ v =
        α * (mappedPolynomialGradient f R ⬝ᵥ v) := by
    rw [hnormal]
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  constructor
  · have he := homogeneous_image_relation_target_radial_tangent f P R hR hRP
    rw [hscale] at he
    exact (mul_eq_zero.mp he).resolve_left hα
  · intro v
    have he := image_relation_target_jacobian_tangent f P R hRP v
    rw [hscale] at he
    exact (mul_eq_zero.mp he).resolve_left hα

variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

local notation "S" => MvPolynomial (Fin n) K
local notation "κ₀" => IsLocalRing.ResidueField (Localization.AtPrime Q)

/-- The actual polynomial map and its image equation yield the local
contradiction once parameter preservation supplies common tangent and
ruling kernels. No local factorization, tangent-lattice action,
polynomial derivative transport or target tangency is assumed.
Identifying these remaining covectors with the original Gauss parameter
under dominance is still a separate geometric step. -/
theorem actual_image_cone_parameter_preservation_obstruction
    (H : Fin n → S) (hN : IsNilpotent (jac H)) (I : ImageRelationWitness H)
    (hQ : Q = Ideal.span {I.equation}) (g : S) (hg : g ≠ 0)
    (P : Fin n → S) (hHP : H = fun i => g * P i)
    (p q : S) {d : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (hq₀ : algebraMap S κ₀ q ≠ 0) (hqP : algebraMap S κ₀ (aeval P q) ≠ 0)
    (hpreserve : I.equation ∣ aeval P p * q - p * aeval P q)
    (α : κ₀) (hα : α ≠ 0)
    (hnormal : mappedPolynomialGradient ((algebraMap S κ₀).comp (aeval P).toRingHom) I.equation =
      fun j => α * mappedPolynomialGradient (algebraMap S κ₀) I.equation j)
    (hb : ∃ v : Fin n → κ₀, mappedPolynomialGradient (algebraMap S κ₀) I.equation ⬝ᵥ v = 0 ∧
      polynomialRatioCovector (algebraMap S κ₀) p q ⬝ᵥ v ≠ 0)
    (hker : ∀ v : Fin n → κ₀, mappedPolynomialGradient (algebraMap S κ₀) I.equation ⬝ᵥ v = 0 →
      (polynomialRatioCovector (algebraMap S κ₀) p q ⬝ᵥ v = 0 ↔
        polynomialRatioCovector ((algebraMap S κ₀).comp (aeval P).toRingHom) p q ⬝ᵥ v = 0)) :
    False := by
  have hRP := I.primitive_part_vanishing H g hg P hHP
  obtain ⟨hP, hJ⟩ := common_cone_normal_constructs_tangent_data (algebraMap S κ₀)
    P I.equation I.homogeneous hRP α hα hnormal
  apply source_cone_nilpotence_obstructs_parameter_preservation Q I.equation g I.irreducible hQ hg
    P (by simpa only [← hHP] using hN) p q hp hq hq₀ hqP hpreserve hP
    (fun v _ => hJ v) hb hker

end DimensionFourDependence
