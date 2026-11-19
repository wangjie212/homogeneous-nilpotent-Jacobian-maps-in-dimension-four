import DimensionFourDependence.PencilBaseNormalKernel
import DimensionFourDependence.ClosedGaussNormalJetRealization

/-! # The original fixed-vertex Gauss pencil base maps to the vertex axis

No normal incidence at the base is assumed. The original Euler normal
identity, the exact reduced quotient kernel and the constructed normal
jets prove that all three transverse output coordinates vanish on the
whole pencil base. The result is retained in arbitrary field-valued
points, actual prime ideals and the original base ideal's radical.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Every field-valued base point of the original reduced closed
Gauss pencil maps to the specified fourth-axis vertex. The normal
incidence and coefficient kernel are constructed from the original map. -/
theorem original_fixed_vertex_pencil_base_output_first_three_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    ∀ i : Fin 3, ψ (H i.castSucc) = 0 := by
  let f := closedGaussParameterSourceHom H I e
  let w := closedGaussParameterNormal H I e
  have hw0 : w ≠ 0 := by
    intro hz
    have he := closedGaussParameterSourceHom_normal H I e (imageNormalPivot H I)
    change f (w (imageNormalPivot H I)) = _ at he
    rw [hz, Pi.zero_apply, map_zero, div_self (imageNormalPivot_ne_zero H I)] at he
    exact zero_ne_one he
  obtain ⟨v, hv, _hprimitive, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hwlast : w (Fin.last 3) = 0 := by
    apply f.injective
    change f (w (Fin.last 3)) = f 0
    rw [closedGaussParameterSourceHom_normal, hvertex, zero_div, map_zero]
  have hvlast : v (Fin.last 3) = 0 := by
    rw [hrep] at hwlast
    have he := (mul_eq_zero.mp hwlast).resolve_left hr
    apply RatFunc.algebraMap_injective K
    simpa only [map_zero] using he
  have hrepF (i : Fin 4) : f (w i) = f r * Polynomial.aeval (f RatFunc.X) (v i) := by
    rw [hrep i, map_mul, rational_function_algHom_polynomial_value]
  have hpair : (∑ i, f (w i) * algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) = 0 := by
    simpa only [f, w, closedGaussParameterSourceHom_normal, dotProduct] using
      I.normalized_normal_dot_output_eq_zero H hd hH
  have hsection : (∑ i, Polynomial.aeval (f RatFunc.X) (v i) *
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) = 0 := by
    have he : f r * (∑ i, Polynomial.aeval (f RatFunc.X) (v i) *
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) = 0 := by
      rw [Finset.mul_sum]
      convert hpair using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrepF i]
      ring
    exact (mul_eq_zero.mp he).resolve_left ((map_ne_zero f).mpr hr)
  obtain ⟨i, j, _hminor, hLI⟩ :=
    closed_gauss_parameter_constructs_independent_normal_jet_minor H hd hH hind I hGauss e
  apply pencil_base_output_first_three_zero_of_normal_jets
    p q hq hrel H w v r hLI hrep hvlast ?_ ψ hpψ hqψ
  rw [← hparameter]
  exact hsection

omit F in
/-- Every prime of the original source containing the pencil base
equations contains all three transverse original output coordinates. -/
theorem original_fixed_vertex_pencil_base_prime_contains_outputs
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hpQ : p ∈ Q) (hqQ : q ∈ Q) :
    ∀ i : Fin 3, H i.castSucc ∈ Q := by
  let ψ : MvPolynomial (Fin 4) K →ₐ[K] Q.ResidueField := IsScalarTower.toAlgHom K _ _
  have hpψ : ψ p = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hpQ
  have hqψ : ψ q = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hqQ
  intro i
  exact Ideal.algebraMap_residueField_eq_zero.mp
    (original_fixed_vertex_pencil_base_output_first_three_zero
      H hd hH hind I hGauss hvertex e p q hq hrel hparameter ψ hpψ hqψ i)

omit F in
/-- The whole original pencil base, including nonclosed generic
points of its curve components, maps into the vertex axis. -/
theorem original_fixed_vertex_pencil_base_radical_contains_outputs
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q) :
    ∀ i : Fin 3, H i.castSucc ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).radical := by
  intro i
  rw [Ideal.radical_eq_sInf]
  apply Ideal.mem_sInf.mpr
  intro Q hQ
  let : Q.IsPrime := hQ.2
  exact original_fixed_vertex_pencil_base_prime_contains_outputs
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter Q
    (hQ.1 (Ideal.subset_span (by simp))) (hQ.1 (Ideal.subset_span (by simp))) i

/-- Any output covector annihilating the vertex, in any coefficient
extension, vanishes on the actual original pencil base. -/
theorem original_fixed_vertex_pencil_base_annihilates_vertex_covector
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0)
    (n : Fin 4 → F) (hn : n (Fin.last 3) = 0) :
    (∑ i : Fin 4, n i * ψ (H i)) = 0 := by
  have hfirst := original_fixed_vertex_pencil_base_output_first_three_zero
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter ψ hpψ hqψ
  rw [Fin.sum_univ_castSucc, hn, zero_mul, add_zero]
  simp only [hfirst, mul_zero, Finset.sum_const_zero]

omit F in
/-- The transverse base-locus equations remain valid after any
coefficient-ring extension, with the original base generators retained. -/
theorem original_fixed_vertex_pencil_base_extended_radical_contains_outputs
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    {A : Type*} [CommRing A] (ι : K →+* A) :
    ∀ i : Fin 3, MvPolynomial.map ι (H i.castSucc) ∈
      (Ideal.span ({MvPolynomial.map ι p, MvPolynomial.map ι q} :
        Set (MvPolynomial (Fin 4) A))).radical := by
  intro i
  have hmem := original_fixed_vertex_pencil_base_radical_contains_outputs
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter i
  have hmap := Ideal.map_radical_le
    (f := MvPolynomial.map ι) (I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (Ideal.mem_map_of_mem (MvPolynomial.map ι) hmem)
  simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hmap

omit F in
/-- Every vertex-annihilating output covector over any coefficient
ring vanishes on the coefficient-extended original pencil base. -/
theorem vertex_output_covector_mem_pencil_base_radical
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    {A : Type*} [CommRing A] (ι : K →+* A) (n : Fin 4 → A) (hn : n (Fin.last 3) = 0) :
    (∑ i : Fin 4, C (n i) * MvPolynomial.map ι (H i)) ∈
      (Ideal.span ({MvPolynomial.map ι p, MvPolynomial.map ι q} :
        Set (MvPolynomial (Fin 4) A))).radical := by
  let B := (Ideal.span ({MvPolynomial.map ι p, MvPolynomial.map ι q} :
    Set (MvPolynomial (Fin 4) A))).radical
  have hfirst := original_fixed_vertex_pencil_base_extended_radical_contains_outputs
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter ι
  rw [Fin.sum_univ_castSucc, hn, map_zero, zero_mul, add_zero]
  exact B.sum_mem (fun i hi => B.mul_mem_left _ (hfirst i))

end DimensionFourDependence
