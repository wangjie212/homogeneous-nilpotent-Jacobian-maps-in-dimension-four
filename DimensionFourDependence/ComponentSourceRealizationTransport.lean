import DimensionFourDependence.AlgebraicComponentTower
import DimensionFourDependence.FullOutputGeometricFiber
import DimensionFourDependence.FiberEmbedding
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # Actual component coordinates retain the original source and its constant values -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual coordinate field of any original full generic-fiber
component supplies an embedding of the entire original rational source,
preserving all four original coordinate labels and the full output action. -/
theorem full_generic_component_coordinates_construct_source_realization
    {K A G : Type*} [Field K] [Field A] [Field G]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    [Algebra (polynomialOutputField H) A] [Algebra A G]
    [Algebra (polynomialOutputField H) G]
    [IsScalarTower (polynomialOutputField H) A G]
    (v : Fin 4 → G)
    (hcomponent : fiberVanishingIdeal (L := A) v ∈
      (extendCoefficientIdeal A (fiberVanishingIdeal (L := polynomialOutputField H)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[polynomialOutputField H] G,
      ∀ i : Fin 4, f (rationalCoordinate (K := K) i) = v i := by
  have hrel : fiberVanishingIdeal (L := polynomialOutputField H) v =
      fiberVanishingIdeal (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)) := by
    rw [← fiberVanishingIdeal_comap_coefficients (E := A)]
    exact minimalPrime_extended_coefficients_comap A _ _ hcomponent
  exact exists_fiber_embedding_of_relations_eq (rationalCoordinate (K := K) (n := 4)) v
    (rationalSource_adjoin_coordinates_eq_top (polynomialOutputField H)) hrel

/-- Equality of the actual original coefficient-field source relations
retains every rational source value that was already a specified constant.
This includes all original closed Gauss coefficients. No new unrelated
coefficient realization is chosen on the component. -/
theorem source_relation_transport_retains_already_constant_values
    {K C G Z : Type*} [Field K] [Field C] [Field G] [Field Z]
    [Algebra K C] [Algebra C G] [Algebra K G] [IsScalarTower K C G]
    [Algebra C Z] [Algebra K Z] [IsScalarTower K C Z] {n : ℕ}
    (Φ : FractionRing (MvPolynomial (Fin n) K) →ₐ[K] G)
    (f : FractionRing (MvPolynomial (Fin n) K) →ₐ[K] Z)
    (v : Fin n → G) (w : Fin n → Z)
    (hΦ : ∀ i, Φ (rationalCoordinate (K := K) i) = v i)
    (hf : ∀ i, f (rationalCoordinate (K := K) i) = w i)
    (hrel : fiberVanishingIdeal (L := C) w = fiberVanishingIdeal (L := C) v)
    (c : FractionRing (MvPolynomial (Fin n) K)) (t : C)
    (hconstant : Φ c = algebraMap C G t) : f c = algebraMap C Z t := by
  have hΦpoly (P : MvPolynomial (Fin n) K) :
      Φ (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) P) =
        aeval (R := C) v (MvPolynomial.map (algebraMap K C) P) := by
    rw [aeval_map_algebra_extension]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := n)) Φ P
    rw [rationalCoordinate_aeval, show (fun i => Φ (rationalCoordinate (K := K) i)) = v from funext hΦ] at he
    exact he
  have hfpoly (P : MvPolynomial (Fin n) K) :
      f (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) P) =
        aeval (R := C) w (MvPolynomial.map (algebraMap K C) P) := by
    rw [aeval_map_algebra_extension]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := n)) f P
    rw [rationalCoordinate_aeval, show (fun i => f (rationalCoordinate (K := K) i)) = w from funext hf] at he
    exact he
  obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) K) c
  have hQsource : algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hQ)
  have hQold : Φ (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) Q) ≠ 0 :=
    (map_ne_zero Φ).mpr hQsource
  have hQnew : f (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) Q) ≠ 0 :=
    (map_ne_zero f).mpr hQsource
  let R := MvPolynomial.map (algebraMap K C) P - MvPolynomial.C t * MvPolynomial.map (algebraMap K C) Q
  have hR : R ∈ fiberVanishingIdeal (L := C) v := by
    change aeval v R = 0
    simp only [R, map_sub, map_mul, aeval_C]
    rw [← hΦpoly P, ← hΦpoly Q]
    apply sub_eq_zero.mpr
    apply (div_eq_iff hQold).mp
    simpa only [map_div₀] using hconstant
  rw [← hrel] at hR
  change aeval (R := C) w R = 0 at hR
  simp only [R, map_sub, map_mul, aeval_C] at hR
  rw [← hfpoly P, ← hfpoly Q] at hR
  rw [map_div₀]
  exact (div_eq_iff hQnew).mpr (sub_eq_zero.mp hR)

end DimensionFourDependence
