import DimensionFourDependence.GeometricClosedGaussEmbedding

/-! # The actual generic source point determines its compatible closed Gauss realization uniquely -/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A closed Gauss embedding retains its actual original source
realization, including all four original coordinates and every coefficient. -/
noncomputable def CompatibleGeometricSourceRealization
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (g : closedGaussParameterField H I →ₐ[K] E) : Prop :=
  ∃ f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K]
      FractionRing (MvPolynomial (Fin 4) E ⧸ P),
    (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
    ∀ c : closedGaussParameterField H I,
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (g c) =
        f (c : FractionRing (MvPolynomial (Fin 4) K))

/-- Every original rational source-field embedding is determined
by its actual original coordinate values, without a selected output chart. -/
theorem rational_source_algHom_ext_original_coordinates
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (f g : FractionRing (MvPolynomial (Fin n) K) →ₐ[K] F)
    (hcoords : ∀ i : Fin n, f (rationalCoordinate (K := K) i) = g (rationalCoordinate (K := K) i)) :
    f = g := by
  have hpoly (Q : MvPolynomial (Fin n) K) :
      f (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Q) =
        g (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Q) := by
    have hf := comp_aeval_apply (rationalCoordinate (K := K) (n := n)) f Q
    have hg := comp_aeval_apply (rationalCoordinate (K := K) (n := n)) g Q
    rw [rationalCoordinate_aeval] at hf hg
    exact hf.trans ((congrArg (fun x : Fin n → F => aeval x Q) (funext hcoords)).trans hg.symm)
  apply AlgHom.ext
  intro z
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K) z
  rw [map_div₀, map_div₀, hpoly, hpoly]

/-- The same actual original geometric source point has only one
compatible embedding of its entire original closed Gauss field. -/
theorem compatible_geometric_source_realization_unique
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (g₁ g₂ : closedGaussParameterField H I →ₐ[K] E)
    (h₁ : CompatibleGeometricSourceRealization H I P g₁)
    (h₂ : CompatibleGeometricSourceRealization H I P g₂) : g₁ = g₂ := by
  obtain ⟨f₁, hf₁, hg₁⟩ := h₁
  obtain ⟨f₂, hf₂, hg₂⟩ := h₂
  have hf : f₁ = f₂ := rational_source_algHom_ext_original_coordinates f₁ f₂
    (fun i => (hf₁ i).trans (hf₂ i).symm)
  apply AlgHom.ext
  intro c
  apply (algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P))).injective
  rw [hg₁, hg₂, hf]

end DimensionFourDependence
