import DimensionFourDependence.ParabolaFieldEmbedding

/-! # Pointwise algebraic source coefficients give one compatible constant-field embedding -/

namespace DimensionFourDependence

set_option maxHeartbeats 300000

/-- A compatible constant embedding is determined at an element
by its actual value in the embedded source field. -/
theorem constant_embedding_value_eq_of_source_value
    {L S B Z : Type*} [Field L] [Field S] [Field B] [Field Z]
    [Algebra L S] [Algebra B Z]
    (f : S →+* Z) (g : L →+* B)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (algebraMap L S l))
    (l : L) (b : B) (hv : f (algebraMap L S l) = algebraMap B Z b) : g l = b :=
  (algebraMap B Z).injective ((hg l).trans hv)

/-- Original coefficients and original coordinate values determine
every rational source value, using ring homomorphisms directly. -/
theorem rational_source_ringHom_ext_original_coefficients_and_coordinates
    {K Z : Type*} [Field K] [Field Z] {n : ℕ}
    (f g : FractionRing (MvPolynomial (Fin n) K) →+* Z)
    (hK : ∀ c : K, f (algebraMap K (FractionRing (MvPolynomial (Fin n) K)) c) =
      g (algebraMap K (FractionRing (MvPolynomial (Fin n) K)) c))
    (hx : ∀ i, f (rationalCoordinate (K := K) i) = g (rationalCoordinate (K := K) i)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K)
  intro P
  have he : f.comp (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) =
      g.comp (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact hK c
    · intro i
      exact hx i
  exact DFunLike.congr_fun he P

/-- If every coefficient of an embedded source is algebraic over
algebraically closed constants, its actual source values construct one
coefficient-field embedding into those constants. -/
theorem algebraic_source_coefficient_values_construct_constant_embedding
    {L S B Z : Type*} [Field L] [Field S] [Field B] [Field Z]
    [Algebra L S] [Algebra B Z] [IsAlgClosed B]
    (f : S →+* Z)
    (halg : ∀ l : L, IsAlgebraic B (f (algebraMap L S l))) :
    ∃ g : L →+* B, ∀ l : L, algebraMap B Z (g l) = f (algebraMap L S l) := by
  classical
  have hvalue (l : L) : ∃ b : B, algebraMap B Z b = f (algebraMap L S l) :=
    algebraic_value_preimage_of_isAlgClosed _ (halg l)
  let gFun : L → B := fun l => Classical.choose (hvalue l)
  have hgFun (l : L) : algebraMap B Z (gFun l) = f (algebraMap L S l) :=
    Classical.choose_spec (hvalue l)
  let g : L →+* B :=
    { toFun := gFun
      map_zero' := by
        apply (algebraMap B Z).injective
        rw [hgFun, map_zero, map_zero, map_zero]
      map_one' := by
        apply (algebraMap B Z).injective
        rw [hgFun, map_one, map_one, map_one]
      map_add' := by
        intro l m
        apply (algebraMap B Z).injective
        rw [hgFun, map_add, map_add, map_add, hgFun, hgFun]
      map_mul' := by
        intro l m
        apply (algebraMap B Z).injective
        rw [hgFun, map_mul, map_mul, map_mul, hgFun, hgFun] }
  exact ⟨g, hgFun⟩

end DimensionFourDependence
