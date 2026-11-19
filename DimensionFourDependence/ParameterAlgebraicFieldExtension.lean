import DimensionFourDependence.ParametricSimpleFixedRoot

/-! # Parameter-algebraic coefficients under a specified coordinate-field embedding

The two actual images of the same rational parameter are canonically
isomorphic. Transporting a polynomial relation through that isomorphism
proves that mapped finite parameter coefficients stay algebraic over
the actual parameter image in a further coordinate field.
-/

namespace DimensionFourDependence

variable {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]

/-- Algebraicity over the actual parameter image is preserved by
every specified embedding of the coordinate field. -/
theorem parameter_algebraic_coefficient_map
    (p : RatFunc K →ₐ[K] F) (g : F →ₐ[K] R) (x : F) (hx : IsAlgebraic p.fieldRange x) :
    IsAlgebraic (g.comp p).fieldRange (g x) := by
  let e := p.equivFieldRange.symm.trans (g.comp p).equivFieldRange
  have hcoeff (a : p.fieldRange) : (e a : R) = g (a : F) := by
    obtain ⟨r, rfl⟩ := p.equivFieldRange.surjective a
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl
  have heval (P : Polynomial p.fieldRange) :
      Polynomial.aeval (g x) (P.map e.toRingHom) = g (Polynomial.aeval x P) := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simp only [Polynomial.map_add, map_add, hP, hQ]
    | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
      change (e a : R) * g x ^ n = g (a : F) * g x ^ n
      rw [hcoeff]
  obtain ⟨P, hP, hPx⟩ := hx
  refine ⟨P.map e.toRingHom, ?_, ?_⟩
  · simpa only [Polynomial.map_zero] using (Polynomial.map_injective e.toRingHom e.injective).ne hP
  · rw [heval, hPx, map_zero]

end DimensionFourDependence
