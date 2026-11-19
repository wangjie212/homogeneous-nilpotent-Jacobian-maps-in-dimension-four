import DimensionFourDependence.VertexLineIncidence

/-! # Original line ideals under the actual coefficient extension -/

namespace DimensionFourDependence

open MvPolynomial

variable {K F : Type*} [Field K] [Field F]

/-- The exact two-coordinate line parametrization commutes with
every field coefficient map, preserving the original coordinate labels. -/
theorem vertexLineParameterHom_map_coefficients
    (f : K →+* F) (b : Fin 3 → K) (j : Fin 3)
    (P : MvPolynomial (Fin 4) K) :
    vertexLineParameterHom (fun i => f (b i)) j (MvPolynomial.map f P) =
      MvPolynomial.map f (vertexLineParameterHom b j P) := by
  have he : (vertexLineParameterHom (fun i => f (b i)) j).toRingHom.comp
        (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (vertexLineParameterHom b j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [vertexLineParameterHom]
    · intro ℓ
      refine Fin.lastCases ?_ (fun i => ?_) ℓ
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, vertexLineParameterHom, aeval_X, Fin.snoc_last]
      · simp [vertexLineParameterHom, map_div₀]
  exact DFunLike.congr_fun he P

/-- Every equation of the original line remains an equation of
the same full line over the coefficient extension. -/
theorem vertexLinePrime_map_mem
    (f : K →+* F) (b : Fin 3 → K) (j : Fin 3)
    (P : MvPolynomial (Fin 4) K) (hP : P ∈ vertexLinePrime b j) :
    MvPolynomial.map f P ∈ vertexLinePrime (fun i => f (b i)) j := by
  change vertexLineParameterHom _ _ _ = 0
  rw [vertexLineParameterHom_map_coefficients]
  change vertexLineParameterHom b j P = 0 at hP
  rw [hP, map_zero]

end DimensionFourDependence
