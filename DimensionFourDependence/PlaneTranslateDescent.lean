import DimensionFourDependence.ConstantPlaneProjection
import DimensionFourDependence.GeometricFiberNonlinearity

/-! # Descent of a fixed plane's translation coefficients

A constant projection complementary to the direction plane has scalar
values on a geometric plane translate. Its corresponding source values
are algebraic over the full output field. Subtracting this projection
leaves exactly the fixed plane directions.
-/

namespace DimensionFourDependence

open Matrix

variable {K M F E G : Type*} [Field K] [Field M] [Field F] [Field E] [Field G]
    [Algebra M F] [Algebra M E] [Algebra E G] [Algebra M G] [IsScalarTower M E G]
    [Algebra.IsAlgebraic M E]

/-- Geometric containment in a translate of a fixed direction plane
descends to a translate with coefficients algebraic in the source field. -/
theorem plane_translate_algebraic_descent (k : K →+* M) (f : F →ₐ[M] G)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w]) (x : Fin 4 → F)
    (a : Fin 4 → E) (r s : G)
    (hpos : ∀ i, f (x i) = algebraMap E G (a i) +
      algebraMap M G (k (v i)) * r + algebraMap M G (k (w i)) * s) :
    ∃ b : Fin 4 → F, (∀ i, IsAlgebraic M (b i)) ∧ ∃ p q : F,
      ∀ i, x i = b i + algebraMap M F (k (v i)) * p + algebraMap M F (k (w i)) * q := by
  let B := directionPlaneMatrix v w
  obtain ⟨C, hCB⟩ := directionPlaneMatrix_has_left_inverse v w hvw
  let P := directionPlaneProjection B C
  let kF : K →+* F := (algebraMap M F).comp k
  let kE : K →+* E := (algebraMap M E).comp k
  let kG : K →+* G := (algebraMap M G).comp k
  have hPB : P * B = 0 := directionPlaneProjection_mul B C hCB
  have hPBG : P.map kG * B.map kG = 0 := by
    rw [← Matrix.map_mul, hPB]
    ext i j
    simp
  have hposv : f ∘ x = (algebraMap E G) ∘ a + B.map kG *ᵥ ![r, s] := by
    funext i
    simpa [B, directionPlaneMatrix, kG, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_assoc]
      using hpos i
  have hproj : P.map kG *ᵥ (f ∘ x) =
      (algebraMap E G) ∘ (P.map kE *ᵥ a) := by
    rw [hposv, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPBG, Matrix.zero_mulVec, add_zero]
    funext i
    change (P.map kG *ᵥ ((algebraMap E G) ∘ a)) i = algebraMap E G ((P.map kE *ᵥ a) i)
    rw [RingHom.map_mulVec (algebraMap E G) (P.map kE) a i]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    change algebraMap M G (k (P i j)) * algebraMap E G (a j) =
      algebraMap E G (algebraMap M E (k (P i j))) * algebraMap E G (a j)
    rw [← IsScalarTower.algebraMap_apply M E G]
  let b : Fin 4 → F := P.map kF *ᵥ x
  have hb (i : Fin 4) : IsAlgebraic M (b i) := by
    have hmap : f (b i) = (P.map kG *ᵥ (f ∘ x)) i := by
      change f.toRingHom ((P.map kF *ᵥ x) i) = (P.map kG *ᵥ (f ∘ x)) i
      rw [RingHom.map_mulVec f.toRingHom (P.map kF) x i]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      change f (algebraMap M F (k (P i j))) * f (x j) = algebraMap M G (k (P i j)) * f (x j)
      rw [f.commutes]
    have hscalar : f (b i) = algebraMap E G ((P.map kE *ᵥ a) i) := by
      rw [hmap, hproj]
      rfl
    apply (isAlgebraic_algHom_iff f f.injective).mp
    rw [hscalar]
    exact (Algebra.IsAlgebraic.isAlgebraic ((P.map kE *ᵥ a) i)).algebraMap
  refine ⟨b, hb, (C.map kF *ᵥ x) 0, (C.map kF *ᵥ x) 1, ?_⟩
  intro i
  have he := congrFun (directionPlaneProjection_decompose (B.map kF) (C.map kF) x) i
  rw [← directionPlaneProjection_map kF B C] at he
  change x i = b i + (B.map kF *ᵥ (C.map kF *ᵥ x)) i at he
  have hB : (B.map kF *ᵥ (C.map kF *ᵥ x)) i =
      kF (v i) * (C.map kF *ᵥ x) 0 + kF (w i) * (C.map kF *ᵥ x) 1 := by
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rfl
  rw [hB] at he
  simpa only [kF, RingHom.comp_apply, add_assoc] using he

end DimensionFourDependence
