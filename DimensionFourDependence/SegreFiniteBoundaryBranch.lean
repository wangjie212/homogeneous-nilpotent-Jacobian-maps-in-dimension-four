import DimensionFourDependence.SegreActualBoundaryAlgebraicity
import DimensionFourDependence.SegreBoundaryParameterField

/-! # Finite branches over the original Segre ruling parameter -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual parameter subfield of the boundary constants is the
original rational ruling field, with its specified embedding retained. -/
noncomputable def segreBoundaryRulingRationalEquiv
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ] :
    RatFunc K ≃ₐ[K] segreBoundaryRulingField Y hY j hj κ :=
  (segreSourceRulingParameterHom Y hY j hj).equivFieldRange.trans
    (((IsScalarTower.toAlgHom K (coefficientField (K := K) Y) κ).comp
      (segreRulingFieldCoefficientHom Y hY j hj)).equivFieldRange)

/-- Both original ruling equations over the actual boundary parameter field. -/
noncomputable def segreBoundaryRulingMatrix
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ] :
    Matrix (Fin 2) (Fin 4) (segreBoundaryRulingField Y hY j hj κ) :=
  (segreRulingMatrix j (segreRulingFieldParameter Y hY j hj)).map
    (((IsScalarTower.toAlgHom K (coefficientField (K := K) Y) κ).comp
      (segreRulingFieldCoefficientHom Y hY j hj)).equivFieldRange)

/-- The actual normalized algebraic point lies over one finite extension
of the original ruling parameter. Its four coordinates and both ruling
equations are preserved in the finite field. -/
theorem normalized_algebraic_segre_ruling_point_finite_branch
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ]
    (b : Fin 4 → κ) (a : Fin 4) (ha : b a = 1)
    (halg : ∀ i, IsAlgebraic (segreBoundaryRulingField Y hY j hj κ) (b i))
    (hb : (segreRulingMatrix j (segreRulingFieldParameter Y hY j hj)).map
      ((algebraMap (coefficientField (K := K) Y) κ).comp
        (segreRulingFieldCoefficientHom Y hY j hj).toRingHom) *ᵥ b = 0) :
    ∃ B : IntermediateField (segreBoundaryRulingField Y hY j hj κ) κ,
      Module.Finite (segreBoundaryRulingField Y hY j hj κ) B ∧
        ∃ v : Fin 4 → B, v a = 1 ∧ (∀ i, (v i : κ) = b i) ∧
          (segreBoundaryRulingMatrix Y hY j hj κ).map
            (algebraMap (segreBoundaryRulingField Y hY j hj κ) B) *ᵥ v = 0 := by
  let J := segreBoundaryRulingField Y hY j hj κ
  let B := IntermediateField.adjoin J (Set.range b)
  have hfin : Module.Finite J B := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨i, rfl⟩
    exact (halg i).isIntegral)
  let v : Fin 4 → B := fun i => ⟨b i, IntermediateField.subset_adjoin J _ ⟨i, rfl⟩⟩
  refine ⟨B, hfin, v, ?_, fun _ => rfl, ?_⟩
  · apply Subtype.ext
    exact ha
  · funext r
    apply (algebraMap B κ).injective
    change algebraMap B κ
      (((segreBoundaryRulingMatrix Y hY j hj κ).map (algebraMap J B) *ᵥ v) r) =
      algebraMap B κ 0
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero, Matrix.map_apply]
    change (∑ i, ((algebraMap (coefficientField (K := K) Y) κ).comp
      (segreRulingFieldCoefficientHom Y hY j hj).toRingHom)
        (segreRulingMatrix j (segreRulingFieldParameter Y hY j hj) r i) * b i) = 0
    exact congrFun hb r

/-- Every normalized actual full-fiber point on either original Segre
ruling constructs its own finite branch over that original rational
parameter field. Algebraicity follows from the original nilpotent map. -/
theorem actual_full_fiber_segre_boundary_has_finite_ruling_branch
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (segreOriginalOutputTriple H)) κ] [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (a : Fin 4) (ha : z (some a) = 1)
    (hboundary : projectiveFieldPoint
      (E := coefficientField (K := K) (segreOriginalOutputTriple H)) z hz ∈
        projectiveClosureSet (L := coefficientField (K := K) (segreOriginalOutputTriple H))
          (rationalCoordinate (K := K) (n := 4)))
    (hkernel : (segreRulingMatrix j
      (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)).map
        ((algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp
          (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj).toRingHom) *ᵥ
            (fun i => z (some i)) = 0) :
    ∃ B : IntermediateField (segreBoundaryRulingField (segreOriginalOutputTriple H) hY j hj κ) κ,
      Module.Finite (segreBoundaryRulingField (segreOriginalOutputTriple H) hY j hj κ) B ∧
        ∃ v : Fin 4 → B, v a = 1 ∧ (∀ i, (v i : κ) = z (some i)) ∧
          (segreBoundaryRulingMatrix (segreOriginalOutputTriple H) hY j hj κ).map
            (algebraMap (segreBoundaryRulingField (segreOriginalOutputTriple H) hY j hj κ) B) *ᵥ v = 0 := by
  exact normalized_algebraic_segre_ruling_point_finite_branch (segreOriginalOutputTriple H) hY j hj κ
    (fun i => z (some i)) a ha
    (actual_full_fiber_segre_boundary_coordinates_algebraic_over_ruling_field
      H hrank hY hd hH hN hind I hSegre j hj κ z hz a ha hboundary hkernel) hkernel

end DimensionFourDependence
