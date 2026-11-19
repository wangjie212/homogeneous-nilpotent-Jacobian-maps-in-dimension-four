import DimensionFourDependence.AlgebraicImagePointExtension
import DimensionFourDependence.ScalarExtendedMapHypotheses
import DimensionFourDependence.NormalRigidGenericQuadric

/-! # The quadric argument after adjoining algebraic coefficients

The actual original generic point and its two actual contained lines are
kept in the same ambient field. Integral incomparability gives their
exact image relations over the new algebraic coefficient field. Normal
independence also survives, so the checked geometric argument applies.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K F E : Type u} [Field K] [CharZero K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsAlgebraic K F] [IsAlgClosed F]

omit [CharZero K] [Algebra K F] [Algebra K E] [Algebra F E]
  [IsScalarTower K F E] [Algebra.IsAlgebraic K F] [IsAlgClosed F] in
/-- Transport a line-atlas point along equality of actual equations. -/
def hypersurfaceLineAtlas_transport {R S : MvPolynomial (Fin 4) E}
    (h : R = S) (s : hypersurfaceLineAtlas R) : hypersurfaceLineAtlas S := by
  subst S
  exact s

omit [CharZero K] [Algebra K F] [Algebra K E] [Algebra F E]
  [IsScalarTower K F E] [Algebra.IsAlgebraic K F] [IsAlgClosed F] in
/-- Transport changes only the membership proof, preserving the actual line. -/
theorem hypersurfaceAtlasLine_transport {R S : MvPolynomial (Fin 4) E}
    (h : R = S) (s : hypersurfaceLineAtlas R) :
    hypersurfaceAtlasLine S (hypersurfaceLineAtlas_transport h s) = hypersurfaceAtlasLine R s := by
  subst S
  rfl

/-- The actual two generic image lines give a smooth quadric over an
algebraically closed algebraic coefficient extension, with no assumption
about the Gauss-image dimension of the extended presentation. -/
theorem algebraic_coefficient_extension_two_lines_quadric
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0)
    (s t : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hs : O ∈ hypersurfaceAtlasLine _ s) (ht : O ∈ hypersurfaceAtlasLine _ t)
    (hne : hypersurfaceAtlasLine _ s ≠ hypersurfaceAtlasLine _ t) :
    I.degree = 2 ∧
      (∀ x : Fin 4 → F, x ≠ 0 →
        (fun i => aeval x (pderiv i (MvPolynomial.map (algebraMap K F) I.equation))) ≠ 0) ∧
      ∃ (e : (Fin 4 → F) ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F))) (c : F), c ≠ 0 ∧
        rulingPolynomialInCoordinates e = MvPolynomial.C c * MvPolynomial.map (algebraMap K F) I.equation ∧
        ∀ x : Fin 4 → F, aeval x (MvPolynomial.map (algebraMap K F) I.equation) = 0 ↔
          standardRulingQuadric (e x) = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let HF : Fin 4 → MvPolynomial (Fin 4) F := fun i => MvPolynomial.map (algebraMap K F) (H i)
  let IF : ImageRelationWitness HF := I.scalarExtension (E := F) H hrank
  have heq : MvPolynomial.map (algebraMap F E) IF.equation =
      MvPolynomial.map (algebraMap K E) I.equation := by
    change MvPolynomial.map (algebraMap F E) (MvPolynomial.map (algebraMap K F) I.equation) = _
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K F E]
  let sf := hypersurfaceLineAtlas_transport heq.symm s
  let tf := hypersurfaceLineAtlas_transport heq.symm t
  have hsf : hypersurfaceAtlasLine _ sf = hypersurfaceAtlasLine _ s :=
    hypersurfaceAtlasLine_transport heq.symm s
  have htf : hypersurfaceAtlasLine _ tf = hypersurfaceAtlasLine _ t :=
    hypersurfaceAtlasLine_transport heq.symm t
  have hF := algebraic_coefficient_extension_image_point_relations (F := F) H O hrel
  have hq := relation_generic_distinct_lines_quadric_of_normal_independent HF hd
    (isHomogMap_map_coefficients H hH)
    ((polyRank_jac_map_coefficients H).trans hrank)
    (componentsIndependent_map_coefficients H hind) IF
    (I.gauss_two_scalar_extended_normal_independent H hd hH hN hrank hGauss)
    O hF sf tf (by rw [hsf]; exact hs) (by rw [htf]; exact ht)
      (by rw [hsf, htf]; exact hne)
  have hid : IF.degree = I.degree := rfl
  have hie : IF.equation = MvPolynomial.map (algebraMap K F) I.equation := rfl
  rw [hid, hie] at hq
  exact hq

end DimensionFourDependence
