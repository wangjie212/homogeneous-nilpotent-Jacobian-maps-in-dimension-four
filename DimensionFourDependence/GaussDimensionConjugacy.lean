import DimensionFourDependence.ImageRelationConjugacy
import DimensionFourDependence.CommonVertexCoordinateChoice
import DimensionFourDependence.ProjectiveRatioLinearCoordinates

/-! # The actual Gauss dimension survives source-target coordinate conjugacy -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The image-relation witness transported from the original map has
exactly the original Gauss-image dimension. -/
theorem gaussImageDimension_linearPolynomialConjugate
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    gaussImageDimension (linearPolynomialConjugate T S H) (I.linearConjugate H T S hTS hST) =
      gaussImageDimension H I := by
  let H' := linearPolynomialConjugate T S H
  let J := I.linearConjugate H T S hTS hST
  let nu := rationalImageNormal H I.equation
  let f := matrixSourceFractionEquiv T S hTS hST
  let mu : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) := fun i => f (nu i)
  let a := imageNormalPivot H I
  let b := imageNormalPivot H' J
  have hnormal : rationalImageNormal H' J.equation =
      mu ᵥ* T.map (algebraMap K (FractionRing (MvPolynomial (Fin 4) K))) := by
    change rationalImageNormal (linearPolynomialConjugate T S H)
      (I.linearConjugate H T S hTS hST).equation = _
    rw [ImageRelationWitness.linearConjugate_equation,
      rationalImageNormal_linearPolynomialConjugate T S hTS hST H I.equation]
  have ha : mu a ≠ 0 := (map_ne_zero f).mpr (imageNormalPivot_ne_zero H I)
  have hb : (mu ᵥ* T.map (algebraMap K (FractionRing (MvPolynomial (Fin 4) K)))) b ≠ 0 := by
    have he := imageNormalPivot_ne_zero H' J
    rw [hnormal] at he
    exact he
  change Algebra.trdeg K (projectiveRatioField (K := K) (rationalImageNormal H' J.equation) b) =
    Algebra.trdeg K (projectiveRatioField (K := K) nu a)
  rw [hnormal, projectiveRatioField_vecMul_eq mu T S hTS a b ha hb]
  exact projectiveRatioField_trdeg_map f.toAlgHom nu a

/-- A nonzero constant common vertex constructs a genuine conjugated
map with all original algebraic hypotheses and a fourth-axis vertex.
Transporting an actual geometric fiber component is a separate step. -/
theorem common_vertex_constructs_standard_axis_map_data
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {d : ℕ} (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (v : Fin 4 → K) (hv : v ≠ 0)
    (hnormal : rationalImageNormal H I.equation ⬝ᵥ
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)) = 0) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1),
      ∃ J : ImageRelationWitness (linearPolynomialConjugate T S H),
        IsHomogMap (linearPolynomialConjugate T S H) d ∧
        IsNilpotent (jac (linearPolynomialConjugate T S H)) ∧
        polyRank (jac (linearPolynomialConjugate T S H)) = 3 ∧
        (¬ComponentsDependent (linearPolynomialConjugate T S H)) ∧
        gaussImageDimension (linearPolynomialConjugate T S H) J = gaussImageDimension H I ∧
        rationalImageNormal (linearPolynomialConjugate T S H) J.equation (Fin.last 3) = 0 := by
  obtain ⟨T, S, hTS, hST, _hcol, haxis⟩ :=
    nonzero_common_vertex_constructs_conjugated_image_witness H I v hv hnormal
  refine ⟨T, S, hTS, hST, I.linearConjugate H T S hTS hST,
    linearPolynomialConjugate_homogeneous T S H hH,
    linearPolynomialConjugate_nilpotent T S hTS hST H hN, ?_,
    linearPolynomialConjugate_componentsIndependent T S hTS hST H hind,
    gaussImageDimension_linearPolynomialConjugate T S hTS hST H I, haxis⟩
  rw [linearPolynomialConjugate_polyRank T S hTS hST H]
  exact hrank

end DimensionFourDependence
