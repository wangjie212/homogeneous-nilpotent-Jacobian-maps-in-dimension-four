import DimensionFourDependence.AffinePlaneCurveDichotomy
import DimensionFourDependence.SourceRealizationFiberComponent

/-! # Affine plane conics and their original linear coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2200000

variable {E F G : Type u} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G] {n : ℕ}

/-- A closed affine plane conic in the ambient coordinates, with a
split affine plane embedding and its entire plane relation ideal. -/
structure AffinePlaneConic (y : Fin n → F) where
  origin : Fin n → E
  plane : Matrix (Fin n) (Fin 2) E
  leftInverse : Matrix (Fin 2) (Fin n) E
  split : leftInverse * plane = 1
  coordinates : Fin 2 → F
  point : y = algebraMap E F ∘ origin + plane.map (algebraMap E F) *ᵥ coordinates
  equation : MvPolynomial (Fin 2) E
  irreducible : Irreducible equation
  degree_two : equation.totalDegree = 2
  relations : fiberVanishingIdeal (L := E) coordinates = Ideal.span {equation}

theorem AffinePlaneCurveChart.exists_affinePlaneConic {y : Fin n → F}
    (W : AffinePlaneCurveChart (E := E) y) (hd : W.equation.totalDegree = 2) :
    Nonempty (AffinePlaneConic (E := E) y) := by
  classical
  let o : Fin n → E := fun i => (W.coordinate i).coeff 0
  let B : Matrix (Fin n) (Fin 2) E := fun i j => (pderiv j (W.coordinate i)).coeff 0
  let D : Matrix (Fin 2) (Fin n) E := fun i j => if j = W.projection i then 1 else 0
  let w := fun i => y (W.projection i)
  have hDB : D * B = 1 := by
    funext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (W.projection i)]
    · simp only [D, B, ite_eq_left rfl, one_mul, W.projection_identity, pderiv_X]
      by_cases h : j = i
      · subst j
        simp
      · simp [Ne.symm h]
    · intro k _ hk
      simp [D, hk]
    · simp
  refine ⟨⟨o, B, D, hDB, w, ?_, W.equation, W.equation_irreducible, hd, W.relation_ideal⟩⟩
  funext i
  change y i = algebraMap E F (o i) + ∑ j, algebraMap E F (B i j) * w j
  have h := congrArg (aeval w) (affine_polynomial_expansion (W.coordinate i) (W.degree_le_one i))
  simpa only [W.coordinate_value i, map_add, map_sum, map_mul, aeval_C, aeval_X, o, B, w] using h

noncomputable def AffinePlaneConic.map {y : Fin n → F} (W : AffinePlaneConic (E := E) y)
    (f : F →ₐ[E] G) : AffinePlaneConic (E := E) (f ∘ y) where
  origin := W.origin
  plane := W.plane
  leftInverse := W.leftInverse
  split := W.split
  coordinates := f ∘ W.coordinates
  point := by
    funext i
    have h := congrArg (fun v : Fin n → F => f (v i)) W.point
    simpa only [Pi.add_apply, Function.comp_apply, map_add, Matrix.mulVec, dotProduct,
      Matrix.map_apply, map_sum, map_mul, f.commutes] using h
  equation := W.equation
  irreducible := W.irreducible
  degree_two := W.degree_two
  relations := (fiberVanishingIdeal_algHom f W.coordinates).trans W.relations

noncomputable def AffinePlaneConic.mulVec {y : Fin n → F} (W : AffinePlaneConic (E := E) y)
    (A D : Matrix (Fin n) (Fin n) E) (h : D * A = 1) :
    AffinePlaneConic (E := E) (A.map (algebraMap E F) *ᵥ y) where
  origin := A *ᵥ W.origin
  plane := A * W.plane
  leftInverse := W.leftInverse * D
  split := by rw [Matrix.mul_assoc W.leftInverse, ← Matrix.mul_assoc D, h, Matrix.one_mul, W.split]
  coordinates := W.coordinates
  point := by
    conv_lhs => rw [W.point]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.map_mul]
    exact congrArg (fun v : Fin n → F => v + (A.map (algebraMap E F) * W.plane.map (algebraMap E F)) *ᵥ
      W.coordinates) (funext fun i => (RingHom.map_mulVec (algebraMap E F) A W.origin i).symm)
  equation := W.equation
  irreducible := W.irreducible
  degree_two := W.degree_two
  relations := W.relations

end DimensionFourDependence
