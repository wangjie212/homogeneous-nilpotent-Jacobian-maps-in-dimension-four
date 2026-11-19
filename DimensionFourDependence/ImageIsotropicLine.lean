import DimensionFourDependence.CoefficientIsotropicLine
import DimensionFourDependence.NormalizedGraphLines

/-! # Algebraic isotropic directions give lines on the actual image equation

The image equation is transported to the selected graph chart and the
constructed coefficient partials integrate the normalized direction.
The final identity is expressed in the original output-coordinate order.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

section

variable (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Q" => (fun i : Fin 4 => algebraMap (MvPolynomial (Fin 4) K) F (H i))
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) F (H (p (Fin.castSucc i))))
local notation "L" => coefficientField (K := K) Y

omit [CharZero K] in
/-- The original image equation vanishes at the actual coefficient-field
graph point after the simultaneous chart permutation. -/
theorem ImageRelationWitness.coefficient_chart_relation
    (h : L) (hh : (h : F) = Q (p 3)) (W : ImageRelationWitness H) :
    aeval (Fin.snoc (coefficientCoordinate (K := K) Y) h) (rename p.symm W.equation) = 0 := by
  apply (algebraMap L F).injective
  rw [map_zero]
  have hpoint : (fun j : Fin 4 => algebraMap L F
      ((Fin.snoc (coefficientCoordinate (K := K) Y) h : Fin 4 → L) j)) = Q ∘ p := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Function.comp_apply, IntermediateField.algebraMap_apply]
      exact hh
    · simp only [Fin.snoc_castSucc, Function.comp_apply]
      rfl
  have hRQ : aeval Q W.equation = 0 := by
    rw [← aeval_polynomial_to_fraction, W.vanishing, map_zero]
  calc
    algebraMap L F (aeval (Fin.snoc (coefficientCoordinate (K := K) Y) h)
        (rename p.symm W.equation)) =
        aeval (fun j => algebraMap L F ((Fin.snoc (coefficientCoordinate (K := K) Y) h : Fin 4 → L) j))
          (rename p.symm W.equation) :=
      comp_aeval_apply _ (IsScalarTower.toAlgHom K L F) _
    _ = aeval (Q ∘ p) (rename p.symm W.equation) := by rw [hpoint]
    _ = aeval Q W.equation := by
      rw [aeval_rename]
      have hf : (Q ∘ p) ∘ p.symm = Q := by
        funext i
        simp only [Function.comp_apply, p.apply_symm_apply]
      rw [hf]
    _ = 0 := hRQ

/-- The actual image contains the entire line obtained from an algebraic
normalized direction satisfying the Hessian and cubic conditions (3.4).
The radial identity and all extended derivations are constructed. -/
theorem ImageRelationWitness.normalized_isotropic_line
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (h : L) (hh : (h : F) = Q (p 3)) (W : ImageRelationWitness H)
    (E : Type*) [Field E] [CharZero E] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] [Algebra.IsAlgebraic L E]
    (hrank : ((coefficientHessian Y hY h).map (algebraMap L E)).rank = 2)
    (Z : Fin 3 → E) (a b : Fin 3)
    (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap L E)) Z Z = 0)
    (hCubic : (∑ i, ∑ j, ∑ k, algebraMap L E (coefficientCubicTensor Y hY h i j k) *
      Z i * Z j * Z k) = 0) :
    aeval (fun j : Fin 4 =>
      Polynomial.C ((Fin.snoc (fun i => algebraMap L E (coefficientCoordinate (K := K) Y i))
        (algebraMap L E h) : Fin 4 → E) (p.symm j)) +
      Polynomial.C ((Fin.snoc Z (∑ i, Z i * algebraMap L E (coefficientGradient Y hY h i)) : Fin 4 → E)
        (p.symm j)) * Polynomial.X) W.equation = 0 := by
  have hYa : algebraMap L E (coefficientCoordinate (K := K) Y a) ≠ 0 := by
    intro hz
    have hc : coefficientCoordinate (K := K) Y a = 0 :=
      (algebraMap L E).injective (by simpa only [map_zero] using hz)
    apply (hY.transcendental a).ne_zero
    exact congrArg (fun z : L => (z : F)) hc
  have hline := coefficient_normalized_isotropic_direction_line Y hY E h
    (homogeneous_last_output_euler H hd hH p hY h hh) hrank Z a b hYa hZa hZb hZ hCubic
    (rename p.symm W.equation) (W.coefficient_chart_relation H p h hh)
  simpa only [aeval_rename, Function.comp_def] using hline

end

end DimensionFourDependence
