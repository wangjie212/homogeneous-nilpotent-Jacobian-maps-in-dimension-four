import DimensionFourDependence.FixedVertexIndependentGraphBasis
import DimensionFourDependence.OriginalGraphTensorValues
import DimensionFourDependence.SpecifiedGraphDualTransport
import DimensionFourDependence.FiniteAlgebraicGraphDualPair
import DimensionFourDependence.FixedVertexGraphBasisWitness

/-! # The original fixed-axis graph basis constructs its finite parameter field -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [fieldK : Field K] [charK : CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [fieldE : Field E] [algCE : Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a₀" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "W₀" => LinearMap.ker ((extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin' : (Fin 4 → E) →ₗ[E] (Fin 2 → E))

variable (κ : Type u) [Field κ] [Algebra K κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]
    [IsScalarTower K (coefficientField (K := K)
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ] [Algebra E κ]

local notation "g" => IsScalarTower.toAlgHom K (L) κ
local notation "f" => (g).comp (f₀)

/-- Exact finite graph basis data, including the original scaled
fourth-axis direction and all four dual values. -/
noncomputable def ActualFiniteOriginalFixedGraphBasisExists (M S : Fin 4 → E) : Prop :=
    ∃ C : IntermediateField (f).fieldRange κ, Module.Finite (f).fieldRange C ∧
      ∃ m s b a : Fin 3 → C,
        (∀ i, (m i : κ) = algebraMap E κ (graphRestrictedCovector p (Aₑ) M i)) ∧
        (∀ i, (s i : κ) = algebraMap E κ (graphRestrictedCovector p (Aₑ) S i)) ∧
        (∀ i, (b i : κ) = algebraMap E κ (((M (Fin.last 3))⁻¹ •
          (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E)) (p i.castSucc))) ∧
        b ∈ finiteParameterGraphRuling (f) C (A) ∧ a ∈ finiteParameterGraphRuling (f) C (A) ∧
        m ⬝ᵥ b = 1 ∧ s ⬝ᵥ b = 0 ∧ m ⬝ᵥ a = 0 ∧ s ⬝ᵥ a = 1 ∧
        LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling (f) C (A)) m,
          rulingFormRestriction (finiteParameterGraphRuling (f) C (A)) s]

end DimensionFourDependence
