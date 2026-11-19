import DimensionFourDependence.FixedVertexFiniteGraphBasisData
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

/-- The constructed original fixed-axis pair descends into a finite
field over the exact original graph parameter image. Its power,
denominator and both directions keep all dual values, and the fixed
direction is explicitly the original fourth axis. -/
theorem original_fixed_vertex_independent_forms_construct_finite_graph_basis
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hcompat :
      letI : Algebra C₀ κ := ((algebraMap (L) κ).comp (a₀).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (M S : Fin 4 → E) (hM : M (Fin.last 3) ≠ 0) (hS : S (Fin.last 3) = 0)
    (hpair : IndependentOriginalChosenRulingForms H I E hH hd hind hGauss M S) :
    ActualFiniteOriginalFixedGraphBasisExists H I p hY h hh E e κ M S := by
  have hbase := @fixed_vertex_root_forms_construct_explicit_original_graph_basis_witnesses
    K fieldK charK H I p hY h hh e E fieldE algCE d hH hd hind hGauss hvertex M S hM hS hpair
  obtain ⟨bE, aE, hbEq, _hbE, _haE, hbgraph, hagraph, hmb, hsb, hma, hsa⟩ := hbase
  let : Algebra C₀ κ := ((algebraMap (L) κ).comp (a₀).toRingHom).toAlgebra
  let : IsScalarTower C₀ E κ := hcompat
  let gC := (g).comp (a₀)
  let σ := algebraMap E κ
  have hσ (c : C₀) : σ (algebraMap C₀ E c) = gC c :=
    (IsScalarTower.algebraMap_apply C₀ E κ c).symm
  have hf : gC.comp e.toAlgHom = (f) := by
    apply AlgHom.ext
    intro r
    exact congrArg (g) (actualClosedGaussCoefficientHom_parameter_value H I p hY h hh e r)
  have halg (z : E) : IsAlgebraic (f).fieldRange (σ z) := by
    rw [← hf]
    exact specified_algebraic_coefficient_image_algebraic_over_same_parameter e gC σ hσ z
  have hscalar (r : RatFunc K) : σ (algebraMap C₀ E (e r)) = (f) r := by
    rw [hσ]
    exact DFunLike.congr_fun hf r
  let mF := fun i => σ (graphRestrictedCovector p (Aₑ) M i)
  let sF := fun i => σ (graphRestrictedCovector p (Aₑ) S i)
  let bF := fun i : Fin 3 => σ (bE (p i.castSucc))
  let aF := fun i : Fin 3 => σ (aE (p i.castSucc))
  have hbF : (fun i => (f) (rationalParameterDerivative K ((A) i))) ⬝ᵥ bF = 0 := by
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * bE (p i.castSucc)) = 0 at hbgraph
    simpa only [map_sum, map_mul, map_zero, hscalar, dotProduct] using congrArg σ hbgraph
  have haF : (fun i => (f) (rationalParameterDerivative K ((A) i))) ⬝ᵥ aF = 0 := by
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * aE (p i.castSucc)) = 0 at hagraph
    simpa only [map_sum, map_mul, map_zero, hscalar, dotProduct] using congrArg σ hagraph
  have hmbF : mF ⬝ᵥ bF = 1 := by simpa only [dotProduct, map_sum, map_mul, map_one] using congrArg σ hmb
  have hsbF : sF ⬝ᵥ bF = 0 := by simpa only [dotProduct, map_sum, map_mul, map_zero] using congrArg σ hsb
  have hmaF : mF ⬝ᵥ aF = 0 := by simpa only [dotProduct, map_sum, map_mul, map_zero] using congrArg σ hma
  have hsaF : sF ⬝ᵥ aF = 1 := by simpa only [dotProduct, map_sum, map_mul, map_one] using congrArg σ hsa
  obtain ⟨C, hfinite, m, s, b, a, hm, hs, hb, _ha, hbW, haW, hmbC, hsbC, hmaC, hsaC, hpairC⟩ :=
    algebraic_graph_dual_pair_constructs_same_finite_ruling_field (K := K) (F := κ) (f) (A) mF sF bF aF
      (fun i => halg _) (fun i => halg _) (fun i => halg _) (fun i => halg _)
      hbF haF hmbF hsbF hmaF hsaF
  exact ⟨C, hfinite, m, s, b, a, hm, hs,
    (fun i => (hb i).trans (congrArg σ (congrFun hbEq (p i.castSucc)))),
    hbW, haW, hmbC, hsbC, hmaC, hsaC, hpairC⟩

end DimensionFourDependence
