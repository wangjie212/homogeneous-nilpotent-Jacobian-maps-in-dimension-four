import DimensionFourDependence.ActualChosenGraphDualPair
import DimensionFourDependence.ClosedGaussAlgebraicRealization

/-! # The same original graph dual pair survives the specified geometric coefficients -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

section Coefficients

variable {K C E B : Type*} [Field K] [Field C] [Field E] [Field B]
    [Algebra K C] [Algebra C E] [Algebra.IsAlgebraic C E] [Algebra K B]

/-- Algebraic coefficient images are algebraic over the very same
rational-parameter image under every specified compatible embedding. -/
theorem specified_algebraic_coefficient_image_algebraic_over_same_parameter
    (e : RatFunc K ≃ₐ[K] C) (g : C →ₐ[K] B) (σ : E →+* B)
    (hσ : ∀ c : C, σ (algebraMap C E c) = g c) (a : E) :
    IsAlgebraic (g.comp e.toAlgHom).fieldRange (σ a) := by
  have hrange : (g.comp e.toAlgHom).fieldRange = g.fieldRange := by
    ext b
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨e r, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨e.symm c, ?_⟩
      change g (e (e.symm c)) = g c
      rw [e.apply_symm_apply]
  rw [hrange]
  exact compatible_algebraic_coefficient_image_isAlgebraic_over_fieldRange g σ hσ a

end Coefficients

universe u

attribute [local instance] coefficientFieldScalarTower

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    {B : Type u} [Field B] [Algebra K B]

local notation "C₀" => closedGaussParameterField H I
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => (fun i => algebraMap C₀ E (e ((A) i)))
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

/-- One original dual pair, constructed on the actual chosen ruling,
retains its graph-ruling membership, all four dual values, coefficient
algebraicity and restriction independence in the specified geometric
coefficient realization. No conjugate embedding or new dual pair is
chosen after the coefficient map. -/
theorem actual_chosen_graph_dual_pair_retained_by_specified_coefficients
    (g : C₀ →ₐ[K] B) (σ : E →+* B)
    (hσ : ∀ c : C₀, σ (algebraMap C₀ E c) = g c)
    (m s : Fin 4 → E)
    (hpair : LinearIndependent E ![rulingFormRestriction W₀ m, rulingFormRestriction W₀ s]) :
    let f := g.comp e.toAlgHom
    let W := LinearMap.ker (dotProductBilin B B (fun i : Fin 3 => f (rationalParameterDerivative K ((A) i))))
    let m₃ := σ ∘ graphRestrictedCovector p (Aₑ) m
    let s₃ := σ ∘ graphRestrictedCovector p (Aₑ) s
    (∀ i, IsAlgebraic f.fieldRange (m₃ i)) ∧ (∀ i, IsAlgebraic f.fieldRange (s₃ i)) ∧
      ∃ b a : Fin 4 → E, b ∈ W₀ ∧ a ∈ W₀ ∧
        (fun i => σ (b (p i.castSucc))) ∈ W ∧ (fun i => σ (a (p i.castSucc))) ∈ W ∧
        m₃ ⬝ᵥ (fun i => σ (b (p i.castSucc))) = 1 ∧
        s₃ ⬝ᵥ (fun i => σ (b (p i.castSucc))) = 0 ∧
        m₃ ⬝ᵥ (fun i => σ (a (p i.castSucc))) = 0 ∧
        s₃ ⬝ᵥ (fun i => σ (a (p i.castSucc))) = 1 ∧
        LinearIndependent B ![rulingFormRestriction W m₃, rulingFormRestriction W s₃] := by
  let f := g.comp e.toAlgHom
  let W := LinearMap.ker (dotProductBilin B B (fun i : Fin 3 => f (rationalParameterDerivative K ((A) i))))
  let m₃ := graphRestrictedCovector p (Aₑ) m
  let s₃ := graphRestrictedCovector p (Aₑ) s
  refine ⟨fun i => specified_algebraic_coefficient_image_algebraic_over_same_parameter e g σ hσ (m₃ i),
    fun i => specified_algebraic_coefficient_image_algebraic_over_same_parameter e g σ hσ (s₃ i), ?_⟩
  obtain ⟨b, a, hb, ha, hbgraph, hagraph, hmb, hsb, hma, hsa, _hind⟩ :=
    actual_chosen_ruling_independent_forms_construct_original_graph_dual_pair
      H I p hY h hh e E hH hd hind hGauss m s hpair
  have hscalar (r : RatFunc K) : σ (algebraMap C₀ E (e r)) = f r := hσ (e r)
  have hbW : (fun i => σ (b (p i.castSucc))) ∈ W := by
    change (∑ i : Fin 3, f (rationalParameterDerivative K ((A) i)) * σ (b (p i.castSucc))) = 0
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * b (p i.castSucc)) = 0 at hbgraph
    simpa only [map_sum, map_mul, map_zero, hscalar] using congrArg σ hbgraph
  have haW : (fun i => σ (a (p i.castSucc))) ∈ W := by
    change (∑ i : Fin 3, f (rationalParameterDerivative K ((A) i)) * σ (a (p i.castSucc))) = 0
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * a (p i.castSucc)) = 0 at hagraph
    simpa only [map_sum, map_mul, map_zero, hscalar] using congrArg σ hagraph
  have hmb' : (σ ∘ m₃) ⬝ᵥ (fun i => σ (b (p i.castSucc))) = 1 := by
    simpa only [Function.comp_apply, dotProduct, map_sum, map_mul, map_one] using congrArg σ hmb
  have hsb' : (σ ∘ s₃) ⬝ᵥ (fun i => σ (b (p i.castSucc))) = 0 := by
    simpa only [Function.comp_apply, dotProduct, map_sum, map_mul, map_zero] using congrArg σ hsb
  have hma' : (σ ∘ m₃) ⬝ᵥ (fun i => σ (a (p i.castSucc))) = 0 := by
    simpa only [Function.comp_apply, dotProduct, map_sum, map_mul, map_zero] using congrArg σ hma
  have hsa' : (σ ∘ s₃) ⬝ᵥ (fun i => σ (a (p i.castSucc))) = 1 := by
    simpa only [Function.comp_apply, dotProduct, map_sum, map_mul, map_one] using congrArg σ hsa
  exact ⟨b, a, hb, ha, hbW, haW, hmb', hsb', hma', hsa',
    ruling_form_pair_independent_of_specified_dual_values W _ _ _ _ hbW haW hmb' hsb' hma' hsa'⟩

end DimensionFourDependence
