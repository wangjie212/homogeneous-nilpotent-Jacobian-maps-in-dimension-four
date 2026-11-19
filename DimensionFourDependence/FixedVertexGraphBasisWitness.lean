import DimensionFourDependence.FixedVertexIndependentGraphBasis

/-! # Explicit original fixed-axis graph basis witnesses -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

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
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap (closedGaussParameterField H I) E (e ((A) i))
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "Wg" => extendedClosedGaussGraphRuling H I p hY h hh e E

/-- Independence of the two original output forms on the chosen ruling.
A named predicate keeps this dependent linear-map type fixed when a
further target field is introduced. -/
noncomputable def IndependentOriginalChosenRulingForms (M S : Fin 4 → E) : Prop :=
  LinearIndependent E ![rulingFormRestriction (W₀) M, rulingFormRestriction (W₀) S]

/-- Expose both original graph basis vectors as ordinary existential
witnesses, retaining the exact scaled fourth axis and every dual value. -/
theorem fixed_vertex_root_forms_construct_explicit_original_graph_basis_witnesses
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (M S : Fin 4 → E) (hM : M (Fin.last 3) ≠ 0) (hS : S (Fin.last 3) = 0)
    (hpair : IndependentOriginalChosenRulingForms H I E hH hd hind hGauss M S) :
    ∃ b a : Fin 4 → E, b = (M (Fin.last 3))⁻¹ • (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) ∧
      b ∈ (W₀) ∧ a ∈ (W₀) ∧ (fun i => b (p i.castSucc)) ∈ (Wg) ∧
      (fun i => a (p i.castSucc)) ∈ (Wg) ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => b (p i.castSucc)) = 1 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => b (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => a (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => a (p i.castSucc)) = 1 := by
  let b : Fin 4 → E := (M (Fin.last 3))⁻¹ • (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E)
  have hfixed : ∃ a : Fin 4 → E, b ∈ (W₀) ∧ a ∈ (W₀) ∧
      (fun i => b (p i.castSucc)) ∈ (Wg) ∧ (fun i => a (p i.castSucc)) ∈ (Wg) ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => b (p i.castSucc)) = 1 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => b (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => a (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => a (p i.castSucc)) = 1 ∧
      LinearIndependent E ![rulingFormRestriction (Wg) (graphRestrictedCovector p (Aₑ) M),
        rulingFormRestriction (Wg) (graphRestrictedCovector p (Aₑ) S)] :=
    independent_fixed_vertex_root_forms_construct_original_axis_graph_dual_pair
      H I p hY h hh e E hH hd hind hGauss hvertex M S hM hS hpair
  obtain ⟨a, hb, ha, hbgraph, hagraph, hmb, hsb, hma, hsa, _hpairGraph⟩ := hfixed
  exact ⟨b, a, rfl, hb, ha, hbgraph, hagraph, hmb, hsb, hma, hsa⟩

end DimensionFourDependence
