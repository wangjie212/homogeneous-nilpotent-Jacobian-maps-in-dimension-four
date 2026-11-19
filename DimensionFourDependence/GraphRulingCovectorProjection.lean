import DimensionFourDependence.GraphDenominatorCharacteristic
import DimensionFourDependence.RulingFormRelations

/-! # Original ruling covectors and dual vectors in a graph chart -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

section Projection

variable {E : Type*} [Field E]

/-- Restrict an original four-coordinate covector to the graph
whose omitted coordinate is the given linear combination. -/
noncomputable def graphRestrictedCovector
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → E) (c : Fin 4 → E) : Fin 3 → E :=
  fun i => c (p i.castSucc) + c (p 3) * A i

/-- The original covector pairing is exactly its graph restriction
paired with the projected original vector. -/
theorem graphRestrictedCovector_pairing
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → E) (c b : Fin 4 → E)
    (hb : b (p 3) = ∑ i : Fin 3, A i * b (p i.castSucc)) :
    graphRestrictedCovector p A c ⬝ᵥ (fun i => b (p i.castSucc)) = c ⬝ᵥ b := by
  have he : c ⬝ᵥ b =
      (∑ i : Fin 3, c (p i.castSucc) * b (p i.castSucc)) + c (p 3) * b (p 3) := by
    unfold dotProduct
    rw [← Equiv.sum_comp p (fun i => c i * b i), Fin.sum_univ_castSucc]
    rfl
  rw [he, hb]
  unfold dotProduct
  simp only [graphRestrictedCovector, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The same graph restriction commutes with a specified coefficient
embedding; every original coordinate label is retained. -/
theorem graphRestrictedCovector_field_map
    {F : Type*} [Field F] (g : E →+* F)
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → E) (c : Fin 4 → E) :
    graphRestrictedCovector p (g ∘ A) (g ∘ c) = g ∘ graphRestrictedCovector p A c := by
  funext i
  simp only [graphRestrictedCovector, Function.comp_apply, map_add, map_mul]

/-- A specified dual pair proves independence of the two restricted
forms on their actual ruling. No new dual basis is selected. -/
theorem ruling_form_pair_independent_of_specified_dual_values
    {n : ℕ} (W : Submodule E (Fin n → E)) (m s b a : Fin n → E)
    (hb : b ∈ W) (ha : a ∈ W)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    (hma : m ⬝ᵥ a = 0) (hsa : s ⬝ᵥ a = 1) :
    LinearIndependent E ![rulingFormRestriction W m, rulingFormRestriction W s] := by
  rw [LinearIndependent.pair_iff]
  intro u v huv
  have hb' := LinearMap.congr_fun huv ⟨b, hb⟩
  have ha' := LinearMap.congr_fun huv ⟨a, ha⟩
  change u * (m ⬝ᵥ b) + v * (s ⬝ᵥ b) = 0 at hb'
  change u * (m ⬝ᵥ a) + v * (s ⬝ᵥ a) = 0 at ha'
  exact ⟨by simpa only [hmb, hsb, mul_one, mul_zero, add_zero] using hb',
    by simpa only [hma, hsa, mul_one, mul_zero, zero_add] using ha'⟩

end Projection

section Ruling

variable {K C E : Type*} [Field K] [Field C] [Field E] [Algebra K C]

/-- The original normal ruling equations give both graph equations
after every specified coefficient embedding. The arbitrary normal
representative and rational parameter change introduce no new ruling
hypothesis. -/
theorem original_normal_ruling_constructs_graph_projection_equations
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (v : Fin 4 → RatFunc K)
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) (a : C)
    (hgraph : ∀ i, f (v i) = a * parameterGraphNormal p A i)
    (ha : a ≠ 0) (g : C →+* E) (b : Fin 4 → E)
    (hb : (normalRulingMatrix (rationalParameterDerivative K) v).map
      (g.comp f.toRingHom) *ᵥ b = 0) :
    b (p 3) = ∑ i : Fin 3, g (A i) * b (p i.castSucc) ∧
      (∑ i : Fin 3, g (D (A i)) * b (p i.castSucc)) = 0 := by
  have hzero : (∑ i, g (f (v i)) * b i) = 0 := congrFun hb 0
  have hfirst : (∑ i, g (f (rationalParameterDerivative K (v i))) * b i) = 0 := congrFun hb 1
  have hcoverFirst : (∑ i, g (D (f (v i))) * b i) = 0 := by
    calc
      _ = g (D (f RatFunc.X)) * ∑ i, g (f (rationalParameterDerivative K (v i))) * b i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [rational_parameter_chain_rule f D (v i), map_mul]
        ring
      _ = 0 := by rw [hfirst, mul_zero]
  have hzeroScaled : (∑ i, g (a * parameterGraphNormal p A i) * b i) = 0 := by
    simpa only [← hgraph] using hzero
  have hfirstScaled : (∑ i, g (D (a * parameterGraphNormal p A i)) * b i) = 0 := by
    simpa only [← hgraph] using hcoverFirst
  obtain ⟨hlin, hder⟩ := rescaled_normal_ruling_pairings D a (parameterGraphNormal p A) g b
    ha hzeroScaled hfirstScaled
  rw [← Equiv.sum_comp p (fun i => g (parameterGraphNormal p A i) * b i),
    Fin.sum_univ_castSucc] at hlin
  simp only [parameterGraphNormal, Function.comp_apply, Equiv.symm_apply_apply,
    Fin.snoc_castSucc, Fin.snoc_last, map_neg, map_one, one_mul, neg_mul,
    Finset.sum_neg_distrib] at hlin
  change -(∑ i : Fin 3, g (A i) * b (p i.castSucc)) + b (p 3) = 0 at hlin
  rw [← Equiv.sum_comp p (fun i => g (D (parameterGraphNormal p A i)) * b i),
    Fin.sum_univ_castSucc] at hder
  simp only [parameterGraphNormal, Function.comp_apply, Equiv.symm_apply_apply,
    Fin.snoc_castSucc, Fin.snoc_last, map_neg, D.map_one_eq_zero, map_zero,
    zero_mul, add_zero, neg_mul, Finset.sum_neg_distrib] at hder
  exact ⟨by linear_combination hlin, neg_eq_zero.mp hder⟩

end Ruling

end DimensionFourDependence
