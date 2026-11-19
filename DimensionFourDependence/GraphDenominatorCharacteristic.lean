import DimensionFourDependence.RationalCoverJetComparison
import DimensionFourDependence.GraphNormalSecondJet

/-! # The graph denominator's zero direction is the actual characteristic direction

The normal's scalar representative and a rational parameter change
contribute only lower normal jets and nonzero scalar factors. On the
actual ruling these lower jets vanish. The original characteristic
matrix therefore vanishes exactly on the kernel of the pivot-normalized
second-graph-derivative covector used by the root construction.
-/

namespace DimensionFourDependence

open Matrix

variable {K C E : Type*} [Field K] [Field C] [Field E] [Algebra K C]

/-- The graph normal in the original four source coordinate labels. -/
noncomputable def parameterGraphNormal (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) : Fin 4 → C :=
  Fin.snoc (fun i => -A i) 1 ∘ p.symm

/-- The second graph-normal derivative has exactly minus the
original three-coordinate second-gradient pairing. -/
theorem parameterGraphNormal_second_pairing
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) (D : Derivation K C C)
    (g : C →+* E) (b : Fin 4 → E) :
    (∑ i, g (D (D (parameterGraphNormal p A i))) * b i) =
      -(∑ j : Fin 3, g (D (D (A j))) * b (p j.castSucc)) := by
  rw [← Equiv.sum_comp p (fun i => g (D (D (parameterGraphNormal p A i))) * b i),
    Fin.sum_univ_castSucc]
  simp only [parameterGraphNormal, Function.comp_apply, Equiv.symm_apply_apply,
    Fin.snoc_castSucc, Fin.snoc_last, map_neg, D.map_one_eq_zero, map_zero,
    zero_mul, add_zero, neg_mul, Finset.sum_neg_distrib]

/-- The pivot-normalized graph second-derivative covector in the
original coordinate labels, after a specified coefficient embedding. -/
noncomputable def parameterGraphRootNumerator
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) (D : Derivation K C C) (a : C) (g : C →+* E) : Fin 4 → E :=
  (g a)⁻¹ • (Fin.snoc (fun i => g (D (D (A i)))) 0 ∘ p.symm)

/-- The actual numerator's scalar pairing retains its original
second-graph-derivative value and exact inverse pivot. -/
theorem parameterGraphRootNumerator_pairing
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) (D : Derivation K C C)
    (a : C) (g : C →+* E) (b : Fin 4 → E) :
    parameterGraphRootNumerator p A D a g ⬝ᵥ b =
      (g a)⁻¹ * ∑ j : Fin 3, g (D (D (A j))) * b (p j.castSucc) := by
  rw [parameterGraphRootNumerator, smul_dotProduct]
  change (g a)⁻¹ * (∑ i, (Fin.snoc (fun j => g (D (D (A j)))) 0 ∘ p.symm) i * b i) = _
  rw [← Equiv.sum_comp p (fun i => (Fin.snoc (fun j => g (D (D (A j)))) 0 ∘ p.symm) i * b i),
    Fin.sum_univ_castSucc]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]

/-- The original characteristic matrix and actual graph-root
numerator have exactly the same zero directions on the original ruling,
including every coefficient extension. No characteristic membership
or parameter-change factor is assumed. -/
theorem graph_root_numerator_zero_iff_original_characteristic
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (v : Fin 4 → RatFunc K)
    (p : Equiv.Perm (Fin 4)) (A : Fin 3 → C) (a : C)
    (hgraph : ∀ i, f (v i) = a * parameterGraphNormal p A i)
    (ha : a ≠ 0) (hspeed : D (f RatFunc.X) ≠ 0)
    (g : C →+* E) (b : Fin 4 → E)
    (hb : (normalRulingMatrix (rationalParameterDerivative K) v).map
      (g.comp f.toRingHom) *ᵥ b = 0) :
    parameterGraphRootNumerator p A D a g ⬝ᵥ b = 0 ↔
      (normalCharacteristicMatrix (rationalParameterDerivative K) v).map
        (g.comp f.toRingHom) *ᵥ b = 0 := by
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
  have hpair := rescaled_normal_ruling_pairings D a (parameterGraphNormal p A) g b ha hzeroScaled hfirstScaled
  have hsecond : (∑ i, g (D (D (f (v i)))) * b i) =
      -g a * ∑ j : Fin 3, g (D (D (A j))) * b (p j.castSucc) := by
    simp_rw [hgraph]
    rw [rescaled_normal_second_pairing D a (parameterGraphNormal p A) g b hpair.1 hpair.2,
      parameterGraphNormal_second_pairing]
    ring
  have hchar := rational_cover_characteristic_matrix_zero_iff f D v g b hspeed hb
  have hga : g a ≠ 0 := (map_ne_zero g).mpr ha
  rw [hchar, hsecond, parameterGraphRootNumerator_pairing, mul_eq_zero,
    or_iff_right (inv_ne_zero hga), mul_eq_zero, or_iff_right (neg_ne_zero.mpr hga)]

end DimensionFourDependence
