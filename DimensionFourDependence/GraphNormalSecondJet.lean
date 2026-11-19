import DimensionFourDependence.GraphNormalParameterRuling

/-! # The second normal jet on the actual ruling is the graph denominator

Multiplying the graph normal by a nonzero parameter coefficient changes
its second derivative by lower-jet terms. On the actual ruling those
terms vanish, leaving exactly minus the normal pivot times the graph
gradient's second derivative.
-/

namespace DimensionFourDependence

open Matrix

section Pairings

variable {K C E : Type*} [Field K] [Field C] [Field E] [Algebra K C]

/-- The exact second product derivative over a field. -/
theorem derivation_second_product
    (D : Derivation K C C) (a b : C) :
    D (D (a * b)) = D (D a) * b + 2 * D a * D b + a * D (D b) := by
  rw [D.leibniz, map_add]
  simp only [smul_eq_mul]
  rw [D.leibniz, D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- On a direction killing a rescaled normal and its derivative,
the original normal and its derivative also vanish. -/
theorem rescaled_normal_ruling_pairings
    (D : Derivation K C C) (a : C) (v : Fin 4 → C) (g : C →+* E) (b : Fin 4 → E)
    (ha : a ≠ 0)
    (hzero : (∑ i, g (a * v i) * b i) = 0)
    (hfirst : (∑ i, g (D (a * v i)) * b i) = 0) :
    (∑ i, g (v i) * b i) = 0 ∧ (∑ i, g (D (v i)) * b i) = 0 := by
  have haz : g a ≠ 0 := (map_ne_zero g).mpr ha
  have hzero' : g a * (∑ i, g (v i) * b i) = 0 := by
    simpa only [Finset.mul_sum, map_mul, mul_assoc] using hzero
  have hv := (mul_eq_zero.mp hzero').resolve_left haz
  have hfirst' : g (D a) * (∑ i, g (v i) * b i) + g a * (∑ i, g (D (v i)) * b i) = 0 := by
    calc
      _ = ∑ i, g (D (a * v i)) * b i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [D.leibniz]
        simp only [smul_eq_mul, map_add, map_mul]
        ring
      _ = 0 := hfirst
  rw [hv, mul_zero, zero_add] at hfirst'
  exact ⟨hv, (mul_eq_zero.mp hfirst').resolve_left haz⟩

/-- The lower terms in the second rescaled-normal pairing vanish
on the actual ruling, leaving the original second pairing times a. -/
theorem rescaled_normal_second_pairing
    (D : Derivation K C C) (a : C) (v : Fin 4 → C) (g : C →+* E) (b : Fin 4 → E)
    (hzero : (∑ i, g (v i) * b i) = 0)
    (hfirst : (∑ i, g (D (v i)) * b i) = 0) :
    (∑ i, g (D (D (a * v i))) * b i) = g a * ∑ i, g (D (D (v i))) * b i := by
  calc
    _ = ∑ i, (g (D (D a)) * (g (v i) * b i) +
        g (2 * D a) * (g (D (v i)) * b i) + g a * (g (D (D (v i))) * b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [derivation_second_product]
      simp only [map_add, map_mul]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hzero, hfirst, mul_zero, mul_zero, zero_add, zero_add]

end Pairings

end DimensionFourDependence
