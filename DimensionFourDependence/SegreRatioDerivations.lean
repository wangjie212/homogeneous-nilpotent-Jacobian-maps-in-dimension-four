import DimensionFourDependence.SegreRulingDirectionCalculus

/-! # The actual commuting coordinate derivatives in the two original Segre ratios -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 1500000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- Scale an original output partial by the original radial output. -/
noncomputable def segreRatioDerivation (δ : Fin 3 → Derivation K E E)
    (Y : Fin 3 → E) (j : Fin 3) : Derivation K E E := Y 0 • δ j

@[simp]
theorem segreRatioDerivation_apply (δ : Fin 3 → Derivation K E E)
    (Y : Fin 3 → E) (j : Fin 3) (a : E) :
    segreRatioDerivation δ Y j a = Y 0 * δ j a := rfl

/-- The actual scaled partial has the exact coordinate derivative on
each original ratio, without an independent-coordinate identification. -/
theorem segreRatioDerivation_ratio
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (hY0 : Y 0 ≠ 0) (j : Fin 3) (hj : j ≠ 0) (i : Fin 3) :
    segreRatioDerivation δ Y j (Y i / Y 0) = if i = j then 1 else 0 := by
  rw [segreRatioDerivation_apply, (δ j).leibniz_div, hcoord, hcoord]
  simp only [Ne.symm hj, ite_false, smul_eq_mul, mul_zero, sub_zero]
  split_ifs <;> field_simp [hY0]

/-- The two actual scaled original output partials commute because
they both fix the original radial output and the original partials commute. -/
theorem segreRatioDerivations_commute
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (j k : Fin 3) (hj : j ≠ 0) (hk : k ≠ 0) (x : E) :
    segreRatioDerivation δ Y j (segreRatioDerivation δ Y k x) =
      segreRatioDerivation δ Y k (segreRatioDerivation δ Y j x) := by
  simp only [segreRatioDerivation_apply, Derivation.leibniz, hcoord,
    Ne.symm hj, Ne.symm hk, ite_false, smul_eq_mul, mul_zero, add_zero]
  rw [hcomm]

end DimensionFourDependence
