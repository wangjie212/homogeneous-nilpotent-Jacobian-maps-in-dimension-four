import DimensionFourDependence.RulingRemainderRootComparison
import DimensionFourDependence.ClosedParameterVectorDescent

/-! # The actual finite ruling extension retains its selected remainder root under comparison -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000

variable {K E κ : Type u} [Field K] [CharZero K] [Field E] [IsAlgClosed E] [Field κ]
    [Algebra K E] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]

/-- Compare a finite-parameter factorization with a constant-coefficient
generic ruling value while retaining the selected root in its original
coordinate field. Both covector descent and root uniqueness are derived. -/
theorem finite_parameter_factored_value_preserves_selected_remainder_root
    (D : Derivation K E E) (s t : E) (hs : D s = 1) (ht : D t = 0)
    (C : IntermediateField (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) κ)
    (hC : Module.Finite (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) C)
    (a b : Fin 2 → C) (c e : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (hc : ∀ i, D (c i) = 0) (he : ∀ i, D (e i) = 0)
    (v : E) (hv : v ≠ 0)
    (hlocal : algebraMap E κ v =
      Polynomial.aeval (algebraMap E κ s) (segreRulingPowerPolynomial a b d))
    (hglobal : v = (segreRulingPowerPolynomial c e d).eval s)
    (w : Fin 2 → κ)
    (hroot : algebraMap C κ (a 0) * w 0 + algebraMap C κ (a 1) * w 1 = 0) :
    algebraMap E κ (c 0) * w 0 + algebraMap E κ (c 1) * w 1 = 0 := by
  obtain ⟨A, B, hAmap, _hBmap, hAalg, hBalg, hvalue⟩ :=
    finite_parameter_linear_power_value_descends_to_closed_constants t s v C hC a b d hlocal
  have hA (i : Fin 2) : D (A i) = 0 :=
    derivation_zero_of_algebraic_parameter_constant D t ht _ (hAalg i)
  have hB (i : Fin 2) : D (B i) = 0 :=
    derivation_zero_of_algebraic_parameter_constant D t ht _ (hBalg i)
  apply ruling_factored_generic_value_preserves_remainder_root D s hs A B c e d hd hA hB hc he
    (hvalue.symm.trans hglobal) (by rw [← hvalue]; exact hv) (algebraMap E κ) w
  rw [hAmap 0, hAmap 1]
  exact hroot

end DimensionFourDependence
