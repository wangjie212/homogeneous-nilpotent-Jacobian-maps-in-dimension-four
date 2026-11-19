import DimensionFourDependence.RationalParameterConstants
import DimensionFourDependence.GaussCharacteristicSubspaces

/-! # Actual first and second normal jets under a rational parameter cover

The chain rule expresses the second derivative after changing parameter
as a nonzero scalar times the original second derivative, plus a first
derivative term. On the actual ruling the latter term vanishes. The
nonzero scalar is derived for every original rational parameter embedded
in a rational closed cover.
-/

namespace DimensionFourDependence

open Matrix

section Constants

variable {K C : Type*} [Field K] [CharZero K] [Field C] [Algebra K C]

/-- The derivative in a rational cover is nonzero on the image of
every original rational parameter. No separability scalar is supplied. -/
theorem rational_cover_parameter_derivative_ne_zero
    (e : RatFunc K ≃ₐ[K] C) (f : RatFunc K →ₐ[K] C) :
    fieldDerivationConjugate e (rationalParameterDerivative K) (f RatFunc.X) ≠ 0 := by
  intro hz
  change e (rationalParameterDerivative K (e.symm (f RatFunc.X))) = 0 at hz
  have hzero : rationalParameterDerivative K (e.symm (f RatFunc.X)) = 0 := by
    apply e.injective
    rw [map_zero]
    exact hz
  obtain ⟨c, hc⟩ := (rationalParameterDerivative_eq_zero_iff_scalar _).mp hzero
  have hscalar : f RatFunc.X = algebraMap K C c := by
    calc
      _ = e (e.symm (f RatFunc.X)) := (e.apply_symm_apply _).symm
      _ = e (algebraMap K (RatFunc K) c) := congrArg e hc
      _ = _ := e.commutes c
  have hpre : RatFunc.X = algebraMap K (RatFunc K) c :=
    f.injective (hscalar.trans (f.commutes c).symm)
  have htrans : Transcendental K (RatFunc.X : RatFunc K) := RatFunc.transcendental_X
  apply htrans
  rw [hpre]
  exact isAlgebraic_algebraMap c

end Constants

section Jets

variable {K C E : Type*} [Field K] [Field C] [Field E] [Algebra K C]

/-- The full second rational chain rule, retaining the original
first derivative contribution and the actual parameter-speed square. -/
theorem rational_parameter_second_chain_rule
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (r : RatFunc K) :
    D (D (f r)) = f (rationalParameterDerivative K (rationalParameterDerivative K r)) *
      D (f RatFunc.X) ^ 2 + f (rationalParameterDerivative K r) * D (D (f RatFunc.X)) := by
  calc
    _ = D (f (rationalParameterDerivative K r) * D (f RatFunc.X)) :=
      congrArg D (rational_parameter_chain_rule f D r)
    _ = _ := by
      rw [D.leibniz, rational_parameter_chain_rule f D (rationalParameterDerivative K r)]
      simp only [smul_eq_mul]
      ring

/-- On a direction annihilating the original first normal jet,
the second-jet pairing changes only by the actual speed square. -/
theorem rational_normal_second_jet_pairing
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (v : Fin 4 → RatFunc K)
    (g : C →+* E) (b : Fin 4 → E)
    (hfirst : (∑ i, g (f (rationalParameterDerivative K (v i))) * b i) = 0) :
    (∑ i, g (D (D (f (v i)))) * b i) =
      g (D (f RatFunc.X)) ^ 2 *
        ∑ i, g (f (rationalParameterDerivative K (rationalParameterDerivative K (v i)))) * b i := by
  calc
    _ = ∑ i, (g (D (f RatFunc.X)) ^ 2 *
        (g (f (rationalParameterDerivative K (rationalParameterDerivative K (v i)))) * b i) +
      g (D (D (f RatFunc.X))) * (g (f (rationalParameterDerivative K (v i))) * b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rational_parameter_second_chain_rule, map_add, map_mul, map_pow, map_mul]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfirst, mul_zero, add_zero]

/-- A genuine nonzero parameter speed makes second-normal
vanishing invariant on the actual ruling direction. -/
theorem rational_normal_second_jet_zero_iff
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (v : Fin 4 → RatFunc K)
    (g : C →+* E) (b : Fin 4 → E) (hspeed : D (f RatFunc.X) ≠ 0)
    (hfirst : (∑ i, g (f (rationalParameterDerivative K (v i))) * b i) = 0) :
    (∑ i, g (D (D (f (v i)))) * b i) = 0 ↔
      (∑ i, g (f (rationalParameterDerivative K (rationalParameterDerivative K (v i)))) * b i) = 0 := by
  rw [rational_normal_second_jet_pairing f D v g b hfirst, mul_eq_zero,
    or_iff_right (pow_ne_zero 2 ((map_ne_zero g).mpr hspeed))]

/-- On the original ruling, annihilation of the full original
characteristic matrix is exactly second-normal vanishing in the cover. -/
theorem rational_cover_characteristic_matrix_zero_iff
    (f : RatFunc K →ₐ[K] C) (D : Derivation K C C) (v : Fin 4 → RatFunc K)
    (g : C →+* E) (b : Fin 4 → E) (hspeed : D (f RatFunc.X) ≠ 0)
    (hb : (normalRulingMatrix (rationalParameterDerivative K) v).map
      (g.comp f.toRingHom) *ᵥ b = 0) :
    (normalCharacteristicMatrix (rationalParameterDerivative K) v).map
      (g.comp f.toRingHom) *ᵥ b = 0 ↔ (∑ i, g (D (D (f (v i)))) * b i) = 0 := by
  have hfirst : (∑ i, g (f (rationalParameterDerivative K (v i))) * b i) = 0 := congrFun hb 1
  have hiff := rational_normal_second_jet_zero_iff f D v g b hspeed hfirst
  constructor
  · intro hchar
    exact hiff.mpr (congrFun hchar 2)
  · intro hsecond
    have hlast := hiff.mp hsecond
    funext i
    fin_cases i
    · exact congrFun hb 0
    · exact congrFun hb 1
    · exact hlast

end Jets

end DimensionFourDependence
