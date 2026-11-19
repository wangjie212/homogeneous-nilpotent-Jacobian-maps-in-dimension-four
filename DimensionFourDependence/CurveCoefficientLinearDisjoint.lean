import DimensionFourDependence.DifferentialConstantLinearIndependence
import DimensionFourDependence.CurveDerivationCompatibility
import DimensionFourDependence.TranscendentalSeparatingDerivation

/-! # A curve and independent coefficient field are linearly disjoint over algebraically closed constants -/

namespace DimensionFourDependence

open Module

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F C : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F] [Field C] [Algebra K C] [Algebra C F] [IsScalarTower K C F]

/-- An original curve field and a coefficient field admitting a
transcendental original curve parameter are linearly disjoint. Both
compatible derivations and the original constant-field assertion are
constructed, rather than assumed. -/
theorem curve_coefficient_linearDisjoint_of_transcendental_parameter
    (J : IntermediateField K F) (hJ : Algebra.trdeg K J ≤ 1)
    (t : J) (ht : Transcendental C (algebraMap J F t)) : J.LinearDisjoint C := by
  classical
  letI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have htK : Transcendental K t := by
    intro ha
    exact ht ((ha.algHom (IsScalarTower.toAlgHom K J F)).tower_top C)
  obtain ⟨D, hDt⟩ := exists_derivation_apply_eq_one_of_transcendental t htK
  obtain ⟨ΔC, hΔt⟩ := exists_derivation_apply_eq_one_of_transcendental
    (algebraMap J F t) ht
  let Δ := ΔC.restrictScalars K
  have hparam : Δ (algebraMap J F t) = algebraMap J F (D t) := by
    change ΔC (algebraMap J F t) = algebraMap J F (D t)
    rw [hDt, map_one]
    exact hΔt
  have hcompat := curve_derivation_compatible_of_parameter D Δ t htK hJ hparam
  have hD : D ≠ 0 := by
    intro hz
    have he := hDt
    rw [hz, Derivation.zero_apply] at he
    exact zero_ne_one he
  have hconstants := curve_derivation_constants_are_original D hD hJ
  let b := Basis.ofVectorSpace K C
  have hbind : LinearIndependent K (algebraMap C F ∘ b) := by
    exact b.linearIndependent.map' (IsScalarTower.toAlgHom K C F).toLinearMap
      (LinearMap.ker_eq_bot.mpr (algebraMap C F).injective)
  have hblift : LinearIndependent J (algebraMap C F ∘ b) :=
    differential_constants_linearIndependent D Δ hcompat hconstants _ hbind
      (fun i => ΔC.map_algebraMap (b i))
  exact IntermediateField.LinearDisjoint.of_basis_right' b hblift

/-- Any finite or infinite original-constant-independent source
coordinate family on the actual curve remains independent over the
independent coefficient field. -/
theorem curve_coordinate_linearIndependent_over_independent_coefficients
    (J : IntermediateField K F) (hJ : Algebra.trdeg K J ≤ 1)
    (t : J) (ht : Transcendental C (algebraMap J F t))
    {ι : Type*} (v : ι → J) (hv : LinearIndependent K v) :
    LinearIndependent C (fun i => algebraMap J F (v i)) :=
  (curve_coefficient_linearDisjoint_of_transcendental_parameter J hJ t ht).linearIndependent_left hv

end DimensionFourDependence
