import DimensionFourDependence.PlanarActiveNormalization
import DimensionFourDependence.PlanarNilpotentDependence

/-! # Proposition 6.3: the actual normalized active outputs are proportional over `K(z,t)` -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 2400000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "A₂" => MvPolynomial (Fin 2) R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L

/-- The two active polynomial coordinates with their original
coefficient ring embedded in its fraction field. -/
noncomputable def activeFractionPolynomial (p : R₄) : Aₗ :=
  MvPolynomial.map (algebraMap R₂ L) (planarCoefficientEquiv p)

theorem activeFractionPolynomial_injective : Function.Injective (activeFractionPolynomial (K := K)) :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective R₂ L)).comp planarCoefficientEquiv.injective

theorem activeFractionPolynomial_normalized_origin (p : R₄) :
    aeval (fun _ : Fin 2 => (0 : L)) (activeFractionPolynomial (planarActiveNormalized p)) = 0 := by
  have hp : constantCoeff (planarCoefficientEquiv (planarActiveNormalized p) : A₂) = 0 := by
    simpa using planarCoefficientEquiv_normalized_at_origin p
  simpa [activeFractionPolynomial, constantCoeff_map, hp]

/-- The active fraction-field Jacobian has the same entries as the
original active block, mapped through the actual coefficient regrouping. -/
theorem jac_activeFractionPolynomial (A : Fin 2 → R₄) :
    jac (fun i => activeFractionPolynomial (A i)) = (planarActiveJacobian A).map activeFractionPolynomial := by
  funext i j
  change pderiv j (MvPolynomial.map (algebraMap R₂ L) (planarCoefficientEquiv (A i))) =
    MvPolynomial.map (algebraMap R₂ L) (planarCoefficientEquiv (pderiv (j.castAdd 2) (A i)))
  rw [planarCoefficientEquiv_pderiv_active, pderiv_map]

/-- The original active block constructs a constant component relation
over the actual field `K(z,t)` after removing both active-origin values. -/
theorem planar_normalized_active_block_componentsDependent_over_fraction_field
    (A : Fin 2 → R₄) (hN : IsNilpotent (planarActiveJacobian A)) :
    ComponentsDependent (fun i => activeFractionPolynomial (planarActiveNormalized (A i))) := by
  let ψ : R₄ →+* Aₗ := (MvPolynomial.map (algebraMap R₂ L)).comp planarCoefficientEquiv.toRingHom
  have hnorm : IsNilpotent (jac (fun i => activeFractionPolynomial (planarActiveNormalized (A i)))) := by
    rw [jac_activeFractionPolynomial, planarActiveJacobian_normalized]
    exact hN.map ψ.mapMatrix
  exact normalized_planar_nilpotent_componentsDependent _
    (fun i => activeFractionPolynomial_normalized_origin (A i)) hnorm

end DimensionFourDependence.Shear
