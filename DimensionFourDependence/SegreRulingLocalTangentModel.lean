import DimensionFourDependence.SegreRulingHomogeneousProfiles

/-! # A regular local tangent action along the Segre uniformizer -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The source tangent lattice `(v,t*v+pi*b)` in all four original
coordinates. It is faithful over the generic field when `pi` is nonzero. -/
def segreRulingSourceTangentFrame (t π : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, 0, 0; t, 0, π, 0; 0, t, 0, π]

/-- Coordinate variations in the source chart `(x,y,t,pi)`:
`delta t = pi*z*b1`, `delta pi = pi*(b2-s*b1)`. -/
def segreRulingChartVariationMatrix (π z s : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, π * z, 0; 0, 0, -π * s, π]

/-- All entries of the normalized tangent action are regular. The
profiles `df,dg,da` are ordered by `(x,y,t,pi)`; every transverse
derivative term is explicitly multiplied by the uniformizer. -/
def segreRulingLocalTangentMatrix (j π z s a f g : R) (df dg da : Fin 4 → R) :
    Matrix (Fin 4) (Fin 4) R :=
  let U : Matrix (Fin 2) (Fin 4) R :=
    !![df 0, df 1, π * z * df 2 - π * s * df 3 - j * s * f, π * df 3 + j * f;
       dg 0, dg 1, π * z * dg 2 - π * s * dg 3 - j * s * g, π * dg 3 + j * g]
  let L : Fin 4 → R := ![da 0, da 1, z - a * s + π * z * da 2 - π * s * da 3, a + π * da 3]
  Matrix.of ![U 0, U 1, (fun i => a * U 0 i + f * L i), (fun i => a * U 1 i + g * L i)]

/-- The chart Jacobian obtained by differentiating the exact output
rows `pi^j*(f,g)` and `(t+pi*a)*pi^j*(f,g)`. -/
def segreRulingLocalOutputJacobian (j : ℕ) (π t a f g : R) (df dg da : Fin 4 → R) :
    Matrix (Fin 4) (Fin 4) R :=
  let U : Matrix (Fin 2) (Fin 4) R :=
    !![π ^ j * df 0, π ^ j * df 1, π ^ j * df 2, π ^ j * df 3 + (j : R) * π ^ (j - 1) * f;
       π ^ j * dg 0, π ^ j * dg 1, π ^ j * dg 2, π ^ j * dg 3 + (j : R) * π ^ (j - 1) * g]
  let L : Fin 4 → R := ![π * da 0, π * da 1, 1 + π * da 2, a + π * da 3]
  Matrix.of ![U 0, U 1, (fun i => (t + π * a) * U 0 i + π ^ j * f * L i),
    (fun i => (t + π * a) * U 1 i + π ^ j * g * L i)]

/-- The full normalized action preserves the actual tangent lattice.
This polynomial identity includes the zero-common-factor-order case. -/
theorem segre_ruling_local_jacobian_tangent_identity
    (j : ℕ) (π t z s a f g : R) (df dg da : Fin 4 → R) :
    segreRulingLocalOutputJacobian j π t a f g df dg da * segreRulingChartVariationMatrix π z s =
      π ^ j • (segreRulingSourceTangentFrame t π * segreRulingLocalTangentMatrix (j : R) π z s a f g df dg da) := by
  cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    simp [segreRulingLocalOutputJacobian, segreRulingChartVariationMatrix,
      segreRulingSourceTangentFrame, segreRulingLocalTangentMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, pow_succ] <;> ring

/-- The regular tangent action retains its specified coefficient
realization under arbitrary ring maps. -/
theorem segreRulingLocalTangentMatrix_map (σ : R →+* S)
    (j π z s a f g : R) (df dg da : Fin 4 → R) :
    (segreRulingLocalTangentMatrix j π z s a f g df dg da).map σ =
      segreRulingLocalTangentMatrix (σ j) (σ π) (σ z) (σ s) (σ a) (σ f) (σ g)
        (fun i => σ (df i)) (fun i => σ (dg i)) (fun i => σ (da i)) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [segreRulingLocalTangentMatrix, Matrix.map_apply, map_add, map_sub, map_mul]

/-- Specialization at the given uniformizer removes exactly the
transverse derivative terms and constructs the full four-dimensional
ruling-chart matrix used in the reduced nilpotence contradiction. -/
theorem segre_ruling_local_tangent_specialization (σ : R →+* S)
    (j π z s a f g : R) (df dg da : Fin 4 → R) (hπ : σ π = 0) :
    (segreRulingLocalTangentMatrix j π z s a f g df dg da).map σ =
      segreRulingChartTangentMatrix (σ j) (σ f) (σ g) (σ (df 0)) (σ (df 1))
        (σ (dg 0)) (σ (dg 1)) (σ a) (σ (da 0)) (σ (da 1)) (σ z) (σ s) := by
  rw [segreRulingLocalTangentMatrix_map]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [segreRulingLocalTangentMatrix, segreRulingChartTangentMatrix, hπ] <;> ring

end DimensionFourDependence
