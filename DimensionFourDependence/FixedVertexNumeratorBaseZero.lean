import DimensionFourDependence.FixedVertexPencilBase
import DimensionFourDependence.FixedVertexRootNumerator
import DimensionFourDependence.ExtendedHomogeneousPowerSections

/-! # The actual root numerator vanishes on the original pencil base

The original pencil base maps to the vertex axis. Extending the
coefficient ring preserves its radical equations. Consequently every
output covector annihilating the vertex vanishes on the extended base;
the actual second-normal numerator has this property by construction.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)

local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "B₀" => Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
  Set (MvPolynomial (Fin 4) E))

include hd hH hind hGauss hvertex hq hrel hparameter

/-- A vertex-annihilating output covector belongs to the radical of
the original coefficient-extended pencil base ideal. -/
theorem vertex_output_covector_mem_extended_pencil_base_radical
    (n : Fin 4 → E) (hn : n (Fin.last 3) = 0) :
    extendedClosedGaussOutputLinearPolynomial H I E n ∈ (B₀).radical := by
  have hfirst := original_fixed_vertex_pencil_base_extended_radical_contains_outputs
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter (ι)
  change (∑ i : Fin 4, n i • MvPolynomial.map (ι) (H i)) ∈ (B₀).radical
  rw [Fin.sum_univ_castSucc, hn, zero_smul, add_zero]
  apply (B₀).radical.sum_mem
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul]
  exact (B₀).radical.mul_mem_left _ (hfirst i)

/-- The actual root numerator, with its exact original second-normal
provenance, vanishes on the whole coefficient-extended base V(p,q).
Neither this base incidence nor its vertex coefficient is assumed. -/
theorem actual_gauss_root_numerator_mem_extended_pencil_base_radical
    (n : Fin 4 → E) (hn : HasActualGaussRootNumerator H I E e n) :
    extendedClosedGaussOutputLinearPolynomial H I E n ∈ (B₀).radical :=
  vertex_output_covector_mem_extended_pencil_base_radical H I E hd hH hind hGauss
    hvertex e p q hq hrel hparameter n
    (actual_gauss_root_numerator_fixed_vertex_coordinate_zero H I E e hH hd hind hGauss hvertex n hn)

end DimensionFourDependence
