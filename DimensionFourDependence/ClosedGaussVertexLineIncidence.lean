import DimensionFourDependence.VertexLineIncidence
import DimensionFourDependence.ClosedGaussNormalJetRealization
import DimensionFourDependence.NativeGraphNormalComparison
import DimensionFourDependence.FixedVertexCharacteristicAxis

/-! # The actual generic normal plane meets original vertex lines properly

The original map constructs the independent jets. Its chosen normal row
is the image of the same closed Gauss normal, so no independent moving
plane or nonvanishing direction-pairing hypothesis is introduced.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "ν" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0

include hvertex e

/-- Every nonzero original transverse direction pairs nontrivially
with the actual chosen generic normal, after the actual coefficient cover. -/
theorem actual_closed_gauss_normal_transverse_direction_pairing_ne_zero
    (b : Fin 3 → K) (hb : b ≠ 0) :
    (∑ i : Fin 3, (ν) i.castSucc * (ι) (b i)) ≠ 0 := by
  let w := closedGaussParameterNormal H I e
  let ρ : RatFunc K →+* E := (algebraMap (closedGaussParameterField H I) E).comp e.toRingHom
  have hwlast : w (Fin.last 3) = 0 := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (w (Fin.last 3)) =
      closedGaussParameterSourceHom H I e 0
    rw [closedGaussParameterSourceHom_normal, hvertex, zero_div, map_zero]
  obtain ⟨i, j, hminor, hLI⟩ :=
    closed_gauss_parameter_constructs_independent_normal_jet_minor H hd hH hind I hGauss e
  have hpair := independent_normal_jets_transverse_constant_pairing_ne_zero
    (rationalParameterDerivative K) w hLI hwlast b hb
  have hrow (i : Fin 4) : (ν) i = ρ (w i) := by
    change extendedClosedGaussRulingMatrix H I E
      (actualGaussRulingParameterChoice H I hH hd hind hGauss) 0 i = _
    rw [extendedClosedGaussRulingMatrix_first_row_closed_normal H I E e]
    rfl
  have hc (c : K) : ρ (algebraMap K (RatFunc K) c) = (ι) c := by
    change algebraMap (closedGaussParameterField H I) E
      (e (algebraMap K (RatFunc K) c)) = _
    rw [e.commutes]
    rfl
  have hmap : ρ (∑ i : Fin 3, w i.castSucc * algebraMap K (RatFunc K) (b i)) =
      ∑ i : Fin 3, (ν) i.castSucc * (ι) (b i) := by
    simp only [map_sum, map_mul, hc, hrow]
  rw [← hmap]
  exact (_root_.map_ne_zero ρ).mpr hpair

/-- The actual generic normal plane contains the source vertex
and excludes the whole scalar-extended line of every original direction. -/
theorem actual_closed_gauss_normal_vertex_line_plane_incidence
    (b : Fin 3 → K) (hb : b ≠ 0) (j : Fin 3) (hj : b j ≠ 0) :
    aeval (Fin.snoc (0 : Fin 3 → E) 1) (linearFormPolynomial (ν)) = 0 ∧
      linearFormPolynomial (ν) ∉ vertexLinePrime (fun i => (ι) (b i)) j := by
  constructor
  · simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
    exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex 0
  · exact vertexLinePrime_linearForm_not_mem _ j
      ((_root_.map_ne_zero (ι)).mpr hj) (ν)
      (actual_closed_gauss_normal_transverse_direction_pairing_ne_zero
        H I E hd hH hind hGauss hvertex e b hb)

end DimensionFourDependence
