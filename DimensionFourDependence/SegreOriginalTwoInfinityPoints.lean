import DimensionFourDependence.SegreOriginalGeometricNormalForm
import DimensionFourDependence.SegreProjectiveRulingPoints
import DimensionFourDependence.GenericFiberSinglePoleBound
import DimensionFourDependence.GenericFiberHyperbolaCubicDirections
import DimensionFourDependence.StandardRulingQuadric

/-! # The original nonlinear Segre fiber has a nonradial infinity point on each ruling -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
  (E : Type*) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
  [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
  (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
  (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
    (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
  (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P))

local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "x₀" => primeQuotientCoordinate P
local notation "y₀" => genericOutputValue H E
local notation "s₀" => (y₀) 1 / (y₀) 0
local notation "t₀" => (y₀) 2 / (y₀) 0
local notation "Z₀" => segreFirstRulingDirection (t₀)
local notation "W₀" => segreSecondRulingDirection (s₀)

include hd hH hN hrank hind hP hline

/-- The exact Segre normal form and nonlinear actual component
construct both poles and their bounds, hence two distinct nonradial
points of the original projective closure on the two specified rulings. -/
theorem segre_original_normal_form_constructs_two_infinity_points
    (hy0 : (y₀) 0 ≠ 0) (hyquad : (y₀) 0 * (y₀) 3 - (y₀) 1 * (y₀) 2 = 0)
    (c q α β : E) (τ v w : G₀) (hn : c ≠ 0 ∨ q ≠ 0)
    (hzero : c = 0 → α = 0 ∧ β = 0)
    (hx : ∀ i, (x₀) i = τ * algebraMap E G₀ ((y₀) i) +
      v * algebraMap E G₀ ((Z₀) i) + w * algebraMap E G₀ ((W₀) i) +
      algebraMap E G₀ ((Pi.single 3 c : Fin 4 → E) i))
    (heq : algebraMap E G₀ q = algebraMap E G₀ (algebraMap K E ((d : K)⁻¹) * c) * τ +
      algebraMap E G₀ α * v + algebraMap E G₀ β * w + algebraMap E G₀ (1 / (y₀) 0) * v * w) :
    ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
      p ∈ projectiveClosureSet (L := E) (x₀) ∧ r ∈ projectiveClosureSet (L := E) (x₀) ∧
      SegreFirstRulingBoundaryPoint (s₀) (t₀) p ∧ SegreSecondRulingBoundaryPoint (s₀) (t₀) r ∧ p ≠ r := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let a : E := algebraMap K E ((d : K)⁻¹) * c
  let κ : E := 1 / (y₀) 0
  have hκ : κ ≠ 0 := by dsimp only [κ]; exact one_div_ne_zero hy0
  have ha : a ≠ 0 ∨ (a = 0 ∧ α = 0 ∧ β = 0 ∧ q ≠ 0) := by
    by_cases hc : c = 0
    · obtain ⟨hα, hβ⟩ := hzero hc
      exact Or.inr ⟨by simp [a, hc], hα, hβ, hn.resolve_left (fun h => h hc)⟩
    · left
      exact mul_ne_zero ((map_ne_zero (algebraMap K E)).mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)))) hc
  have hns : (¬∃ e : E, algebraMap E G₀ e = v) ∧ (¬∃ e : E, algebraMap E G₀ e = w) := by
    rcases ha with ha | ⟨ha, hα, hβ, hq⟩
    · exact nonlinear_quadratic_normal_form_parameters_nonscalar (x₀) (y₀) (Z₀) (W₀) (Pi.single 3 c)
        τ v w a α β κ q ha hx heq hline 0
    · have he : algebraMap E G₀ q = algebraMap E G₀ κ * v * w := by
        change algebraMap E G₀ q = algebraMap E G₀ a * τ +
          algebraMap E G₀ α * v + algebraMap E G₀ β * w + algebraMap E G₀ κ * v * w at heq
        simpa only [ha, hα, hβ, map_zero, zero_mul, zero_add] using heq
      exact nonlinear_hyperbola_parameters_nonscalar (x₀) (y₀) (Z₀) (W₀) (Pi.single 3 c)
        τ v w κ q hκ hq hx he hline 0
  let U : Fin 3 → E := fun i => (y₀) i.castSucc
  have htarget : segreGraphTarget U = (y₀) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact (segre_last_coordinate_eq_graph (y₀) hy0 hyquad).symm
  have hpos (i : Fin 4) : (x₀) i = τ * algebraMap E G₀ (segreGraphTarget U i) +
      v * algebraMap E G₀ (segreFirstRulingDirection (U 2 / U 0) i) +
      w * algebraMap E G₀ (segreSecondRulingDirection (U 1 / U 0) i) +
      algebraMap E G₀ ((Pi.single 3 c : Fin 4 → E) i) := by
    simpa only [htarget, show U 0 = (y₀) 0 from rfl, show U 1 = (y₀) 1 from rfl,
      show U 2 = (y₀) 2 from rfl] using hx i
  have hfirst : ∃ p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
      p ∈ projectiveClosureSet (L := E) (x₀) ∧ SegreFirstRulingBoundaryPoint (s₀) (t₀) p := by
    obtain ⟨V, hV, hv⟩ := nonscalar_has_valuation_pole v hns.1
    letI : Algebra E V := valuationConstantAlgebra V hV
    let vGAlgebra : Algebra V G₀ := inferInstance
    letI : SMul V G₀ := vGAlgebra.toSMul
    letI : IsScalarTower E V G₀ := valuationConstantScalarTower V hV
    have hb : V.valuation w ≤ 1 ∧ V.valuation τ ≤ V.valuation v := by
      rcases ha with ha | ⟨ha, hα, hβ, hq⟩
      · exact generic_fiber_single_pole_bounds H hd hH hN hrank hind E P hP V
          τ v w (Z₀) (W₀) (Pi.single 3 c) a α β κ q ha hκ hx heq hv
      · have he : algebraMap E G₀ q = algebraMap E G₀ κ * v * w := by
          change algebraMap E G₀ q = algebraMap E G₀ a * τ +
            algebraMap E G₀ α * v + algebraMap E G₀ β * w + algebraMap E G₀ κ * v * w at heq
          simpa only [ha, hα, hβ, map_zero, zero_mul, zero_add] using heq
        obtain ⟨hw, hτ⟩ := generic_fiber_hyperbola_single_pole_bounds H hd hH hN hrank hind E P hP V
          τ v w (Z₀) (W₀) (Pi.single 3 c) κ q hκ hq hx he hv
        exact ⟨hw.le, hτ⟩
    obtain ⟨_ρ, b, hb0, _hshift, hp, h2, h3, hkey⟩ :=
      segre_first_transverse_pole_constructs_boundary_point V U hy0 (x₀) c τ v w hpos hv hb.2 hb.1
    exact ⟨projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb0,
      hp, segre_field_point_first_ruling_boundary (s₀) (t₀) b hb0 h2 h3 hkey⟩
  have hsecond : ∃ r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
      r ∈ projectiveClosureSet (L := E) (x₀) ∧ SegreSecondRulingBoundaryPoint (s₀) (t₀) r := by
    obtain ⟨V, hV, hw⟩ := nonscalar_has_valuation_pole w hns.2
    letI : Algebra E V := valuationConstantAlgebra V hV
    let vGAlgebra : Algebra V G₀ := inferInstance
    letI : SMul V G₀ := vGAlgebra.toSMul
    letI : IsScalarTower E V G₀ := valuationConstantScalarTower V hV
    have hx' (i : Fin 4) : (x₀) i = τ * algebraMap E G₀ ((y₀) i) +
        w * algebraMap E G₀ ((W₀) i) + v * algebraMap E G₀ ((Z₀) i) +
        algebraMap E G₀ ((Pi.single 3 c : Fin 4 → E) i) := by rw [hx i]; ring
    have heq' : algebraMap E G₀ q = algebraMap E G₀ a * τ +
        algebraMap E G₀ β * w + algebraMap E G₀ α * v + algebraMap E G₀ κ * w * v := by
      linear_combination heq
    have hb : V.valuation v ≤ 1 ∧ V.valuation τ ≤ V.valuation w := by
      rcases ha with ha | ⟨ha, hα, hβ, hq⟩
      · exact generic_fiber_single_pole_bounds H hd hH hN hrank hind E P hP V
          τ w v (W₀) (Z₀) (Pi.single 3 c) a β α κ q ha hκ hx' heq' hw
      · have he : algebraMap E G₀ q = algebraMap E G₀ κ * w * v := by
          simpa only [ha, hα, hβ, map_zero, zero_mul, zero_add] using heq'
        obtain ⟨hv, hτ⟩ := generic_fiber_hyperbola_single_pole_bounds H hd hH hN hrank hind E P hP V
          τ w v (W₀) (Z₀) (Pi.single 3 c) κ q hκ hq hx' he hw
        exact ⟨hv.le, hτ⟩
    obtain ⟨_ρ, b, hb0, _hshift, hp, h1, h3, hkey⟩ :=
      segre_second_transverse_pole_constructs_boundary_point V U hy0 (x₀) c τ v w hpos hw hb.2 hb.1
    exact ⟨projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb0,
      hp, segre_field_point_second_ruling_boundary (s₀) (t₀) b hb0 h1 h3 hkey⟩
  obtain ⟨p, hp, hpR⟩ := hfirst
  obtain ⟨r, hr, hrR⟩ := hsecond
  exact ⟨p, r, hp, hr, hpR, hrR, segre_first_and_second_ruling_boundary_points_distinct (s₀) (t₀) p r hpR hrR⟩

/-- Section 5.2: every original nonlinear geometric Segre fiber has
two distinct actual points at infinity, one on each ruling through its
generic output. Neither is the radial intersection of the two rulings.
All coordinate functions, constants, nonscalar parameters, poles and
valuation normalizations are constructed from the original hypotheses. -/
theorem original_segre_nonlinear_geometric_fiber_has_two_infinity_points
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0) :
    ∃ p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E),
      p ∈ projectiveClosureSet (L := E) (x₀) ∧ r ∈ projectiveClosureSet (L := E) (x₀) ∧
      SegreFirstRulingBoundaryPoint (s₀) (t₀) p ∧ SegreSecondRulingBoundaryPoint (s₀) (t₀) r ∧ p ≠ r := by
  obtain ⟨hy0, c, q, α, β, τ, v, w, hn, hzero, hx, heq⟩ :=
    original_segre_geometric_fiber_constructs_radial_transverse_normal_form H hd hH hN hrank hind hSegre E P hP hline
  have hyquad : (y₀) 0 * (y₀) 3 - (y₀) 1 * (y₀) 2 = 0 := by
    have he := (genericOutputValue_relations H E (standardRulingPolynomial (F := K))).mpr
      (by simpa [standardRulingPolynomial] using hSegre)
    simpa [standardRulingPolynomial] using he
  exact segre_original_normal_form_constructs_two_infinity_points H hd hH hN hrank hind E P hP hline
    hy0 hyquad c q α β τ v w hn hzero hx heq

end DimensionFourDependence
