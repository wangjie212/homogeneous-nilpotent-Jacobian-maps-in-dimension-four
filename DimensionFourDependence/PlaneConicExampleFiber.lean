import DimensionFourDependence.PlaneConicExample
import DimensionFourDependence.HomogeneousGenericFiberAction
import DimensionFourDependence.FixedLastGeometricFiberValue
import DimensionFourDependence.ParabolaFromAffineSquare

/-! # Every geometric component of the example is the stated parabola -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 130000

variable {K : Type u} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The three normalized polynomial values on the chart where the
final source coordinate is nonzero. -/
theorem planeConicExample_dehomogenized {F : Type u} [Field F] (f : K →+* F)
    (z : Fin 4 → F) (hw : z 3 ≠ 0) {d : ℕ} (hd : 4 ≤ d) :
    let a := z 0 / z 3
    let U := z 1 / z 3 - a ^ 2
    let V := z 2 / z 3 + 2 * a * U
    (fun i => eval₂Hom f z (planeConicExample d i)) = fun i => (z 3) ^ d * (![U, V, -U ^ 2, 0] : Fin 4 → F) i := by
  dsimp only
  have hpow : z 3 ^ (d - 4) * z 3 ^ 4 = z 3 ^ d := by rw [← pow_add, Nat.sub_add_cancel hd]
  funext i
  fin_cases i <;> simp [planeConicExample, planeConicExampleQuadratic, ← hpow]
  all_goals field_simp [hw]

private theorem planeConicExample_third_ne_zero (d : ℕ) : planeConicExample (K := K) d 2 ≠ 0 := by
  intro h
  have he := congrArg (aeval (![0, 1, 0, 1] : Fin 4 → K)) h
  simp [planeConicExample, planeConicExampleQuadratic] at he

variable [CharZero K]

/-- Every geometric generic component of the displayed example has the
actual parametrization in the paper. The output values determine `w ^ d`,
then `U` and `V` for the chosen `w`. -/
theorem plane_conic_example_geometric_generic_parabola
    {d : ℕ} (hd : 4 ≤ d)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra K E]
    [Algebra (polynomialOutputField (planeConicExample (K := K) d)) E]
    [IsScalarTower K (polynomialOutputField (planeConicExample (K := K) d)) E]
    [Algebra.IsAlgebraic (polynomialOutputField (planeConicExample (K := K) d)) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField (planeConicExample (K := K) d)) x)).minimalPrimes) :
    let H := planeConicExample (K := K) d
    let v := fun i => algebraMap (polynomialOutputField H) E (genericFiberOutputScalar H i)
    let z := primeQuotientCoordinate P
    let F := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
    ∃ w U V : E, ∃ a : F, w ≠ 0 ∧ Transcendental E a ∧
      w ^ d = (v 0) ^ 2 / (-v 2) ∧ w ^ d * U = v 0 ∧ w ^ d * V = v 1 ∧
      z = ![algebraMap E F w * a,
        algebraMap E F w * (algebraMap E F U + a ^ 2),
        algebraMap E F w * (algebraMap E F V - 2 * a * algebraMap E F U), algebraMap E F w] := by
  let H := planeConicExample (K := K) d
  let M := polynomialOutputField H
  let S := FractionRing R₄
  let Y : Fin 4 → S := fun i => algebraMap R₄ S (H i)
  let F := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let z := primeQuotientCoordinate P
  let v := fun i => algebraMap M E (genericFiberOutputScalar H i)
  let g := algebraMap E F
  obtain ⟨_, hN, hr, hlast⟩ := plane_conic_example_homogeneous_nilpotent_rank_three (K := K) hd
  have hJ := rationalJacobian_polynomial H
  have hNY : IsNilpotent (rationalJacobian Y) := hJ.symm ▸ hN.map (algebraMap R₄ S).mapMatrix
  have hrY : (rationalJacobian Y).rank = 3 := hJ.symm ▸ hr
  have hzY : Y (Fin.last 3) = 0 := by
    change algebraMap R₄ S (H (Fin.last 3)) = 0
    rw [show H (Fin.last 3) = 0 from hlast, map_zero]
  obtain ⟨W⟩ := nilpotent_rank_three_zero_last_output_constructs_fiber_equations Y hNY hrY hzY
  obtain ⟨w, hw, hwP⟩ := fixed_last_geometric_component_has_nonzero_last_value Y W hrY E P hP
  have hwz : z 3 = g w := by
    rw [← primeQuotientCoordinate_relations P] at hwP
    change aeval z (X (3 : Fin 4) - C w) = 0 at hwP
    simpa only [map_sub, aeval_X, aeval_C, sub_eq_zero] using hwP
  have hw0 : z 3 ≠ 0 := by
    rw [hwz]
    exact fun h => hw (g.injective (h.trans (map_zero g).symm))
  have hOut (i : Fin 4) : aeval z (MvPolynomial.map (algebraMap K E) (H i)) = g (v i) := by
    have hmem : MvPolynomial.map (algebraMap K E) (H i) - C (v i) ∈ P := by
      apply hP.le
      rw [geometric_generic_fiber_ideal_eq_extended_output_equations (E := E) H]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [← primeQuotientCoordinate_relations P] at hmem
    change aeval z (MvPolynomial.map (algebraMap K E) (H i) - C (v i)) = 0 at hmem
    simpa only [map_sub, aeval_C, sub_eq_zero] using hmem
  let a := z 0 / z 3
  let U₀ := z 1 / z 3 - a ^ 2
  let V₀ := z 2 / z 3 + 2 * a * U₀
  let U := v 0 / w ^ d
  let V := v 1 / w ^ d
  have hform (i : Fin 4) : g (v i) = (z 3) ^ d * (![U₀, V₀, -U₀ ^ 2, 0] : Fin 4 → F) i := by
    have he := congrFun (planeConicExample_dehomogenized (g.comp (algebraMap K E)) z hw0 hd) i
    change eval₂ ((algebraMap E F).comp (algebraMap K E)) z (H i) = _ at he
    rw [← MvPolynomial.eval₂_map, ← MvPolynomial.aeval_def, hOut] at he
    exact he
  have hU : g U = U₀ := by
    change g (v 0 / w ^ d) = U₀
    rw [map_div₀, map_pow, ← hwz, show g (v 0) = z 3 ^ d * U₀ from hform 0]
    exact mul_div_cancel_left₀ U₀ (pow_ne_zero _ hw0)
  have hV : g V = V₀ := by
    change g (v 1 / w ^ d) = V₀
    rw [map_div₀, map_pow, ← hwz, show g (v 1) = z 3 ^ d * V₀ from hform 1]
    exact mul_div_cancel_left₀ V₀ (pow_ne_zero _ hw0)
  have hv₂ : v 2 ≠ 0 := by
    intro h
    have h' := (algebraMap M E).injective (h.trans (map_zero (algebraMap M E)).symm)
    have he := congrArg (fun r : M => (r : S)) h'
    exact planeConicExample_third_ne_zero d (IsFractionRing.injective R₄ S (he.trans (map_zero (algebraMap R₄ S)).symm))
  have hv₀ : v 0 = w ^ d * U := by
    apply g.injective
    rw [map_mul, map_pow, ← hwz, hU]
    exact hform 0
  have hv₁ : v 1 = w ^ d * V := by
    apply g.injective
    rw [map_mul, map_pow, ← hwz, hV]
    exact hform 1
  have hv₂' : v 2 = -(w ^ d * U ^ 2) := by
    apply g.injective
    rw [map_neg, map_mul, map_pow, map_pow, ← hwz, hU]
    exact (hform 2).trans (mul_neg _ _)
  have hratio : w ^ d = (v 0) ^ 2 / (-v 2) := by
    apply (eq_div_iff (neg_ne_zero.mpr hv₂)).mpr
    rw [hv₀, hv₂', neg_neg]
    ring
  have hcoord : z = ![g w * a, g w * (g U + a ^ 2), g w * (g V - 2 * a * g U), g w] := by
    funext i
    fin_cases i
    · change z 0 = g w * a
      rw [← hwz]
      dsimp only [a]
      field_simp [hw0]
    · change z 1 = g w * (g U + a ^ 2)
      rw [← hwz, hU]
      dsimp only [U₀]
      rw [sub_add_cancel]
      field_simp [hw0]
    · change z 2 = g w * (g V - 2 * a * g U)
      rw [← hwz, hV, hU]
      dsimp only [V₀]
      rw [add_sub_cancel_right]
      field_simp [hw0]
    · exact hwz
  have ha : Transcendental E a := by
    obtain ⟨u, hu, hker⟩ := matrix_nilpotent_exists_nonzero_kernel _ hNY (by omega)
    let Z := fun i : Fin 3 => Y (W.chart i.castSucc)
    let L := coefficientField (K := K) Z
    let : Algebra M L := fullOutputCoefficientAlgebra Y hrY W.chart W.independent
    let : IsScalarTower M L S := IsScalarTower.of_algebraMap_eq (R := M) (S := L) (A := S) (fun _ => rfl)
    let : IsScalarTower K L S := coefficientFieldScalarTower Z
    have hk : rationalJacobian Z *ᵥ u = 0 := funext (fun i => congrFun hker (W.chart i.castSucc))
    have htr := rational_coefficientField_trdeg_eq_one Z W.independent u hu hk
    obtain ⟨i, hi⟩ := exists_transcendental_coordinate x (rationalSource_adjoin_coordinates_eq_top L) (htr.trans_ne one_ne_zero)
    have hiM : Transcendental M (x i) := fun h => hi (h.tower_top L)
    have hiE : Transcendental E (z i) := componentGenericPoint_transcendental x P hP i hiM
    intro halg
    apply hiE
    rw [hcoord]
    fin_cases i
    · exact (isAlgebraic_algebraMap w).mul halg
    · have ha₂ : IsAlgebraic E (a ^ 2) := by simpa only [pow_two] using halg.mul halg
      exact (isAlgebraic_algebraMap w).mul ((isAlgebraic_algebraMap U).add ha₂)
    · have ht : IsAlgebraic E (2 : F) := by
        rw [← map_ofNat g]
        exact isAlgebraic_algebraMap (2 : E)
      exact (isAlgebraic_algebraMap w).mul ((isAlgebraic_algebraMap V).sub ((ht.mul halg).mul (isAlgebraic_algebraMap U)))
    · exact isAlgebraic_algebraMap w
  exact ⟨w, U, V, a, hw, ha, hratio, hv₀.symm, hv₁.symm, hcoord⟩

end DimensionFourDependence
