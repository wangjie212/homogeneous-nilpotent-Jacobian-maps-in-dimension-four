import DimensionFourDependence.HyperbolaParameterNonconstancy

/-! # Both cubic directions in the zero-c, nonzero-q normal form

For an actual nonlinear geometric generic component satisfying
`q=kappa*s*t`, both isotropic parameters supply poles. The hyperbola
separates those poles, the actual radial exclusion bounds the radial
parameter, and the cubic residue equation gives both constant directions.
The coordinate and Euler coefficient data remain explicit.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

section

variable (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [CharZero E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "G" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)

include hd hH hN hrank hind hP

omit [CharZero E] in
/-- At a pole of `s` on the nondegenerate hyperbola, `t` has value
strictly below one and the actual radial parameter has value at most `s`. -/
theorem generic_fiber_hyperbola_single_pole_bounds (V : ValuationSubring G) [Algebra E V] :
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E) (κ q : E),
      κ ≠ 0 → q ≠ 0 →
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      (algebraMap E G q = algebraMap E G κ * s * t) →
      1 < V.valuation s → V.valuation t < 1 ∧ V.valuation τ ≤ V.valuation s := by
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c κ q hκ hq hx heq hs
  have hconstants (b : E) : V.valuation (algebraMap E G b) ≤ 1 := by
    apply (V.valuation_le_one_iff _).mpr
    rw [IsScalarTower.algebraMap_apply E V G b]
    exact (algebraMap E V b).property
  let : V.valuation.IsTrivialOn E := Valuation.IsTrivialOn.of_le_one V.valuation hconstants
  have ht := hyperbola_poles_separated V.valuation κ q hκ hq s t heq hs
  have he := generic_fiber_radial_value_bound H hd hH hN hrank hind E P hP V τ s t Z W c hx
  rw [max_eq_right hs.le, max_eq_left (ht.le.trans hs.le)] at he
  exact ⟨ht, he⟩

/-- A pole in the hyperbola normal form gives one constant cubic
direction, with both required pole bounds derived for the actual component. -/
theorem generic_fiber_hyperbola_single_pole_cubic_isotropy (V : ValuationSubring G) [Algebra E V] :
    let vGAlgebra : Algebra V G := inferInstance
    letI : SMul V G := vGAlgebra.toSMul
    ∀ [IsScalarTower E V G] (τ s t : G) (Z W c : Fin 4 → E) (κ q : E),
      κ ≠ 0 → q ≠ 0 →
      (∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
        s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i)) →
      (algebraMap E G q = algebraMap E G κ * s * t) → 1 < V.valuation s →
      ∀ (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E),
        (∀ i j k, C i j k = C j i k) → (∀ i j k, C i j k = C i k j) →
        (∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0) →
        (∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k) →
        matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 →
        ∀ (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E),
          aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0 →
          tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 := by
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  dsimp only
  intro hTower τ s t Z W c κ q hκ hq hx heq hs ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic
  obtain ⟨ht, hτ⟩ := generic_fiber_hyperbola_single_pole_bounds H hd hH hN hrank hind E P hP V
    τ s t Z W c κ q hκ hq hx heq hs
  exact single_pole_forces_constant_cubic_isotropy V (fun i => primeQuotientCoordinate P (ι i))
    (fun i => genericOutputValue H E (ι i)) (fun i => Z (ι i)) (fun i => W (ι i)) (fun i => c (ι i))
    τ s t (fun i => hx (ι i)) hs hτ ht.le T C h12 h23 hY hCY hZ a₃ S k₃ hCubic

/-- Over algebraically closed constants, a nonscalar hyperbola
parameter supplies the valuation pole and hence its cubic direction. -/
theorem generic_fiber_hyperbola_nonscalar_cubic_isotropy [IsAlgClosed E]
    (τ s t : G) (Z W c : Fin 4 → E) (κ q : E) (hκ : κ ≠ 0) (hq : q ≠ 0)
    (hx : ∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
      s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i))
    (heq : algebraMap E G q = algebraMap E G κ * s * t)
    (hs : ¬ ∃ e : E, algebraMap E G e = s)
    (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (hY : ∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0)
    (hCY : ∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0)
    (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E)
    (hCubic : aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0) :
    tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 := by
  obtain ⟨V, hV, hpole⟩ := nonscalar_has_valuation_pole s hs
  let : Algebra E V := valuationConstantAlgebra V hV
  let vGAlgebra : Algebra V G := inferInstance
  let : SMul V G := vGAlgebra.toSMul
  let : IsScalarTower E V G := valuationConstantScalarTower V hV
  exact generic_fiber_hyperbola_single_pole_cubic_isotropy H hd hH hN hrank hind E P hP V
    τ s t Z W c κ q hκ hq hx heq hpole ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic

/-- In the `c=0,q≠0` quadratic normal form, actual component
nonlinearity supplies both nonscalar parameters and both cubic directions.
No pole, valuation, cubic graph or nonscalarity assumption remains. -/
theorem generic_fiber_nonlinear_hyperbola_cubic_directions [IsAlgClosed E]
    (τ s t : G) (Z W c : Fin 4 → E) (κ q : E) (hκ : κ ≠ 0) (hq : q ≠ 0)
    (hx : ∀ i, primeQuotientCoordinate P i = τ * algebraMap E G (genericOutputValue H E i) +
      s * algebraMap E G (Z i) + t * algebraMap E G (W i) + algebraMap E G (c i))
    (heq : algebraMap E G q = algebraMap E G κ * s * t)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (ι : Fin 3 → Fin 4) (T : Matrix (Fin 3) (Fin 3) E) (C : Fin 3 → Fin 3 → Fin 3 → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (hY : ∀ j, (∑ i, genericOutputValue H E (ι i) * T i j) = 0)
    (hCY : ∀ j k, (∑ i, genericOutputValue H E (ι i) * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T (fun i => Z (ι i)) (fun i => Z (ι i)) = 0)
    (hW : matrixBilinearPairing T (fun i => W (ι i)) (fun i => W (ι i)) = 0)
    (a₃ : Fin 3 → E) (S : Matrix (Fin 3) (Fin 3) E) (k₃ : E)
    (hCubic : aeval (fun i => primeQuotientCoordinate P (ι i)) (cubicFiberPolynomial a₃ S C k₃) = 0) :
    tensorTrilinearPairing C (fun i => Z (ι i)) (fun i => Z (ι i)) (fun i => Z (ι i)) = 0 ∧
      tensorTrilinearPairing C (fun i => W (ι i)) (fun i => W (ι i)) (fun i => W (ι i)) = 0 := by
  obtain ⟨hs, ht⟩ := nonlinear_hyperbola_parameters_nonscalar
    (primeQuotientCoordinate P) (genericOutputValue H E) Z W c τ s t κ q hκ hq hx heq hline 0
  have hZc := generic_fiber_hyperbola_nonscalar_cubic_isotropy H hd hH hN hrank hind E P hP
    τ s t Z W c κ q hκ hq hx heq hs ι T C h12 h23 hY hCY hZ a₃ S k₃ hCubic
  have hx' (i : Fin 4) : primeQuotientCoordinate P i =
      τ * algebraMap E G (genericOutputValue H E i) + t * algebraMap E G (W i) +
        s * algebraMap E G (Z i) + algebraMap E G (c i) := by rw [hx i]; ring
  have heq' : algebraMap E G q = algebraMap E G κ * t * s := by linear_combination heq
  have hWc := generic_fiber_hyperbola_nonscalar_cubic_isotropy H hd hH hN hrank hind E P hP
    τ t s W Z c κ q hκ hq hx' heq' ht ι T C h12 h23 hY hCY hW a₃ S k₃ hCubic
  exact ⟨hZc, hWc⟩

end

end DimensionFourDependence
