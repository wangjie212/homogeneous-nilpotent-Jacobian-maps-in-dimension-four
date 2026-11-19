import DimensionFourDependence.Corollary53
import DimensionFourDependence.AffinePlaneConicCoordinates
import DimensionFourDependence.ConjugateGeometricFiberPoint

/-! # Corollary 5.3 on the components of the untransformed map -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 135000

private theorem scalar_stabilizer_trivial_of_linear_value
    {E : Type u} [Field E] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (L : MvPolynomial (Fin n) E) (hL : L.IsHomogeneous 1) (a : E) (ha : a ≠ 0)
    (hval : aeval (primeQuotientCoordinate P) L = algebraMap E _ a) (v : Eˣ)
    (hfix : P.comap (polynomialScalarEquiv v).toRingHom = P) : v = 1 := by
  let z := primeQuotientCoordinate P
  have hz : L - C a ∈ P := by
    rw [← primeQuotientCoordinate_relations P]
    change aeval z (L - C a) = 0
    rw [map_sub, aeval_C, hval, sub_self]
  have hmem : polynomialScalarEquiv v (L - C a) ∈ P := by
    change L - C a ∈ P.comap (polynomialScalarEquiv v).toRingHom
    rwa [hfix]
  rw [← primeQuotientCoordinate_relations P] at hmem
  change aeval z (polynomialScalarEquiv v (L - C a)) = 0 at hmem
  rw [map_sub, (show polynomialScalarEquiv v (C a) = C a from (polynomialScalarEquiv v).commutes a),
    polynomialScalarEquiv_apply, homogeneous_aeval_scaled_coordinates L hL, pow_one,
    map_sub, map_mul, aeval_C, aeval_C, hval] at hmem
  have hscalar : ((v : E) - 1) * a = 0 := by
    apply (algebraMap E (FractionRing (MvPolynomial (Fin n) E ⧸ P))).injective
    rw [map_mul, map_sub, map_one, map_zero]
    rw [sub_mul, one_mul]
    exact hmem
  apply Units.ext
  exact sub_eq_zero.mp ((mul_eq_zero.mp hscalar).resolve_right ha)

variable {K : Type u} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The line or plane-conic classification and free scalar action on
the actual geometric generic components in the original coordinates. -/
theorem corollary_5_3_original_coordinates
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hr : polyRank (jac H) = 3)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] :
    let I := extendCoefficientIdeal E (fiberVanishingIdeal (L := polynomialOutputField H) x)
    (∀ (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime], P ∈ I.minimalPrimes →
      LiesInAffineLine (E := E) (primeQuotientCoordinate P) ∨
        Nonempty (AffinePlaneConic (E := E) (primeQuotientCoordinate P))) ∧
    ∃ action : MulAction (rootsOfUnity d E) I.minimalPrimes,
      letI := action
      (∀ (v : rootsOfUnity d E) (P : I.minimalPrimes),
        (v • P).val = P.val.comap (polynomialScalarEquiv (v : Eˣ)).toRingHom) ∧
      (∀ (v : rootsOfUnity d E) (P : I.minimalPrimes), v • P = P → v = 1) ∧
      d ∣ Nat.card I.minimalPrimes := by
  let I := extendCoefficientIdeal E (fiberVanishingIdeal (L := polynomialOutputField H) x)
  obtain ⟨T, S, hTS, hST, hG⟩ := constant_relation_constructs_zero_component_conjugacy H
    (theorem_1_1 d hd H hH hN) (Fin.last 3)
  let G := linearPolynomialConjugate T S H
  let Y := fun i => algebraMap R₄ (FractionRing R₄) (G i)
  have hNG := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hrG := (linearPolynomialConjugate_polyRank T S hTS hST H).trans hr
  have hJ := rationalJacobian_polynomial G
  have hNY : IsNilpotent (rationalJacobian Y) := hJ.symm ▸ hNG.map (algebraMap R₄ (FractionRing R₄)).mapMatrix
  have hrY : (rationalJacobian Y).rank = 3 := hJ.symm ▸ hrG
  have hY : Y (Fin.last 3) = 0 := by
    change algebraMap R₄ (FractionRing R₄) (linearPolynomialConjugate T S H (Fin.last 3)) = 0
    rw [hG, map_zero]
  obtain ⟨W⟩ := nilpotent_rank_three_zero_last_output_constructs_fiber_equations Y hNY hrY hY
  let : Algebra (polynomialOutputField G) E := conjugateOutputAlgebra T S hTS hST H E
  let : Algebra.IsAlgebraic (polynomialOutputField G) E := conjugateOutputAlgebra_isAlgebraic T S hTS hST H E
  let A := T.map (algebraMap K E)
  let B := S.map (algebraMap K E)
  have hAB : A * B = 1 := by
    change T.map (algebraMap K E) * S.map (algebraMap K E) = 1
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  have hBA : B * A = 1 := by
    change S.map (algebraMap K E) * T.map (algebraMap K E) = 1
    rw [← Matrix.map_mul, hST]
    ext i j
    simp [Matrix.one_apply]
  have hpoint (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
      let F := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
      let y := B.map (algebraMap E F) *ᵥ primeQuotientCoordinate P
      fiberVanishingIdeal (L := E) y ∈ (extendCoefficientIdeal E
        (fiberVanishingIdeal (L := polynomialOutputField G) x)).minimalPrimes :=
    inverse_frame_point_relations_form_conjugate_component T S hTS hST H E P hP
  constructor
  · intro P _ hP
    let F := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
    let z := primeQuotientCoordinate P
    let y := B.map (algebraMap E F) *ᵥ z
    let Q := fiberVanishingIdeal (L := E) y
    have hQ := hpoint P hP
    obtain ⟨C₀⟩ := fixed_last_geometric_component_constructs_affine_plane_chart Y W hNY hrY E Q hQ
    obtain ⟨f, hf⟩ := relation_prime_constructs_coordinate_embedding Q y rfl
    have hf' : f.toRingHom ∘ primeQuotientCoordinate Q = y := funext hf
    have hy : A.map (algebraMap E F) *ᵥ y = z := by
      have h1 : (1 : Matrix (Fin 4) (Fin 4) E).map (algebraMap E F) = 1 := by
        ext i j
        simp [Matrix.one_apply]
      rw [show y = B.map (algebraMap E F) *ᵥ z from rfl, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, hAB, h1, Matrix.one_mulVec]
    rcases C₀.equation_degree with he | he
    · have hl := C₀.liesInAffineLine_of_degree_one he
      have hl' := LiesInAffineLine.map_of_compatible f.toRingHom (RingHom.id E)
        (fun a => (f.commutes a).symm) (primeQuotientCoordinate Q) hl
      rw [hf'] at hl'
      left
      change LiesInAffineLine (E := E) z
      rw [← hy]
      exact hl'.mulVec A B hBA
    · obtain ⟨C₁⟩ := C₀.exists_affinePlaneConic he
      have C₂ := C₁.map f
      change AffinePlaneConic (E := E) (f.toRingHom ∘ primeQuotientCoordinate Q) at C₂
      rw [hf'] at C₂
      right
      change Nonempty (AffinePlaneConic (E := E) z)
      rw [← hy]
      exact ⟨C₂.mulVec A B hBA⟩
  · let action := homogeneousGenericFiberAction (E := E) H hH
    let : MulAction (rootsOfUnity d E) I.minimalPrimes := action
    have hAction (v : rootsOfUnity d E) (P : I.minimalPrimes) :
        (v • P).val = P.val.comap (polynomialScalarEquiv (v : Eˣ)).toRingHom := rfl
    have hfree (v : rootsOfUnity d E) (P : I.minimalPrimes) (hv : v • P = P) : v = 1 := by
      have hFix := congrArg (fun q : I.minimalPrimes => q.val) hv
      rw [hAction] at hFix
      let : P.val.IsPrime := P.property.isPrime
      let F := FractionRing (MvPolynomial (Fin 4) E ⧸ P.val)
      let z := primeQuotientCoordinate P.val
      let y := B.map (algebraMap E F) *ᵥ z
      let Q := fiberVanishingIdeal (L := E) y
      obtain ⟨a, ha, haQ⟩ := fixed_last_geometric_component_has_nonzero_last_value Y W hrY E Q
        (hpoint P.val P.property)
      have hya : y (Fin.last 3) = algebraMap E F a := by
        change aeval y (X (Fin.last 3) - C a) = 0 at haQ
        simpa only [map_sub, aeval_X, aeval_C, sub_eq_zero] using haQ
      let L := linearFormPolynomial (B (Fin.last 3))
      have hL : aeval z L = algebraMap E F a := by
        change aeval z (linearFormPolynomial (B (Fin.last 3))) = _
        simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
        exact hya
      apply Subtype.val_injective
      exact scalar_stabilizer_trivial_of_linear_value P.val L (linearFormPolynomial_homogeneous _) a ha hL v.val hFix
    let : NeZero d := ⟨hd.ne'⟩
    let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
    let : NeZero (d : E) := ⟨Nat.cast_ne_zero.mpr hd.ne'⟩
    let : Finite I.minimalPrimes := I.finite_minimalPrimes_of_isNoetherianRing
    have hcard := free_finite_action_group_card_dvd hfree
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity E d] at hcard
    exact ⟨action, hAction, hfree, hcard⟩

end DimensionFourDependence
