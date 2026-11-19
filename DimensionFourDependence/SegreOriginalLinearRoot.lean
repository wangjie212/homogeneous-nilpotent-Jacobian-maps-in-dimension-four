import DimensionFourDependence.SegreGlobalLinearRoot

/-! # The original nonlinear Segre fiber constructs the nonzero original source linear root -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower

universe u
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- From the original map and an actual nonlinear geometric component,
the nonzero first-invariant branch constructs the paper's original
source linear form ell=rc/B(H) and the exact polynomial identity
ell^d=R(H). The actual invariant, global factors, denominator nonvanishing,
normality and Euler homogeneity are all derived internally. -/
theorem original_segre_nonlinear_geometric_fiber_constructs_source_linear_root
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate Q)) :
    ∃ (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
      (c : coefficientField (K := K) (segreOriginalOutputTriple H)),
      (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
        (segreOriginalCoefficientGraph H) ∧
      (c ≠ 0 → ∃ a b l : Fin 4 → K, a ≠ 0 ∧ b ≠ 0 ∧ l ≠ 0 ∧
        algebraMap R₀ S₀ (linearFormPolynomial l) =
          (algebraMap R₀ S₀ (H 0) * (c : S₀)) /
            ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) ∧
        linearFormPolynomial l ^ d = outputLinearCombination H a) := by
  obtain ⟨hY, c, q, k, R, hc, _hq, _hk, _hce, _hqe, hbranch⟩ :=
    original_segre_nonlinear_geometric_fiber_constructs_global_radial_hyperplanes
      H hd hH hN hrank hind hSegre E Q hQ hline
  refine ⟨hY, c, hc, ?_⟩
  intro hc0
  obtain ⟨a, b, ha, hb, _haY, _hbY, _heGeo, heSource⟩ := hbranch hc0
  have hcSource : (c : S₀) ≠ 0 :=
    (map_ne_zero (algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) S₀)).mpr hc0
  have hf : algebraMap R₀ S₀ (H 0) * (c : S₀) ≠ 0 :=
    mul_ne_zero (original_segre_first_output_ne_zero H hind) hcSource
  obtain ⟨l, hl, hvalue, hpower⟩ :=
    segre_global_radial_hyperplane_identity_constructs_source_linear_root
      H hd hH hind _ hf a b hb heSource
  exact ⟨a, b, l, ha, hb, hl, hvalue, hpower⟩

end DimensionFourDependence
