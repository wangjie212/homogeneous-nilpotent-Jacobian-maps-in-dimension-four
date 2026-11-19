import DimensionFourDependence.SegreRealizedFiniteRootForms

/-! # The original ruling-wise radial-product power factorization -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The actual radial pairing has a linear factor times a dth power
on the specified ruling, over one finite extension of its original
parameter. The selected actual infinity point lies on the linear factor,
and both linear forms are nonzero at the original generic output. -/
def SegreFiniteRadialProductFactorization
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
    ∃ C : IntermediateField (segreProjectiveRulingParameterField K Y j p a)
        (projectivePrimeRatioField p (some a)),
      Module.Finite (segreProjectiveRulingParameterField K Y j p a) C ∧
      ∃ R B : Fin 3 → C, R ≠ 0 ∧ B ≠ 0 ∧
        (algebraMap E (projectivePrimeRatioField p (some a)) f) ^ d =
          ((fun i => (R i : projectivePrimeRatioField p (some a))) ⬝ᵥ
            (fun i : Fin 3 => algebraMap E _ (Y i.castSucc))) *
          ((fun i => (B i : projectivePrimeRatioField p (some a))) ⬝ᵥ
            (fun i : Fin 3 => algebraMap E _ (Y i.castSucc))) ^ d ∧
        (fun i => (R i : projectivePrimeRatioField p (some a))) ⬝ᵥ
          (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc)) = 0 ∧
        ((fun i => (R i : projectivePrimeRatioField p (some a))) ⬝ᵥ
          (fun i : Fin 3 => algebraMap E _ (Y i.castSucc))) ≠ 0 ∧
        ((fun i => (B i : projectivePrimeRatioField p (some a))) ⬝ᵥ
          (fun i : Fin 3 => algebraMap E _ (Y i.castSucc))) ≠ 0

variable [CharZero K] {G : Type u} [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual realized fiber and finite selected point construct
all factorization data, including the nonzero restrictions of both forms. -/
theorem segre_realized_finite_boundary_constructs_radial_product_factorization
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (c q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) c q k x y)
    {d : ℕ} (hd : 0 < d) (hc0 : c ≠ 0)
    (hc : coefficientEuler Y hY c = algebraMap K _ ((d : K)⁻¹) * c)
    (htr : Algebra.trdeg K E = 3) (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hboundary : p ∈ projectiveClosureSet (L := E) x)
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial (y j.castSucc / y 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (y j.castSucc / y 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (hfinite : SegreFiniteRulingBoundaryPoint K y j p) :
    SegreFiniteRadialProductFactorization K y (y 0 * R.coefficientMap c) d j p := by
  obtain ⟨a, ha, C, hC, m, s, ρ, hm, hs, hρ, _hfactor, hroot, hsv, hpower, hformula⟩ :=
    segre_realized_finite_boundary_constructs_radial_product_root_forms
      Y hY c q k x y R hd hc0 hc htr j hj p hboundary hinfty hR0 hR1 hfinite
  refine ⟨a, ha, C, hC, s, m, hs, hm, hpower, hsv, ?_, ?_⟩
  · rw [← hroot]
    exact pow_ne_zero d hρ
  · intro hz
    rw [hz, div_zero] at hformula
    exact hρ hformula

end DimensionFourDependence
