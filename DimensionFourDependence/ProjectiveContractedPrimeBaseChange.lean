import DimensionFourDependence.ProjectivePencilPrimeSource

/-! # Finite coefficient base change derived from an actual contracted prime

No horizontal parameter or residue hypothesis is an input here. The
actual curve prime supplies that data, and every finite extension of the
closed Gauss field then gives the Dedekind source model.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3)) {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

/-- A curve-prime contraction constructs a compatible horizontal local
parameter and Dedekind source models for every finite coefficient extension. -/
theorem actual_projective_contracted_prime_base_change_dedekind
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      ∃ (t : Localization.AtPrime Q)
        (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t)),
        primeLocalizationFractionHom (F := L₀) Q t =
          closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X ∧
        ∀ (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E],
          letI : Algebra C₀ (Localization.AtPrime Q) :=
            (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
          letI : CommRing (Localization.AtPrime Q ⊗[C₀] E) :=
            Algebra.TensorProduct.instCommRing (R := C₀) (A := Localization.AtPrime Q) (B := E)
          IsDedekindDomain (Localization.AtPrime Q ⊗[C₀] E) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  obtain ⟨t, ht, hX⟩ := actual_projective_contracted_prime_horizontal_parameter H I s hH e Q f hf hQ P
  refine ⟨t, ht, hX, ?_⟩
  intro E hE halg hfinite
  exact actual_projective_horizontal_divisor_base_change_dedekind H hH I e s Q f hf hQ t ht hX E

end DimensionFourDependence
