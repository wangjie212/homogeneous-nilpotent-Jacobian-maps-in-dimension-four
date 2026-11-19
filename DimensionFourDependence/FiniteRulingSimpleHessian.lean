import DimensionFourDependence.FiniteParameterGraphRuling
import DimensionFourDependence.RulingMixedDerivative

/-! # Constructed finite ruling directions give the actual simple Hessian root

The actual dual basis of the independent root forms supplies both
ruling directions. Its coordinate derivations fix the original Gauss
parameter and retain all four dual pairings. The original root equation
then proves zero self-pairing at the fixed direction and a nonzero
mixed Hessian pairing with the transverse ruling direction.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A finite coefficient ruling vector differentiates every finite
coefficient covector by its exact original dual pairing. -/
theorem finite_parameter_graph_covector_direction_derivative
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (v m : Fin 3 → C) (hv : v ∈ finiteParameterGraphRuling p C A) :
    coordinateEuler (fun i => (v i : F)) delta ((fun i => (m i : F)) ⬝ᵥ y) =
      algebraMap C F (m ⬝ᵥ v) := by
  have ht : coordinateEuler (fun i => (v i : F)) delta (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst _
      (finiteParameterGraphRuling_original_pairing p C A v hv)
  rw [parameter_algebraic_covector_direction_derivative p delta y _ _ hcoord ht
    (fun i => finite_parameter_extension_coefficient_algebraic p C (m i))]
  simp only [dotProduct, map_sum, map_mul, IntermediateField.algebraMap_apply]

/-- The actual root forms construct both original-coordinate ruling
directions and the zero/nonzero Hessian pairings at the fixed root.
No fixed vector, transverse vector, Hessian zero or mixed scalar is supplied. -/
theorem finite_parameter_graph_constructs_simple_root_hessian_pair
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    {d : ℕ} (hd : 0 < d) (rho c : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y) :
    ∃ b z : Fin 3 → C, LinearIndependent C ![b, z] ∧
      b ∈ finiteParameterGraphRuling p C A ∧ z ∈ finiteParameterGraphRuling p C A ∧
      m ⬝ᵥ b = 1 ∧ s ⬝ᵥ b = 0 ∧ m ⬝ᵥ z = 0 ∧ s ⬝ᵥ z = 1 ∧
      matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c))
        (fun i => (b i : F)) (fun i => (b i : F)) = 0 ∧
      matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c))
        (fun i => (z i : F)) (fun i => (b i : F)) =
          (d : F)⁻¹ * rho / ((fun i => (s i : F)) ⬝ᵥ y) ∧
      matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c))
        (fun i => (z i : F)) (fun i => (b i : F)) ≠ 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨b, z, hLI, hb, hz, hMb, hSb, hMz, hSz, _hspan⟩ :=
    two_dimensional_ruling_coordinate_basis (finiteParameterGraphRuling p C A)
      (finiteParameterGraphRuling_finrank p C A hfirst) m s hpair
  let D := coordinateEuler (fun i => (b i : F)) delta
  let E := coordinateEuler (fun i => (z i : F)) delta
  let r : F := (fun i => (m i : F)) ⬝ᵥ y
  let t : F := (fun i => (s i : F)) ⬝ᵥ y
  have hDr : D r = 1 := by
    rw [show D r = coordinateEuler (fun i => (b i : F)) delta ((fun i => (m i : F)) ⬝ᵥ y) from rfl,
      finite_parameter_graph_covector_direction_derivative p delta y hcoord A htangent hfirst C b m hb,
      hMb, map_one]
  have hDt : D t = 0 := by
    rw [show D t = coordinateEuler (fun i => (b i : F)) delta ((fun i => (s i : F)) ⬝ᵥ y) from rfl,
      finite_parameter_graph_covector_direction_derivative p delta y hcoord A htangent hfirst C b s hb,
      hSb, map_zero]
  have hEt : E t = 1 := by
    rw [show E t = coordinateEuler (fun i => (z i : F)) delta ((fun i => (s i : F)) ⬝ᵥ y) from rfl,
      finite_parameter_graph_covector_direction_derivative p delta y hcoord A htangent hfirst C z s hz,
      hSz, map_one]
  have htD : D (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst _
      (finiteParameterGraphRuling_original_pairing p C A b hb)
  have htE : E (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst _
      (finiteParameterGraphRuling_original_pairing p C A z hz)
  have hbD (i : Fin 3) : D (b i : F) = 0 :=
    parameter_algebraic_coefficient_direction_constant p D htD (b i : F)
      (finite_parameter_extension_coefficient_algebraic p C (b i))
  have hbE (i : Fin 3) : E (b i : F) = 0 :=
    parameter_algebraic_coefficient_direction_constant p E htE (b i : F)
      (finite_parameter_extension_coefficient_algebraic p C (b i))
  have hroots := linear_root_factor_fixed_and_mixed_derivatives D E hd r t rho hrho hroot hDr hDt hEt
  have hself : matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c))
      (fun i => (b i : F)) (fun i => (b i : F)) = 0 := by
    rw [← coordinate_direction_mixed_derivative delta _ _ hbD, hfactor]
    exact hroots.2.1
  have hmixed : matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c))
      (fun i => (z i : F)) (fun i => (b i : F)) = (d : F)⁻¹ * rho / t := by
    rw [← coordinate_direction_mixed_derivative delta _ _ hbE, hfactor]
    exact hroots.2.2.1
  refine ⟨b, z, hLI, hb, hz, hMb, hSb, hMz, hSz, hself, hmixed, ?_⟩
  rw [← coordinate_direction_mixed_derivative delta _ _ hbE, hfactor]
  exact hroots.2.2.2

end DimensionFourDependence
