import DimensionFourDependence.AffineParameterParabolaObstruction
import DimensionFourDependence.VertexPreservingParabolaTransport
import DimensionFourDependence.SecondCoordinateAffineChart

/-! # The original nonlinear vertex parabola excludes the constructed affine parameter

The inverse source change transports the actual source-field realization
and the whole parabolic point. The transported parameter remains a
geometric coefficient constant. Its affine chart denominator is nonzero
by injectivity of the actual source-field realization. The original
quadratic vertex coefficient then contradicts the affine parameter.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type*} [Field K] [Field E] [Field G]
    [Algebra K E] [Algebra K G] [Algebra E G] [IsScalarTower K E G]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Actual source realization commutes with the full second-coordinate
chart evaluation, preserving its original three coordinate ratios. -/
theorem second_coordinate_chart_source_algHom_value
    (ψ : S₀ →ₐ[K] G) (P : MvPolynomial (Fin 3) K) :
    ψ (aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))) P) =
      aeval (![ψ (rationalCoordinate (K := K) (0 : Fin 4)) /
          ψ (rationalCoordinate (K := K) (1 : Fin 4)),
        ψ (rationalCoordinate (K := K) (2 : Fin 4)) /
          ψ (rationalCoordinate (K := K) (1 : Fin 4)),
        ψ (rationalCoordinate (K := K) (3 : Fin 4)) /
          ψ (rationalCoordinate (K := K) (1 : Fin 4))] : Fin 3 → G) P := by
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 3 → G => aeval v P)
  funext i
  fin_cases i <;> simp [second_coordinate_cone_chart_point, map_div₀]

/-- A parameter constant on the actual original nonlinear vertex
parabola cannot become an affine polynomial with nonzero vertex partial
after the actual vertex-preserving source coordinate change. -/
theorem vertex_preserving_conjugated_affine_parameter_parabola_impossible
    (f : S₀ →ₐ[K] G) (z : Fin 4 → G)
    (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (t : G) (ht : Transcendental E t) (x A : Fin 3 → E) (w0 B C : E) (hC : C ≠ 0)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E G w0 + algebraMap E G B * t + algebraMap E G C * t ^ 2)
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (r : S₀) (c : E) (hr : f r = algebraMap E G c)
    (P : MvPolynomial (Fin 3) K) (hP : P.totalDegree ≤ 1) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (hparameter : matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST r =
      aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))) P) : False := by
  let φ := matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
  let ψ := f.comp φ.symm.toAlgHom
  let z' : Fin 4 → G := fun i => ψ (rationalCoordinate (K := K) i)
  obtain ⟨x', A', hx', hv⟩ := vertex_preserving_inverse_source_realization_parabola f z hf T S hTS hST t x A hx
  have hw' : z' (Fin.last 3) = algebraMap E G w0 + algebraMap E G B * t + algebraMap E G C * t ^ 2 :=
    hv.trans hw
  have hvalue : ψ (aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))) P) =
      algebraMap E G c := by
    rw [← hparameter]
    change f (φ.symm (φ r)) = _
    rw [φ.symm_apply_apply]
    exact hr
  have hcoord : rationalCoordinate (K := K) (1 : Fin 4) ≠ (0 : S₀) := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀).ne (X_ne_zero (1 : Fin 4))
  have hy : z' 1 ≠ 0 := by
    intro hz
    apply hcoord
    apply ψ.injective
    change z' 1 = ψ 0
    rw [map_zero]
    exact hz
  have hchart : aeval (![z' 0 / z' 1, z' 2 / z' 1, z' 3 / z' 1] : Fin 3 → G) P =
      algebraMap E G c := (second_coordinate_chart_source_algHom_value ψ P).symm.trans hvalue
  exact affine_parameter_constant_on_nonlinear_vertex_parabola_impossible
    P hP hPw t ht z' x' A' w0 B C c hC hx' hw' hy hchart

end DimensionFourDependence
