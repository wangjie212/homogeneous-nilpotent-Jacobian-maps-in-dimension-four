import DimensionFourDependence.ProjectiveSectionProjectionRegularity

/-! # Projection regularities with the actual divisor-selected coordinate order

The original linear projection may choose either base coordinate as its
transcendental residue parameter. Reindexing its three coordinate values
retains the original linear forms and gives both section regularities
without constructing another projection or assuming a fixed base order.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial Matrix

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {F k L : Type u} [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L]
  [Algebra (RatFunc k) L] [IsScalarTower F (RatFunc k) L]
  [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- Every global regular original-chart section supplies both finite
and infinity projection integrality conditions. The monic equation and
the actual projection coordinate values construct all auxiliary frame
ratios; no section integrality or auxiliary-chart section is assumed. -/
theorem projective_original_chart_section_two_reindexed_projection_regularities
    (x : Fin 4 → L) (sectionValue : ProjectiveNormalizedSection (k := F) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (T : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (r : Fin 3 ≃ Fin 3) (v : L) (u : k)
    (hcoordinates : (fun i => linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) (r i)) =
      ![v, algebraMap (RatFunc k) L RatFunc.X, algebraMap (RatFunc k) L (RatFunc.C u)])
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (hroot : Polynomial.aeval v P = 0) :
    IsIntegral (Polynomial k) (sectionValue.coefficient (s.symm none) : L) ∧
      IsIntegral (rationalInfinityRing k)
        (algebraMap (RatFunc k) L (RatFunc.X⁻¹) *
          (sectionValue.coefficient (s.symm none) : L)) := by
  classical
  let a := s.symm none
  have ha : x a ≠ 0 := hbase
  let y := linearProjectionCoordinate T (fun j => x (s.symm (some j)) / x a)
  have hfiniteConstants (z : F) : IsIntegral (Polynomial k) (algebraMap F L z) := by
    rw [IsScalarTower.algebraMap_apply F (RatFunc k) L]
    change IsIntegral (Polynomial k)
      (algebraMap (RatFunc k) L (RatFunc.C (algebraMap F k z)))
    exact projection_constant_isIntegral_finite _
  have hinfinityConstants (z : F) : IsIntegral (rationalInfinityRing k) (algebraMap F L z) := by
    rw [IsScalarTower.algebraMap_apply F (RatFunc k) L]
    change IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.C (algebraMap F k z)))
    exact projection_constant_isIntegral_infinity _
  have hyfinite (j : Fin 3) : IsIntegral (Polynomial k) (y j) := by
    obtain ⟨i, rfl⟩ := r.surjective j
    change IsIntegral (Polynomial k) (linearProjectionCoordinate T
      (fun l => x (s.symm (some l)) / x (s.symm none)) (r i))
    rw [congrFun hcoordinates i]
    fin_cases i
    · exact ⟨P, hP, hroot⟩
    · exact projection_variable_isIntegral_finite
    · exact projection_constant_isIntegral_finite u
  have hfiniteRatios : ∀ i, IsIntegral (Polynomial k) (x i / x a) := by
    apply projective_ratios_integral_of_scaled_projection T x s hbase (x a) hbase hfiniteConstants
    · change IsIntegral (Polynomial k) (x a / x a)
      rw [div_self ha]
      exact isIntegral_one
    · intro j
      change IsIntegral (Polynomial k) ((x a / x a) * y j)
      rw [div_self ha, one_mul]
      exact hyfinite j
  have hfinite := projective_normalized_section_linear_frame_isIntegral x sectionValue
    (Pi.single a 1) (x a) hbase (by simp [Pi.single_apply]) hfiniteConstants hfiniteRatios a
  have hfinite' : IsIntegral (Polynomial k) (sectionValue.coefficient a : L) := by
    simpa only [mul_div_cancel_right₀ _ ha] using hfinite
  let w := algebraMap (RatFunc k) L RatFunc.X
  let t := algebraMap (RatFunc k) L (RatFunc.X⁻¹)
  let h := x a * w
  have hw : w ≠ 0 := by
    simpa only [map_zero] using (algebraMap (RatFunc k) L).injective.ne RatFunc.X_ne_zero
  have hh : h ≠ 0 := mul_ne_zero hbase hw
  have htvalue : x a / h = t := by
    change x a / (x a * w) = algebraMap (RatFunc k) L (RatFunc.X⁻¹)
    rw [map_inv₀]
    change x a / (x a * w) = w⁻¹
    field_simp [ha, hw]
  have hyinfinity (j : Fin 3) : IsIntegral (rationalInfinityRing k) (t * y j) := by
    obtain ⟨i, rfl⟩ := r.surjective j
    change IsIntegral (rationalInfinityRing k) (algebraMap (RatFunc k) L (RatFunc.X⁻¹) *
      linearProjectionCoordinate T (fun l => x (s.symm (some l)) / x (s.symm none)) (r i))
    rw [congrFun hcoordinates i]
    fin_cases i
    · exact infinity_scaled_root_isIntegral_of_monic_degree_bounds P hP hdegree v hroot
    · change IsIntegral (rationalInfinityRing k)
        (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap (RatFunc k) L RatFunc.X)
      rw [← map_mul, inv_mul_cancel₀ RatFunc.X_ne_zero, map_one]
      exact isIntegral_one
    · exact projection_scaled_constant_isIntegral_infinity u
  have hinfinityRatios : ∀ i, IsIntegral (rationalInfinityRing k) (x i / h) := by
    apply projective_ratios_integral_of_scaled_projection T x s hbase h hh hinfinityConstants
    · rw [htvalue]
      exact projection_parameter_isIntegral_infinity
    · intro j
      rw [htvalue]
      exact hyinfinity j
  have hlinear : h = ∑ i, algebraMap F L (projectionProjectiveFrameCoefficients T s (r 1) i) * x i := by
    have hframe := (projection_projective_frame_eq T x s hbase (r 1)).symm
    rw [congrFun hcoordinates (1 : Fin 3)] at hframe
    exact hframe
  have hinfinity := projective_normalized_section_linear_frame_isIntegral x sectionValue
    (projectionProjectiveFrameCoefficients T s (r 1)) h hh hlinear hinfinityConstants hinfinityRatios a
  have hvalue : (sectionValue.coefficient a : L) * x a / h = t * (sectionValue.coefficient a : L) := by
    change (sectionValue.coefficient a : L) * x a / (x a * w) =
      algebraMap (RatFunc k) L (RatFunc.X⁻¹) * (sectionValue.coefficient a : L)
    rw [map_inv₀]
    change (sectionValue.coefficient a : L) * x a / (x a * w) = w⁻¹ * (sectionValue.coefficient a : L)
    field_simp [ha, hw]
  exact ⟨hfinite', Eq.mp (congrArg (fun z : L => IsIntegral (rationalInfinityRing k) z) hvalue) hinfinity⟩

end DimensionFourDependence
