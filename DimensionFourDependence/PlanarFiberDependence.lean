import DimensionFourDependence.PlanarTangentDependence

/-! # The fixed-plane fiber criterion in actual function-field coordinates

An affine translate of a fixed two-space has tangent in that two-space.
For a nonlinear actual fiber, tangent variation and the image normal then
give a constant component relation. All normals, tangent vectors and
constant-field assertions are constructed from the original hypotheses.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K F] [Algebra E F] {n : ℕ}

/-- Coordinates in a translate, over `E`, of a direction plane fixed over `K`. -/
def LiesInConstantPlaneTranslate (v w : Fin n → K) (x : Fin n → F) : Prop :=
  ∃ a : Fin n → E, ∃ r s : F, ∀ i,
    x i = algebraMap E F (a i) + algebraMap K F (v i) * r + algebraMap K F (w i) * s

variable [CharZero K]

/-- The actual source tangent lies in the fixed direction plane whenever
the source generic point lies in a translate over its coefficient field. -/
theorem actual_fiber_tangent_mem_translate_plane
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) (v w : Fin 4 → K)
    (hplane : LiesInConstantPlaneTranslate (E := coefficientField (K := K) Y) v w
      (rationalCoordinate (K := K) (n := 4))) :
    u ∈ Submodule.span (FractionRing (MvPolynomial (Fin 4) K)) (Set.range
      ![(fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)),
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (w i))]) := by
  obtain ⟨a, r, s, hpos⟩ := hplane
  let D := sourceVectorDerivation u
  have ha (i : Fin 4) : D (algebraMap (coefficientField (K := K) Y)
      (FractionRing (MvPolynomial (Fin 4) K)) (a i)) = 0 :=
    (fiberTangentDerivation Y hY u hu hker).map_algebraMap (a i)
  apply (Submodule.mem_span_range_iff_exists_fun
    (R := FractionRing (MvPolynomial (Fin 4) K))).mpr
  refine ⟨![D r, D s], ?_⟩
  funext i
  have he := congrArg D (hpos i)
  rw [show D (rationalCoordinate (K := K) i) = u i from sourceVectorDerivation_coordinate u i] at he
  rw [map_add, map_add, ha i, zero_add] at he
  simpa [Fin.sum_univ_two, Pi.smul_apply, D.leibniz, smul_eq_mul, mul_comm] using he.symm

/-- The fixed-plane assertion of Proposition 2.3 in the actual source
function field: a nonlinear fiber in a translate of one fixed two-space
forces dependence. The geometric generic-fiber comparison is separate. -/
theorem dependent_of_nonlinear_fiber_in_fixed_plane
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : LiesInConstantPlaneTranslate
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc)))) v w
      (rationalCoordinate (K := K) (n := 4)))
    (hline : ¬ LiesInAffineLine
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))))
      (rationalCoordinate (K := K) (n := 4))) : ComponentsDependent H := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  let N := (jac H).map (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)))
  have hNf : IsNilpotent N := hN.map
    (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  obtain ⟨u, hu, hku⟩ := matrix_nilpotent_exists_nonzero_kernel N hNf
    (by change 0 < polyRank (jac H); omega)
  have hkerQ : rationalJacobian Q *ᵥ u = 0 := by rwa [rationalJacobian_polynomial H]
  have hkerY : rationalJacobian (fun i : Fin 3 => Q (W.chart i.castSucc)) *ᵥ u = 0 := by
    funext i
    exact congrFun hkerQ (W.chart i.castSucc)
  have htan := actual_fiber_tangent_mem_translate_plane _ W.independent u hu hkerY v w hplane
  exact dependent_of_nonlinear_planar_actual_tangent H hd hH hN hrank W u hu hku v w hvw htan hline

end DimensionFourDependence
