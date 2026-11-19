import DimensionFourDependence.FiniteGaussBoundaryPoint
import DimensionFourDependence.FiniteGaussBoundaryLocalIntersection
import DimensionFourDependence.ProjectiveModifiedBoundaryEquation

/-! # The constructed simple-root chart bounds the actual infinity local ring

An actual projective boundary point and the original affine fiber
equations identify the constructed chart point with the boundary.
The same graph and root data construct both chart equations and the
simple transverse derivative. Consequently the full actual infinity
chart ideal has origin-local dimension and length at most two.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F]

/-- The actual rational-origin localization of the entire ideal is
finite over its coefficient field, with dimension and length at most two. -/
noncomputable def HasOriginLocalLengthAtMostTwo (I : Ideal (MvPolynomial (Fin 2) F)) : Prop :=
  ∃ hI : I ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom,
    let R := Localization.AtPrime (zeroPointQuotientPrime I hI)
    Module.Finite F R ∧ finrank F R ≤ 2 ∧ Module.length R R ≤ 2

variable {K G : Type*} [Field K] [CharZero K] [Field G] [Algebra K F] [Algebra F G]

/-- From an actual projective boundary point, original graph and
affine fiber equations, and the independent finite root forms, construct
an invertible chart at that very point with local length at most two.
No point identification, equation membership, local quotient map,
rank-one Hessian formula, or simple transverse jet is supplied. -/
theorem finite_parameter_graph_constructs_actual_boundary_chart_local_bound
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, delta i (delta j a) = delta j (delta i a))
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, delta i h = p (A i))
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    {d : ℕ} (hd : 1 < d) (rho c q k : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y)
    (x : Fin 3 → G) (v : Fin 3 → F) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 v)
      (infinity_direction_projective_coordinates_ne_zero v hv) ∈ projectiveClosureSet (L := F) x)
    (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (hQ : aeval x (quadraticFiberPolynomial (fun i => delta i c) (derivationHessian delta h) q) = 0)
    (hC : aeval x (cubicFiberPolynomial (fun i => delta i q)
      (derivationHessian delta c) (derivationCubicTensor delta h) k) = 0) :
    ∃ w z b : Fin 3 → C,
      finiteParameterGraphNormal p C A ⬝ᵥ w = 1 ∧
      b ∈ finiteParameterGraphRuling p C A ∧ z ∈ finiteParameterGraphRuling p C A ∧
      m ⬝ᵥ b = 1 ∧ s ⬝ᵥ b = 0 ∧ m ⬝ᵥ z = 0 ∧ s ⬝ᵥ z = 1 ∧
      (rulingBoundaryCoordinateMatrix w z b).det ≠ 0 ∧
      (rulingBoundaryCoordinateMatrix (fun i => (w i : F)) (fun i => (z i : F)) (fun i => (b i : F))).det ≠ 0 ∧
      ∃ hbF : (fun i => (b i : F)) ≠ 0,
        projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 (fun i => (b i : F)))
          (infinity_direction_projective_coordinates_ne_zero _ hbF) ∈ projectiveClosureSet (L := F) x ∧
        HasOriginLocalLengthAtMostTwo
          (projectiveInfinityChartIdeal x (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (z i : F))) := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨w, z, b, hw, hb, hz, hmb, hsb, hmz, hsz, hdet, hdetF,
      hsecond, htransverse, hfirstChart, _hpairIdeal, _hpairLocal⟩ :=
    finite_parameter_graph_constructs_actual_simple_boundary_intersection p delta y hcoord hcomm
      A htangent hfirst h hgradient C m s hpair (by omega : 0 < d) rho c q hrho hfactor hroot
  have hboundary := parametric_graph_projective_boundary_equations p delta y hcoord A htangent hfirst
    h hgradient x (fun j : Option (Fin 3) => j.elim 0 v)
    (infinity_direction_projective_coordinates_ne_zero v hv) hpoint rfl id c q k hQ hC
  obtain ⟨t, ht, hrep⟩ := finite_parameter_graph_boundary_multiple_of_specified_dual_point
    p delta y hcoord A htangent hfirst C m s b z hpair hb hz hmb hsb hmz hsz
    hd rho c hrho hfactor hroot v hv hboundary.1 halg hboundary.2
  obtain ⟨hbF, hbpoint⟩ := projective_closure_infinity_point_of_nonzero_smul x v
    (fun i => (b i : F)) hv hpoint t ht hrep
  refine ⟨w, z, b, hw, hb, hz, hmb, hsb, hmz, hsz, hdet, hdetF, hbF, hbpoint, ?_⟩
  exact projective_closure_infinity_chart_origin_local_bound x _ _ _
    (fun i => delta i c) (fun i => delta i q) (parametricGraphCubicCovector p A y) hbF hbpoint
    (derivationHessian delta h) (derivationHessian delta c) (derivationCubicTensor delta h) q k
    (parametric_graph_cubic_polynomial_factorization p delta y hcoord A htangent hfirst h hgradient)
    hQ hC ((2 : F)⁻¹ * (-(parametricRulingDenominator p A y)⁻¹))
    (mul_ne_zero (inv_ne_zero (by norm_num))
      (neg_ne_zero.mpr (inv_ne_zero (parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst))))
    hfirstChart hsecond htransverse

end DimensionFourDependence
