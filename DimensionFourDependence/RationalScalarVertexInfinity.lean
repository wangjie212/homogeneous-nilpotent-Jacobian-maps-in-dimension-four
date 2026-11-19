import DimensionFourDependence.RationalScalarBoundary
import DimensionFourDependence.GenericGraphVertexInfinity

/-! # The original fixed vertex survives an independent homogeneous scale -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L A F κ : Type*} [Field L] [CommRing A] [Field F] [Field κ]
  [Algebra L A] [Algebra L F] [Algebra L κ]

/-- Independent rational source scaling retains the original fourth
axis at infinity over the entire rationally enlarged coefficient field. -/
theorem independent_rational_scale_retains_fixed_vertex_infinity
    (ι : A →ₐ[L] F) (hι : Function.Injective ι) (π : A →ₐ[L] κ)
    (v : Fin 4 → F) (s : F) (z : Option (Fin 4) → A)
    (hz : ∀ j, ι (z j) = s * j.elim 1 v)
    (hres : (fun j => π (z j)) =
      (fun j : Option (Fin 4) => j.elim 0 (Fin.snoc (0 : Fin 3 → κ) 1))) :
    ∃ α : RatFunc L →ₐ[L] RatFunc F, α RatFunc.X = RatFunc.X ∧
      letI : Algebra (RatFunc L) (RatFunc F) := α.toRingHom.toAlgebra
      fourthAxisAffineInfinityPoint (RatFunc L) ∈
        projectiveClosureSet (L := RatFunc L) (fun i => RatFunc.X * RatFunc.C (v i)) := by
  have hresne : (fun j => π (z j)) ≠ 0 := by
    rw [hres]
    exact option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
  obtain ⟨α, hα, β, hβ, hb, hboundary⟩ :=
    independent_rational_scale_preserves_residue_projective_boundary ι hι π v s z hz hresne
  refine ⟨α, hα, ?_⟩
  letI : Algebra (RatFunc L) (RatFunc F) := α.toRingHom.toAlgebra
  letI : Algebra (RatFunc L) (RatFunc κ) := β.toAlgebra
  let c : Option (Fin 4) → RatFunc L :=
    fun j => j.elim 0 (Fin.snoc (0 : Fin 3 → RatFunc L) 1)
  have hc : c ≠ 0 := option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
  have hmap : (fun j => algebraMap (RatFunc L) (RatFunc κ) (c j)) ≠ 0 := by
    intro he
    have h := congrFun he (some (Fin.last 3))
    exact one_ne_zero (by
      simpa only [c, Option.elim_some, Fin.snoc_last, map_one, Pi.zero_apply] using h)
  have hprop (j : Option (Fin 4)) :
      rationalScalarProjectiveVector (fun j => π (z j)) j =
        RatFunc.X * algebraMap (RatFunc L) (RatFunc κ) (c j) := by
    cases j with
    | none =>
      have he : π (z none) = 0 := congrFun hres none
      simp only [rationalScalarProjectiveVector, c, Option.elim_none, he, map_zero, mul_zero]
    | some i =>
      have he := congrFun hres (some i)
      change π (z (some i)) = (Fin.snoc (0 : Fin 3 → κ) 1 : Fin 4 → κ) i at he
      simp only [rationalScalarProjectiveVector, Option.elim_some, he]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [c, Option.elim_some, Fin.snoc_last, map_one]
      · simp only [c, Option.elim_some, Fin.snoc_castSucc, Pi.zero_apply, map_zero]
  have hp := projectiveFieldPoint_eq_of_proportional (K := RatFunc L)
    (rationalScalarProjectiveVector (fun j => π (z j))) _ hb hmap
    RatFunc.X RatFunc.X_ne_zero hprop
  rw [projectiveFieldPoint_map_eq c hc hmap] at hp
  rw [hp] at hboundary
  exact hboundary

end DimensionFourDependence
