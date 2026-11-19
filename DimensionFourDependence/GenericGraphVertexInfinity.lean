import DimensionFourDependence.GenericGraphProjectiveBoundary
import DimensionFourDependence.ScaledPlaneVertexAffineFiberBoundary

/-! # A free graph level retains the fixed original source vertex at infinity -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R F : Type*} [Field k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra k R] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]

/-- Exact zero and unit coordinate residues identify the generic-level
boundary with the fixed fourth source axis over the rational level field.
The resulting embedding preserves every original coefficient. -/
theorem rational_graph_retains_fixed_vertex_at_generic_level
    (f : F)
    (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))
    (v : Fin 4 → F) (s : F) (z : Option (Fin 4) → R)
    (hz : ∀ j, algebraMap R F (z j) = s * j.elim 1 v)
    (hres : (fun j => IsLocalRing.residue R (z j)) =
      (fun j : Option (Fin 4) => j.elim 0
        (Fin.snoc (0 : Fin 3 → IsLocalRing.ResidueField R) 1))) :
    ∃ α : RatFunc k →ₐ[k] F, α RatFunc.X = f ∧
      letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
      fourthAxisAffineInfinityPoint (RatFunc k) ∈ projectiveClosureSet (L := RatFunc k) v := by
  have hresne : (fun j => IsLocalRing.residue R (z j)) ≠ 0 := by
    rw [hres]
    exact option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
  obtain ⟨α, hα, β, hβ, hb, hboundary⟩ :=
    rational_graph_constructs_generic_level_projective_boundary (k := k) f hker v s z hz hresne
  refine ⟨α, hα, ?_⟩
  letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
  letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toAlgebra
  let c : Option (Fin 4) → RatFunc k :=
    fun j => j.elim 0 (Fin.snoc (0 : Fin 3 → RatFunc k) 1)
  have hc : c ≠ 0 := option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
  have he : (fun j => RatFunc.C (IsLocalRing.residue R (z j))) =
      (fun j => algebraMap (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) (c j)) := by
    funext j
    rw [congrFun hres j]
    cases j with
    | none => simp only [c, Option.elim_none, map_zero]
    | some i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [c, Option.elim_some, Fin.snoc_last, map_one]
      · simp only [c, Option.elim_some, Fin.snoc_castSucc, Pi.zero_apply, map_zero]
  have hmap : (fun j => algebraMap (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) (c j)) ≠ 0 := by
    rwa [← he]
  have hp := projectiveFieldPoint_eq_of_coordinate_eq (E := RatFunc k)
    (fun j => RatFunc.C (IsLocalRing.residue R (z j))) _ hb hmap he
  rw [projectiveFieldPoint_map_eq c hc hmap] at hp
  rw [hp] at hboundary
  exact hboundary

end DimensionFourDependence
