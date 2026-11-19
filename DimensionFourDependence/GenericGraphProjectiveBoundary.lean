import DimensionFourDependence.RationalGraphLocalParameter
import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # A rational graph's unspecialized level field retains the original boundary -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R F σ : Type*} [Field k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra k R] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]

/-- Integral original projective coordinates at the vertex define an
actual boundary point over the unspecialized rational level field.
Both embeddings of that field are constructed: its variable is the
original function f in the original field and stays a free rational
variable in the residue field. No scalar level is chosen. -/
theorem rational_graph_constructs_generic_level_projective_boundary
    (f : F)
    (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))
    (v : σ → F) (s : F) (z : Option σ → R)
    (hz : ∀ j, algebraMap R F (z j) = s * j.elim 1 v)
    (hres : (fun j => IsLocalRing.residue R (z j)) ≠ 0) :
    ∃ α : RatFunc k →ₐ[k] F, α RatFunc.X = f ∧
      letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
      ∃ β : RatFunc k →+* RatFunc (IsLocalRing.ResidueField R), β RatFunc.X = RatFunc.X ∧
        letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toAlgebra
        ∃ hb : (fun j => RatFunc.C (IsLocalRing.residue R (z j))) ≠ 0,
          projectiveFieldPoint (E := RatFunc k) (fun j => RatFunc.C (IsLocalRing.residue R (z j))) hb ∈
            projectiveClosureSet (L := RatFunc k) v := by
  let A := rationalGraphLocalAlgebra R f hker
  let a : RatFunc k →+* A := rationalGraphLocalParameterHom R f hker
  let ρ : A →+* RatFunc (IsLocalRing.ResidueField R) := rationalGraphLocalResidueHom R f hker
  let α : RatFunc k →ₐ[k] F :=
    { (algebraMap A F).comp a with
      commutes' := fun c => by
        change (rationalGraphLocalParameterHom (k := k) R f hker (RatFunc.C c) : F) = algebraMap k F c
        rw [rationalGraphLocalParameterHom_C]
        change algebraMap R F (algebraMap k R c) = algebraMap k F c
        exact (IsScalarTower.algebraMap_apply k R F c).symm }
  let β : RatFunc k →+* RatFunc (IsLocalRing.ResidueField R) := ρ.comp a
  have hα : α RatFunc.X = f := rationalGraphLocalParameterHom_X_value R f hker
  have hβ : β RatFunc.X = RatFunc.X := rationalGraphLocalParameterHom_X_residue R f hker
  refine ⟨α, hα, ?_⟩
  letI : Algebra (RatFunc k) A := a.toAlgebra
  letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc k) A F := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨β, hβ, ?_⟩
  letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toAlgebra
  let π : A →ₐ[RatFunc k] RatFunc (IsLocalRing.ResidueField R) :=
    { ρ with commutes' := fun _ => rfl }
  let zA : Option σ → A := fun j => rationalGraphLocalCoefficientHom R f hker (z j)
  let b : Option σ → RatFunc (IsLocalRing.ResidueField R) :=
    fun j => RatFunc.C (IsLocalRing.residue R (z j))
  have hvalues : (fun j => π (zA j)) = b := by
    funext j
    exact rationalGraphLocalResidueHom_original_coefficient R f hker (z j)
  have hb : b ≠ 0 := by
    intro he
    apply hres
    funext j
    apply RatFunc.C_injective
    exact (congrFun he j).trans (map_zero RatFunc.C).symm
  have hresA : (fun j => π (zA j)) ≠ 0 := by
    rw [hvalues]
    exact hb
  have hcoords (j : Option σ) : algebraMap A F (zA j) = s * j.elim 1 v := by
    change algebraMap R F (z j) = _
    exact hz j
  have hboundary := residue_field_point_mem_projective_closure π Subtype.val_injective v s zA hcoords hresA
  have heq := projectiveFieldPoint_eq_of_coordinate_eq (E := RatFunc k)
    (fun j => π (zA j)) b hresA hb hvalues
  rw [heq] at hboundary
  exact ⟨hb, hboundary⟩

end DimensionFourDependence
