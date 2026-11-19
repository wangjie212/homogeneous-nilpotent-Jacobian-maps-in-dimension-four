import DimensionFourDependence.RationalScalarVertexInfinity
import DimensionFourDependence.RationalGraphLocalParameter

/-! # The actual generic graph boundary retains an independent homogeneous scale -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R F : Type*} [Field k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra k R] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]

/-- Both generic parameters are kept: the original graph function is
the level variable over k, and the independent rational variable scales
all four original affine coordinates. Their common vertex remains at
infinity over the entire two-variable rational coefficient field. -/
theorem rational_graph_constructs_independently_scaled_generic_vertex_boundary
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
      ∃ γ : RatFunc (RatFunc k) →ₐ[RatFunc k] RatFunc F,
        γ RatFunc.X = RatFunc.X ∧
        letI : Algebra (RatFunc (RatFunc k)) (RatFunc F) := γ.toRingHom.toAlgebra
        fourthAxisAffineInfinityPoint (RatFunc (RatFunc k)) ∈
          projectiveClosureSet (L := RatFunc (RatFunc k))
            (fun i => RatFunc.X * RatFunc.C (v i)) := by
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
  have hα : α RatFunc.X = f := rationalGraphLocalParameterHom_X_value R f hker
  refine ⟨α, hα, ?_⟩
  letI : Algebra (RatFunc k) A := a.toAlgebra
  letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc k) A F := IsScalarTower.of_algebraMap_eq' rfl
  let β : RatFunc k →+* RatFunc (IsLocalRing.ResidueField R) := ρ.comp a
  letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toAlgebra
  let π : A →ₐ[RatFunc k] RatFunc (IsLocalRing.ResidueField R) :=
    { ρ with commutes' := fun _ => rfl }
  let ι : A →ₐ[RatFunc k] F := IsScalarTower.toAlgHom (RatFunc k) A F
  let zA : Option (Fin 4) → A := fun j => rationalGraphLocalCoefficientHom R f hker (z j)
  have hcoords (j : Option (Fin 4)) : ι (zA j) = s * j.elim 1 v := by
    change algebraMap R F (z j) = _
    exact hz j
  have hresA : (fun j => π (zA j)) =
      (fun j : Option (Fin 4) => j.elim 0
        (Fin.snoc (0 : Fin 3 → RatFunc (IsLocalRing.ResidueField R)) 1)) := by
    funext j
    change rationalGraphLocalResidueHom R f hker
      (rationalGraphLocalCoefficientHom R f hker (z j)) = _
    rw [rationalGraphLocalResidueHom_original_coefficient, congrFun hres j]
    cases j with
    | none => simp only [Option.elim_none, map_zero]
    | some i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Option.elim_some, Fin.snoc_last, map_one]
      · simp only [Option.elim_some, Fin.snoc_castSucc, Pi.zero_apply, map_zero]
  exact independent_rational_scale_retains_fixed_vertex_infinity ι Subtype.val_injective π
    v s zA hcoords hresA

end DimensionFourDependence
