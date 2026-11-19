import DimensionFourDependence.RationalScalarBoundaryCoefficients
import DimensionFourDependence.RationalGraphLocalParameter

/-! # An arbitrary original generic graph boundary retains both free parameters -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R F σ : Type*} [Field k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra k R] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]

/-- Both field embeddings retain their coefficient actions. The
boundary keeps the actual residue of every original coordinate;
no direction or value of either free parameter is prescribed. -/
theorem rational_graph_constructs_independently_scaled_generic_projective_boundary
    (f : F)
    (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))
    (v : σ → F) (s : F) (z : Option σ → R)
    (hz : ∀ j, algebraMap R F (z j) = s * j.elim 1 v)
    (hres : (fun j => IsLocalRing.residue R (z j)) ≠ 0) :
    ∃ α : RatFunc k →ₐ[k] F, α RatFunc.X = f ∧
      letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
      ∃ β : RatFunc k →ₐ[k] RatFunc (IsLocalRing.ResidueField R),
        β RatFunc.X = RatFunc.X ∧
        letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toRingHom.toAlgebra
        ∃ γ : RatFunc (RatFunc k) →ₐ[RatFunc k] RatFunc F,
          γ RatFunc.X = RatFunc.X ∧
          letI : Algebra (RatFunc (RatFunc k)) (RatFunc F) := γ.toRingHom.toAlgebra
          ∃ δ : RatFunc (RatFunc k) →ₐ[RatFunc k] RatFunc (RatFunc (IsLocalRing.ResidueField R)),
            δ RatFunc.X = RatFunc.X ∧
            letI : Algebra (RatFunc (RatFunc k)) (RatFunc (RatFunc (IsLocalRing.ResidueField R))) :=
              δ.toRingHom.toAlgebra
            ∃ hb : rationalScalarProjectiveVector
                (fun j => RatFunc.C (IsLocalRing.residue R (z j))) ≠ 0,
              projectiveFieldPoint (E := RatFunc (RatFunc k))
                (rationalScalarProjectiveVector (fun j => RatFunc.C (IsLocalRing.residue R (z j)))) hb ∈
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

  letI : Algebra (RatFunc k) A := a.toAlgebra
  letI : Algebra (RatFunc k) F := α.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc k) A F := IsScalarTower.of_algebraMap_eq' rfl
  let β : RatFunc k →ₐ[k] RatFunc (IsLocalRing.ResidueField R) :=
    { ρ.comp a with
      commutes' := fun c => by
        change ρ (a (RatFunc.C c)) = algebraMap k (RatFunc (IsLocalRing.ResidueField R)) c
        rw [rationalGraphLocalParameterHom_C]
        rw [rationalGraphLocalResidueHom_original_coefficient]
        rfl }
  have hβ : β RatFunc.X = RatFunc.X := rationalGraphLocalParameterHom_X_residue R f hker
  refine ⟨α, hα, β, hβ, ?_⟩
  letI : Algebra (RatFunc k) (RatFunc (IsLocalRing.ResidueField R)) := β.toRingHom.toAlgebra
  let π : A →ₐ[RatFunc k] RatFunc (IsLocalRing.ResidueField R) :=
    { ρ with commutes' := fun _ => rfl }
  let ι : A →ₐ[RatFunc k] F := IsScalarTower.toAlgHom (RatFunc k) A F
  let zA : Option σ → A := fun j => rationalGraphLocalCoefficientHom R f hker (z j)
  have hcoords (j : Option σ) : ι (zA j) = s * j.elim 1 v := by
    change algebraMap R F (z j) = _
    exact hz j
  have hvalues : (fun j => π (zA j)) =
      (fun j => RatFunc.C (IsLocalRing.residue R (z j))) := by
    funext j
    exact rationalGraphLocalResidueHom_original_coefficient R f hker (z j)
  have hresA : (fun j => π (zA j)) ≠ 0 := by
    rw [hvalues]
    intro he
    apply hres
    funext j
    apply RatFunc.C_injective
    exact (congrFun he j).trans (map_zero RatFunc.C).symm
  obtain ⟨γ, hγ, δ, hδ, hb, hboundary⟩ :=
    independent_rational_scale_preserves_coefficient_compatible_projective_boundary
      ι Subtype.val_injective π v s zA hcoords hresA
  refine ⟨γ, hγ, δ, hδ, ?_⟩
  letI : Algebra (RatFunc (RatFunc k)) (RatFunc F) := γ.toRingHom.toAlgebra
  letI : Algebra (RatFunc (RatFunc k)) (RatFunc (RatFunc (IsLocalRing.ResidueField R))) :=
    δ.toRingHom.toAlgebra
  simpa only [hvalues] using (⟨hb, hboundary⟩ : ∃ hb, _)

/-- At infinity the independent affine scale multiplies every
nonzero projective coordinate by one common unit, so it preserves
the original projective direction itself. -/
theorem rationalScalarProjectiveFieldPoint_eq_at_infinity
    {Q κ τ : Type*} [Field Q] [Field κ] [Algebra Q (RatFunc κ)]
    (z : Option τ → κ) (hzero : z none = 0) (hz : z ≠ 0)
    (hb : (fun j => RatFunc.C (z j)) ≠ 0) :
    projectiveFieldPoint (E := Q) (rationalScalarProjectiveVector z)
        (rationalScalarProjectiveVector_ne_zero z hz) =
      projectiveFieldPoint (E := Q) (fun j => RatFunc.C (z j)) hb := by
  apply projectiveFieldPoint_eq_of_proportional _ _ _ _ RatFunc.X RatFunc.X_ne_zero
  intro j
  cases j with
  | none => simp only [rationalScalarProjectiveVector, Option.elim_none, hzero, map_zero, mul_zero]
  | some i => rfl

end DimensionFourDependence
