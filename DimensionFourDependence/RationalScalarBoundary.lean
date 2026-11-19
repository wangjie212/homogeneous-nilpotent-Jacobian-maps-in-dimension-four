import DimensionFourDependence.RationalScalarLocalization

/-! # Independent rational scaling preserves an actual residue boundary -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {κ σ : Type*} [Field κ]

/-- The homogenizing coordinate stays fixed while the original affine
source coordinates acquire the same independent rational scale. -/
noncomputable def rationalScalarProjectiveVector (z : Option σ → κ) : Option σ → RatFunc κ :=
  fun j => j.elim (RatFunc.C (z none)) (fun i => RatFunc.X * RatFunc.C (z (some i)))

/-- Free rational scaling cannot annihilate a nonzero projective vector. -/
theorem rationalScalarProjectiveVector_ne_zero (z : Option σ → κ) (hz : z ≠ 0) :
    rationalScalarProjectiveVector z ≠ 0 := by
  intro he
  apply hz
  funext j
  apply RatFunc.C_injective
  cases j with
  | none => exact (congrFun he none).trans (map_zero RatFunc.C).symm
  | some i =>
    have hi : RatFunc.X * RatFunc.C (z (some i)) = 0 := congrFun he (some i)
    exact ((mul_eq_zero.mp hi).resolve_left RatFunc.X_ne_zero).trans (map_zero RatFunc.C).symm

variable {L A F : Type*} [Field L] [CommRing A] [Field F]
  [Algebra L A] [Algebra L F] [Algebra L κ]

/-- Adjoining an independent homogeneous scale preserves the boundary
of the original affine source solution. The local coefficient inclusion
and specialization are retained and both rational scalar embeddings are
constructed, each sending the new variable to the free rational variable. -/
theorem independent_rational_scale_preserves_residue_projective_boundary
    (ι : A →ₐ[L] F) (hι : Function.Injective ι) (π : A →ₐ[L] κ)
    (v : σ → F) (s : F) (z : Option σ → A)
    (hz : ∀ j, ι (z j) = s * j.elim 1 v)
    (hres : (fun j => π (z j)) ≠ 0) :
    ∃ α : RatFunc L →ₐ[L] RatFunc F, α RatFunc.X = RatFunc.X ∧
      letI : Algebra (RatFunc L) (RatFunc F) := α.toRingHom.toAlgebra
      ∃ β : RatFunc L →+* RatFunc κ, β RatFunc.X = RatFunc.X ∧
        letI : Algebra (RatFunc L) (RatFunc κ) := β.toAlgebra
        ∃ hb : rationalScalarProjectiveVector (fun j => π (z j)) ≠ 0,
          projectiveFieldPoint (E := RatFunc L)
            (rationalScalarProjectiveVector (fun j => π (z j))) hb ∈
              projectiveClosureSet (L := RatFunc L) (fun i => RatFunc.X * RatFunc.C (v i)) := by
  let O := rationalScalarLocalization L A
  let a := rationalScalarParameterHom L A
  let iF := rationalScalarSpecialization L A ι
  let iκ := rationalScalarSpecialization L A π
  let α : RatFunc L →ₐ[L] RatFunc F :=
    { iF.comp a with
      commutes' := fun c => by
        change iF (a (RatFunc.C c)) = algebraMap L (RatFunc F) c
        rw [rationalScalarParameterHom_C, rationalScalarSpecialization_coefficient]
        rw [IsScalarTower.algebraMap_apply L F (RatFunc F)]
        exact congrArg RatFunc.C (ι.commutes c) }
  let β : RatFunc L →+* RatFunc κ := iκ.comp a
  have hα : α RatFunc.X = RatFunc.X := by
    change iF (a RatFunc.X) = _
    rw [rationalScalarParameterHom_X, rationalScalarSpecialization_variable]
  have hβ : β RatFunc.X = RatFunc.X := by
    change iκ (a RatFunc.X) = _
    rw [rationalScalarParameterHom_X, rationalScalarSpecialization_variable]
  refine ⟨α, hα, ?_⟩
  letI : Algebra (RatFunc L) O := a.toAlgebra
  letI : Algebra O (RatFunc F) := iF.toAlgebra
  letI : Algebra (RatFunc L) (RatFunc F) := α.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc L) O (RatFunc F) := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨β, hβ, ?_⟩
  letI : Algebra (RatFunc L) (RatFunc κ) := β.toAlgebra
  let ψ : O →ₐ[RatFunc L] RatFunc κ := { iκ with commutes' := fun _ => rfl }
  let t : O := algebraMap (Polynomial A) O Polynomial.X
  let zO : Option σ → O := fun j => j.elim (rationalScalarCoefficientHom L A (z none))
    (fun i => t * rationalScalarCoefficientHom L A (z (some i)))
  let b := rationalScalarProjectiveVector (fun j => π (z j))
  have hvalues : (fun j => ψ (zO j)) = b := by
    funext j
    cases j with
    | none => exact rationalScalarSpecialization_coefficient L A π (z none)
    | some i =>
      change iκ (t * rationalScalarCoefficientHom L A (z (some i))) =
        RatFunc.X * RatFunc.C (π (z (some i)))
      rw [map_mul]
      exact congrArg₂ (· * ·) (rationalScalarSpecialization_variable L A π)
        (rationalScalarSpecialization_coefficient L A π (z (some i)))
  have hb : b ≠ 0 := rationalScalarProjectiveVector_ne_zero _ hres
  have hresO : (fun j => ψ (zO j)) ≠ 0 := by rwa [hvalues]
  have hcoords (j : Option σ) : algebraMap O (RatFunc F) (zO j) =
      RatFunc.C s * j.elim 1 (fun i => RatFunc.X * RatFunc.C (v i)) := by
    change iF (zO j) = _
    cases j with
    | none =>
      simp only [iF, zO, Option.elim_none, rationalScalarSpecialization_coefficient]
      rw [hz none]
      simp only [Option.elim_none, mul_one]
    | some i =>
      simp only [iF, zO, t, Option.elim_some, map_mul]
      rw [rationalScalarSpecialization_coefficient, rationalScalarSpecialization_variable]
      rw [hz (some i)]
      simp only [Option.elim_some, map_mul]
      ring
  have hinj : Function.Injective (algebraMap O (RatFunc F)) :=
    rationalScalarSpecialization_injective L A ι hι
  have hboundary := residue_field_point_mem_projective_closure ψ hinj
    (fun i => RatFunc.X * RatFunc.C (v i)) (RatFunc.C s) zO hcoords hresO
  have hp := projectiveFieldPoint_eq_of_coordinate_eq (E := RatFunc L)
    (fun j => ψ (zO j)) b hresO hb hvalues
  rw [hp] at hboundary
  exact ⟨hb, hboundary⟩

end DimensionFourDependence
