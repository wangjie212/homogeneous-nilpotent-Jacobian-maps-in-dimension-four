import DimensionFourDependence.RationalScaleRelativeHilbert

/-! # An independently scaled source transfers its curve degree to the relative pencil constants -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] Algebra.toSMul

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {C S B F : Type u} [Field C] [Field S] [Field B] [Field F]
  [Algebra C S] [Algebra B F]

local notation "G₀" => RatFunc F
local notation "J₀" => IntermediateField.adjoin B {(RatFunc.X : G₀)}
local notation "D₀" => pencilCoefficientCurveField (E := B) (RatFunc.X : G₀)

/-- Algebraicity of the realized original coefficients constructs
their actual embedding in the relative closure of the scaled target field. -/
noncomputable def scaledSourceRelativeCoefficientHom
    (φ : S →+* G₀)
    (hcoeff : ∀ c : C, IsAlgebraic (J₀) (φ (algebraMap C S c))) : C →+* (D₀) :=
  { toFun := fun c => ⟨φ (algebraMap C S c), mem_algebraicClosure_iff.mpr (hcoeff c)⟩
    map_zero' := Subtype.ext (by
      change φ (algebraMap C S 0) = 0
      simp only [map_zero])
    map_one' := Subtype.ext (by
      change φ (algebraMap C S 1) = 1
      simp only [map_one])
    map_add' := fun c d => Subtype.ext (by
      change φ (algebraMap C S (c + d)) = φ (algebraMap C S c) + φ (algebraMap C S d)
      simp only [map_add])
    map_mul' := fun c d => Subtype.ext (by
      change φ (algebraMap C S (c * d)) = φ (algebraMap C S c) * φ (algebraMap C S d)
      simp only [map_mul]) }

/-- Its source value is the original specified coefficient value. -/
theorem scaledSourceRelativeCoefficientHom_source
    (φ : S →+* G₀)
    (hcoeff : ∀ c : C, IsAlgebraic (J₀) (φ (algebraMap C S c))) (c : C) :
    algebraMap (D₀) G₀ (scaledSourceRelativeCoefficientHom φ hcoeff c) =
      φ (algebraMap C S c) := rfl

/-- The actual independent-scale specialization and compatible
coefficient extension together bound the original-coordinate pencil
Hilbert function by that of the original source fiber. -/
theorem scaled_source_relative_constant_closure_hilbert_bound
    {σ : Type*} [Finite σ] (φ : S →+* G₀)
    (hcoeff : ∀ c : C, IsAlgebraic (J₀) (φ (algebraMap C S c)))
    (x : σ → S) (v : σ → F) (s : G₀) (hs : s ≠ 0)
    (hcoords : ∀ i, φ (x i) = s * RatFunc.C (v i)) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := algebraicClosure B F) v).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) x).toIdeal n := by
  let g := scaledSourceRelativeCoefficientHom φ hcoeff
  letI : Algebra C (D₀) := g.toAlgebra
  letI : Algebra C G₀ := (φ.comp (algebraMap C S)).toAlgebra
  letI : IsScalarTower C (D₀) G₀ := IsScalarTower.of_algebraMap_eq' rfl
  let f : S →ₐ[C] G₀ := { φ with commutes' := fun _ => rfl }
  have hsource := projectiveHilbertFunction_point_le_of_source_embedding (L := D₀) f x n
  have hvalues : f ∘ x = (fun i => s * RatFunc.C (v i)) := funext hcoords
  rw [hvalues, projectiveFieldPointIdeal_scale (fun i => RatFunc.C (v i)) s hs] at hsource
  exact (rational_scale_relative_constant_closure_hilbert_bound B F v n).trans hsource

/-- Every positive curve degree over the relative pencil constants
is bounded by the original source curve degree under this constructed
independent-scale realization. -/
theorem scaled_source_relative_constant_closure_curve_degree_bound
    {σ : Type*} [Finite σ] (φ : S →+* G₀)
    (hcoeff : ∀ c : C, IsAlgebraic (J₀) (φ (algebraMap C S c)))
    (x : σ → S) (v : σ → F) (s : G₀) (hs : s ≠ 0)
    (hcoords : ∀ i, φ (x i) = s * RatFunc.C (v i))
    {D D' : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) x).toIdeal D)
    (hD' : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := algebraicClosure B F) v).toIdeal D') :
    D' ≤ D :=
  curveHilbertDegree_le_of_hilbertFunction_le _ _
    (fun n => scaled_source_relative_constant_closure_hilbert_bound φ hcoeff x v s hs hcoords n) hD hD'

end DimensionFourDependence
