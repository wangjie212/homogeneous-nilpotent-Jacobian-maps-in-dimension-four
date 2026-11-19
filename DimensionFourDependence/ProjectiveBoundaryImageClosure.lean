import DimensionFourDependence.ProjectivePrimeCoordinates
import DimensionFourDependence.HomogeneousCoefficientComponents
import DimensionFourDependence.HyperplaneSectionHilbertDegree
import DimensionFourDependence.ProjectivePrimeBaseExtension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # The closed image of the actual projective boundary -/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w
set_option maxHeartbeats 3800000

variable {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F] {σ : Type v} [Finite σ]

private theorem projectiveFieldPointMap_coefficients_composed
    {E : Type w} [Field E] [Algebra L E] (z : σ → E) (P : MvPolynomial σ K) :
    letI := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
    projectiveFieldPointMap (E := L) z (MvPolynomial.map (algebraMap K L) P) =
      projectiveFieldPointMap (E := K) z P := by
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  exact projectiveFieldPointMap_coefficient_extension z P

/-- The actual projective infinity section of the affine point's closure. -/
abbrev AffineClosureBoundary (x : σ → F) :=
  {p : ProjectiveSpectrum (homogeneousSubmodule (Option σ) L) //
    projectiveConeIdeal (L := L) x ⊔ Ideal.span {X none} ≤ p.asHomogeneousIdeal.toIdeal}

/-- The original-field projective source direction of a boundary point,
using its own canonical coordinate field and omitting the zero affine frame. -/
noncomputable def affineBoundarySourceDirection (x : σ → F) (p : AffineClosureBoundary (L := L) x) :
    ProjectiveSpectrum (homogeneousSubmodule σ K) := by
  let E := FractionRing (MvPolynomial (Option σ) L ⧸ p.val.asHomogeneousIdeal.toIdeal)
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  let z := projectivePrimeCoordinate p.val
  have hm : X none ∈ projectiveConeIdeal (L := L) x ⊔ Ideal.span {X none} :=
    (show Ideal.span {X none} ≤ projectiveConeIdeal (L := L) x ⊔ Ideal.span {X none} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hz₀ : z none = 0 := (projectivePrimeCoordinate_eq_zero_iff p.val none).mpr
    (p.property hm)
  have hz : z ∘ some ≠ 0 := by
    intro h
    apply projectivePrimeCoordinate_ne_zero p.val
    funext i
    cases i with
    | none => exact hz₀
    | some i => exact congrFun h i
  exact projectiveFieldPoint (E := K) (z ∘ some) hz

theorem affineBoundarySourceDirection_mem_iff (x : σ → F) (p : AffineClosureBoundary (L := L) x)
    (P : MvPolynomial σ K) :
    P ∈ (affineBoundarySourceDirection (K := K) x p).asHomogeneousIdeal ↔
      rename some (MvPolynomial.map (algebraMap K L) P) ∈ p.val.asHomogeneousIdeal := by
  let E := FractionRing (MvPolynomial (Option σ) L ⧸ p.val.asHomogeneousIdeal.toIdeal)
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  let z := projectivePrimeCoordinate p.val
  have h : projectiveFieldPointMap (E := L) z (rename some (MvPolynomial.map (algebraMap K L) P)) =
      projectiveFieldPointMap (E := K) (z ∘ some) P := by
    rw [projectiveFieldPointMap_coordinate_projection]
    exact projectiveFieldPointMap_coefficients_composed (L := L) (z ∘ some) P
  change projectiveFieldPointMap (E := K) (z ∘ some) P = 0 ↔ _
  rw [← h]
  exact Iff.of_eq (congrArg (fun q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) L) =>
    rename some (MvPolynomial.map (algebraMap K L) P) ∈ q.asHomogeneousIdeal)
    (projectivePrimeCoordinate_represents p.val))

theorem affineBoundarySourceDirection_specializes (x : σ → F) (p q : AffineClosureBoundary (L := L) x)
    (hle : p.val.asHomogeneousIdeal.toIdeal ≤ q.val.asHomogeneousIdeal.toIdeal) :
    affineBoundarySourceDirection (K := K) x q ∈ closure {affineBoundarySourceDirection (K := K) x p} := by
  apply (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp
  intro P hP
  exact (affineBoundarySourceDirection_mem_iff x q P).mpr (hle ((affineBoundarySourceDirection_mem_iff x p P).mp hP))

/-- The image closure is the finite union of the closures of the images
of the genuine relevant minimal primes of the infinity section. -/
theorem affine_boundary_source_image_closure_finite_generators (x : σ → F) :
    let proj := affineBoundarySourceDirection (K := K) (L := L) x
    ∃ T : Set (AffineClosureBoundary (L := L) x), T.Finite ∧
      closure (Set.range proj) = ⋃ p ∈ T, closure {proj p} := by
  let proj := affineBoundarySourceDirection (K := K) (L := L) x
  let I := projectiveConeIdeal (L := L) x
  let J := I ⊔ Ideal.span ({X none} : Set (MvPolynomial (Option σ) L))
  let T : Set (AffineClosureBoundary (L := L) x) := fun p => p.val.asHomogeneousIdeal.toIdeal ∈ J.minimalPrimes
  have hT : T.Finite := by
    apply (J.finite_minimalPrimes_of_isNoetherianRing).preimage
    intro p _ q _ h
    exact Subtype.ext (ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective h))
  let : Finite T := hT.to_subtype
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Option σ) L) :=
    sup_coordinate_isHomogeneous I (projectiveConeIdeal_isHomogeneous x) none
  have hhom (Q : Ideal (MvPolynomial (Option σ) L)) (hQ : Q ∈ J.minimalPrimes) :
      Q.IsHomogeneous (homogeneousSubmodule (Option σ) L) := by
    apply minimal_coefficient_component_isHomogeneous J hJ Q
    have he : extendCoefficientIdeal L J = J := by
      have hm : (MvPolynomial.map (RingHom.id L) : MvPolynomial (Option σ) L →+* _) = RingHom.id _ :=
        RingHom.ext MvPolynomial.map_id
      rw [extendCoefficientIdeal, Algebra.algebraMap_self, hm, Ideal.map_id]
    rwa [he]
  have hcover (p : AffineClosureBoundary (L := L) x) :
      ∃ q : T, proj p ∈ closure {proj q.val} := by
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le p.property
    let q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) L) :=
      ⟨⟨Q, hhom Q hQ⟩, hQ.isPrime, fun h => p.val.not_irrelevant_le (h.trans hQP)⟩
    exact ⟨⟨⟨q, hQ.le⟩, hQ⟩, affineBoundarySourceDirection_specializes x _ p hQP⟩
  refine ⟨T, hT, ?_⟩
  rw [Set.biUnion_eq_iUnion]
  apply le_antisymm
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun _ => isClosed_closure)
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hcover p
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  · apply Set.iUnion_subset
    intro q
    exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self q.val))

/-- If every actual boundary direction lies on a fixed irreducible
projective closure and excludes its generic point, the actual boundary
image closure is a proper closed subset of that closure. -/
theorem affine_boundary_source_image_closure_is_proper
    (x : σ → F) (s : ProjectiveSpectrum (homogeneousSubmodule σ K))
    (hsub : ∀ b : AffineClosureBoundary (L := L) x, affineBoundarySourceDirection x b ∈ closure {s})
    (hne : ∀ b : AffineClosureBoundary (L := L) x, affineBoundarySourceDirection x b ≠ s) :
    closure (Set.range (affineBoundarySourceDirection (L := L) x)) ⊂ closure {s} := by
  have hle : closure (Set.range (affineBoundarySourceDirection (L := L) x)) ⊆ closure {s} :=
    closure_minimal (by rintro _ ⟨p, rfl⟩; exact hsub p) isClosed_closure
  refine ⟨hle, ?_⟩
  obtain ⟨T, _, hT⟩ := affine_boundary_source_image_closure_finite_generators (K := K) (L := L) x
  intro h
  have hs : s ∈ closure {s} := subset_closure (by simp)
  have hd := h hs
  rw [hT] at hd
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hd
  obtain ⟨_, hb'⟩ := Set.mem_iUnion.mp hb
  exact hne b (le_antisymm ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).mpr hb')
    ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).mpr (hsub b)))

end DimensionFourDependence
