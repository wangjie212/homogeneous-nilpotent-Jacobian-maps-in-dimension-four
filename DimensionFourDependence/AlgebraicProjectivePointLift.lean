import DimensionFourDependence.ProjectiveBoundaryCoefficientComponent
import DimensionFourDependence.ProjectivePointCoefficientRestriction
import Mathlib.RingTheory.Ideal.HasGoingUp

/-! # A specified projective boundary lifts along its chosen algebraic coefficient realization -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C A G σ : Type*} [Field C] [Field A] [Field G]
  [Algebra C A] [Algebra A G] [Algebra C G] [IsScalarTower C A G]

/-- The whole projective closure ideal contracts through the actual
coefficient tower to the original projective closure ideal. -/
theorem projectiveConeIdeal_coefficient_comap (v : σ → G) :
    (projectiveConeIdeal (L := A) v).comap (MvPolynomial.map (algebraMap C A)) =
      projectiveConeIdeal (L := C) v := by
  change ((projectiveFieldPointIdeal (E := A) (fun j : Option σ => j.elim 1 v)).toIdeal).comap
    (MvPolynomial.map (algebraMap C A)) =
      (projectiveFieldPointIdeal (E := C) (fun j : Option σ => j.elim 1 v)).toIdeal
  exact projectiveFieldPointIdeal_coefficient_comap _

/-- Passing to a homogeneous core retains an already homogeneous
contraction under a coefficient-field map. -/
theorem homogeneous_core_coefficient_comap_eq
    (P : HomogeneousIdeal (homogeneousSubmodule σ C)) (Q : Ideal (MvPolynomial σ A))
    (hQ : Q.comap (MvPolynomial.map (algebraMap C A)) = P.toIdeal) :
    (Q.homogeneousCore (homogeneousSubmodule σ A)).toIdeal.comap
      (MvPolynomial.map (algebraMap C A)) = P.toIdeal := by
  apply le_antisymm
  · exact (Ideal.comap_mono (Q.toIdeal_homogeneousCore_le _)).trans_eq hQ
  · intro f hf
    change MvPolynomial.map (algebraMap C A) f ∈ Q.homogeneousCore (homogeneousSubmodule σ A)
    rw [← sum_homogeneousComponent f, map_sum]
    apply (Q.homogeneousCore (homogeneousSubmodule σ A)).toIdeal.sum_mem
    intro n hn
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem (homogeneousSubmodule σ A)
        (MvPolynomial.map (algebraMap C A) (homogeneousComponent n f)) from
          ⟨n, (homogeneousComponent_isHomogeneous n f).map _⟩)
    change homogeneousComponent n f ∈ Q.comap (MvPolynomial.map (algebraMap C A))
    rw [hQ]
    have h := P.isHomogeneous n hf
    change (MvPolynomial.decomposition.decompose' f n : MvPolynomial σ C) ∈ P.toIdeal at h
    simpa only [MvPolynomial.decomposition.decompose'_apply] using h

/-- Every specified extension-valued point of the original closure
has a lift to the closure for the chosen algebraic coefficient extension.
The exact contracted prime of that same point is retained. No rationality
or unrelated boundary point is assumed. -/
theorem specified_projective_point_lifts_algebraic_coefficients
    [Algebra.IsAlgebraic C A] (v : σ → G)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option σ) C))
    (hp : p ∈ projectiveClosureSet (L := C) v) :
    ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A),
      q ∈ projectiveClosureSet (L := A) v ∧
        q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
          p.asHomogeneousIdeal.toIdeal := by
  let I := projectiveConeIdeal (L := A) v
  letI : I.IsPrime := projectiveConeIdeal_isPrime v
  letI : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  letI : Algebra.IsIntegral (MvPolynomial (Option σ) C) (MvPolynomial (Option σ) A) :=
    inferInstance
  have hIP : I.under (MvPolynomial (Option σ) C) ≤ p.asHomogeneousIdeal.toIdeal := by
    change I.comap (MvPolynomial.map (algebraMap C A)) ≤ _
    rw [projectiveConeIdeal_coefficient_comap]
    rw [projectiveClosureSet_eq_zeroLocus_cone] at hp
    exact hp
  obtain ⟨Q, hIQ, hQprime, hQcontract⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p.asHomogeneousIdeal.toIdeal I hIP
  let J := Q.homogeneousCore (homogeneousSubmodule (Option σ) A)
  have hJcontract : J.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
      p.asHomogeneousIdeal.toIdeal :=
    homogeneous_core_coefficient_comap_eq p.asHomogeneousIdeal Q hQcontract
  have hIJ : I ≤ J.toIdeal := by
    exact (Ideal.homogeneousCore.gc (𝒜 := homogeneousSubmodule (Option σ) A)
      (projectiveClosureHomogeneousIdeal (L := A) v) Q).mp hIQ
  obtain ⟨i, hi⟩ := projectiveSpectrum_exists_coordinate_not_mem p
  let q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A) :=
    { asHomogeneousIdeal := J
      isPrime := hQprime.homogeneousCore
      not_irrelevant_le := by
        intro h
        have hXi : X i ∈ J := h (HomogeneousIdeal.mem_irrelevant_of_mem _
          (show 0 < (1 : ℕ) by omega) (isHomogeneous_X (R := A) i))
        apply hi
        have hm : X i ∈ J.toIdeal.comap (MvPolynomial.map (algebraMap C A)) := by
          change MvPolynomial.map (algebraMap C A) (X i) ∈ J.toIdeal
          rw [MvPolynomial.map_X]
          exact hXi
        rwa [hJcontract] at hm }
  refine ⟨q, ?_, hJcontract⟩
  rw [projectiveClosureSet_eq_zeroLocus_cone]
  exact hIJ

end DimensionFourDependence
