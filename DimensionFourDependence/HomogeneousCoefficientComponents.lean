import DimensionFourDependence.FiberComponentContraction
import DimensionFourDependence.ProjectiveComponents
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! # Components after coefficient extension retain the original homogeneous grading -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C A σ : Type*} [Field C] [Field A] [Algebra C A]

/-- Every minimal component of an extended homogeneous original ideal
is homogeneous. Its prime homogeneous core contains every original
generator, so minimality makes the core equal to the whole prime. -/
theorem minimal_coefficient_component_isHomogeneous
    (I : Ideal (MvPolynomial σ C))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ C))
    (Q : Ideal (MvPolynomial σ A))
    (hQ : Q ∈ (extendCoefficientIdeal A I).minimalPrimes) :
    Q.IsHomogeneous (homogeneousSubmodule σ A) := by
  let J := Q.homogeneousCore (homogeneousSubmodule σ A)
  have hJprime : J.toIdeal.IsPrime := hQ.isPrime.homogeneousCore
  have hJle : J.toIdeal ≤ Q := Q.toIdeal_homogeneousCore_le _
  have hmap : extendCoefficientIdeal A I ≤ J.toIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change MvPolynomial.map (algebraMap C A) P ∈ J.toIdeal
    rw [← sum_homogeneousComponent P, map_sum]
    apply J.toIdeal.sum_mem
    intro i hi
    have hPi : homogeneousComponent i P ∈ I := by
      have h := hI i hP
      change (MvPolynomial.decomposition.decompose' P i : MvPolynomial σ C) ∈ I at h
      simpa only [MvPolynomial.decomposition.decompose'_apply] using h
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem (homogeneousSubmodule σ A)
        (MvPolynomial.map (algebraMap C A) (homogeneousComponent i P)) from
          ⟨i, (homogeneousComponent_isHomogeneous i P).map _⟩)
    exact hQ.le (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap C A)) hPi)
  have he : Q = J.toIdeal := le_antisymm (hQ.2 ⟨hJprime, hmap⟩ hJle) hJle
  rw [he]
  exact J.isHomogeneous

end DimensionFourDependence
