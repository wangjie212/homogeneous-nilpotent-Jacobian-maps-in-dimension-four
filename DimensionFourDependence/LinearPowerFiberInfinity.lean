import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.SegreGlobalLinearRoot

/-! # A regular source linear power constant on a fiber vanishes at every fiber infinity point -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2500000

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Every equation of the actual homogeneous closure prime belongs
to each actual projective point of that closure. -/
theorem projectiveClosureSet_cone_relation_mem {n : ℕ}
    (x : Fin n → F)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) E))
    (hp : p ∈ projectiveClosureSet (L := E) x)
    (Q : MvPolynomial (Option (Fin n)) E) (hQ : Q ∈ projectiveConeIdeal (L := E) x) :
    Q ∈ p.asHomogeneousIdeal := by
  have hsubset : projectiveClosureSet (L := E) x ⊆
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin n)) E) {Q} := by
    apply closure_minimal _ (ProjectiveSpectrum.isClosed_zeroLocus _ {Q})
    apply Set.singleton_subset_iff.mpr
    exact Set.singleton_subset_iff.mpr hQ
  exact (hsubset hp) (by rfl)

/-- A source linear form whose positive power is constant on the
actual affine fiber vanishes at every actual projective infinity prime.
Its homogeneous leading equation and primality prove this directly,
without choosing a root in the geometric constants. -/
theorem linear_positive_power_constant_on_fiber_vanishes_at_infinity {n : ℕ}
    (x : Fin n → F) (a : Fin n → E) (c : E) (d : ℕ) (hd : 0 < d)
    (hpower : (aeval x (linearFormPolynomial a)) ^ d = algebraMap E F c)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) E))
    (hp : p ∈ projectiveClosureSet (L := E) x) (hinfty : X none ∈ p.asHomogeneousIdeal) :
    rename some (linearFormPolynomial a) ∈ p.asHomogeneousIdeal := by
  let L : MvPolynomial (Option (Fin n)) E := rename some (linearFormPolynomial a)
  let Q := L ^ d - C c * X none ^ d
  have hQhom : Q.IsHomogeneous d := by
    apply IsHomogeneous.sub
    · simpa only [one_mul] using (linearFormPolynomial_homogeneous a).rename_isHomogeneous.pow d
    · exact (MvPolynomial.isHomogeneous_X_pow none d).C_mul c
  have hQzero : aeval (fun j : Option (Fin n) => j.elim 1 x) Q = 0 := by
    simp only [Q, L, map_sub, map_mul, map_pow, aeval_rename, Function.comp_def,
      Option.elim_some, aeval_C, aeval_X, Option.elim_none, one_pow, mul_one, hpower, sub_self]
  have hQcone := (projectiveConeIdeal_mem_of_isHomogeneous x hQhom).mpr hQzero
  have hQmem := projectiveClosureSet_cone_relation_mem x p hp Q hQcone
  have hxpow : X none ^ d ∈ p.asHomogeneousIdeal.toIdeal :=
    p.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hinfty d hd
  have hconst : C c * X none ^ d ∈ p.asHomogeneousIdeal.toIdeal :=
    p.asHomogeneousIdeal.toIdeal.mul_mem_left (C c) hxpow
  have hLpow : L ^ d ∈ p.asHomogeneousIdeal.toIdeal := by
    have he := p.asHomogeneousIdeal.toIdeal.add_mem hQmem hconst
    simpa only [Q, sub_add_cancel] using he
  exact p.isPrime.mem_of_pow_mem d hLpow

variable {K : Type*} [Field K] [CharZero K] [Algebra K E]

/-- An actual polynomial identity ell^d=R(H) and the actual output
values imply the infinity vanishing of ell on the whole actual fiber. -/
theorem original_linear_power_output_identity_all_fiber_infinity_points
    (H : Fin 4 → MvPolynomial (Fin 4) K) (l a : Fin 4 → K)
    (d : ℕ) (hd : 0 < d) (hpower : linearFormPolynomial l ^ d = outputLinearCombination H a)
    (x : Fin 4 → F) (y : Fin 4 → E)
    [Algebra K F] [IsScalarTower K E F]
    (houtput : ∀ i, aeval x (H i) = algebraMap E F (y i))
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hp : p ∈ projectiveClosureSet (L := E) x) (hinfty : X none ∈ p.asHomogeneousIdeal) :
    rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ p.asHomogeneousIdeal := by
  have he := congrArg (aeval x) hpower
  have hval : (aeval x (linearFormPolynomial (fun i => algebraMap K E (l i)))) ^ d =
      algebraMap E F (dotProduct (fun i => algebraMap K E (a i)) y) := by
    simpa only [linearFormPolynomial, outputLinearCombination, dotProduct,
      map_pow, map_sum, map_mul, aeval_C, aeval_X, houtput,
      IsScalarTower.algebraMap_apply K E F] using he
  exact linear_positive_power_constant_on_fiber_vanishes_at_infinity x _ _ d hd hval p hp hinfty

end DimensionFourDependence
