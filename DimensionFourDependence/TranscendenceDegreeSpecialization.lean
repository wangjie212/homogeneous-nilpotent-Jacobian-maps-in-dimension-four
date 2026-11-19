import DimensionFourDependence.Defs

/-! # Dimension drop under a proper algebraic specialization

A homomorphism of a domain algebraic over a subalgebra is injective as
soon as its restriction to that subalgebra is injective. Lifting a
transcendence basis through a surjection then shows that a proper prime
quotient strictly lowers finite transcendence degree. This is the
dimension comparison needed for the line-pair incidence argument.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K A B : Type*} [Field K] [CommRing A] [IsDomain A] [CommRing B]
variable [Algebra K A] [Algebra K B]

/-- Algebraicity makes injectivity on a coefficient subalgebra sufficient
for injectivity on the whole domain. -/
theorem algHom_injective_of_algebraic_subalgebra
    (S : Subalgebra K A) (g : A →ₐ[K] B) (halg : Algebra.IsAlgebraic S A)
    (hS : Function.Injective (g.comp S.val)) : Function.Injective g := by
  apply (injective_iff_map_eq_zero g).mpr
  intro a ha
  by_contra ha0
  obtain ⟨r, hr, b, hb⟩ := (halg.isAlgebraic a).exists_nonzero_dvd
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha0)
  apply hr
  apply hS
  change g (algebraMap S A r) = g (algebraMap S A 0)
  rw [hb, map_mul, ha, zero_mul, map_zero, map_zero]

universe u

variable {K' A' B' : Type u} [Field K'] [CommRing A'] [IsDomain A']
variable [CommRing B'] [IsDomain B'] [Algebra K' A'] [Algebra K' B']

/-- A surjection of domains with the same finite transcendence degree
is injective. The basis and the injective coefficient subalgebra are
constructed from the surjection itself. -/
theorem surjective_algHom_injective_of_trdeg_eq
    (g : A' →ₐ[K'] B') (hgs : Function.Surjective g)
    (hfin : Algebra.trdeg K' A' < Cardinal.aleph0)
    (heq : Algebra.trdeg K' A' = Algebra.trdeg K' B') : Function.Injective g := by
  classical
  obtain ⟨ι, y, hy⟩ := exists_isTranscendenceBasis' K' B'
  let x : ι → A' := fun i => Classical.choose (hgs (y i))
  have hxy : g ∘ x = y := funext (fun i => Classical.choose_spec (hgs (y i)))
  have hx : AlgebraicIndependent K' x := by
    apply AlgebraicIndependent.of_comp g
    rw [hxy]
    exact hy.1
  have hxb : IsTranscendenceBasis K' x :=
    hx.isTranscendenceBasis_of_trdeg_le hfin (heq.trans hy.cardinalMk_eq_trdeg.symm).le
  let S := Algebra.adjoin K' (Set.range x)
  apply algHom_injective_of_algebraic_subalgebra S g hxb.isAlgebraic
  have hmap (p : MvPolynomial ι K') :
      g (algebraMap S A' (hx.aevalEquiv p)) = aeval y p := by
    rw [hx.algebraMap_aevalEquiv, comp_aeval_apply]
    exact congrArg (fun z : ι → B' => aeval z p) hxy
  intro a b hab
  obtain ⟨p, rfl⟩ := hx.aevalEquiv.surjective a
  obtain ⟨q, rfl⟩ := hx.aevalEquiv.surjective b
  apply congrArg hx.aevalEquiv
  apply hy.1
  exact (hmap p).symm.trans (hab.trans (hmap q))

/-- Every proper prime specialization of a domain strictly lowers its
finite transcendence degree over the original coefficient field. -/
theorem prime_quotient_trdeg_lt
    (P : Ideal A') [P.IsPrime] (hP : P ≠ ⊥)
    (hfin : Algebra.trdeg K' A' < Cardinal.aleph0) :
    Algebra.trdeg K' (A' ⧸ P) < Algebra.trdeg K' A' := by
  let g : A' →ₐ[K'] (A' ⧸ P) := Ideal.Quotient.mkₐ K' P
  have hle := trdeg_le_of_surjective g Ideal.Quotient.mk_surjective
  apply lt_of_le_of_ne hle
  intro he
  have hg := surjective_algHom_injective_of_trdeg_eq g Ideal.Quotient.mk_surjective hfin he.symm
  apply hP
  apply le_antisymm _ bot_le
  intro a ha
  apply Ideal.mem_bot.mpr
  apply hg
  exact (Ideal.Quotient.eq_zero_iff_mem.mpr ha).trans (map_zero g).symm

end DimensionFourDependence
