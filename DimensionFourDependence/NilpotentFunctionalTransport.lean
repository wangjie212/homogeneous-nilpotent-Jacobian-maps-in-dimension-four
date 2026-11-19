import DimensionFourDependence.NilpotentFlag

/-! # The nilpotent functional obstruction in Lemma 4.3

An invariant lattice inherits nilpotence from its faithful realization in
the fraction vector space. A nonzero residue functional cannot satisfy
the parameter-preserving transport identity on that lattice.
-/

namespace DimensionFourDependence

section Lift

variable {R F M V : Type*} [CommRing R] [Field F]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] [Module F V]

/-- A linear lattice operator compatible with a nilpotent ambient
operator is itself nilpotent under a faithful lattice realization. -/
theorem linear_lift_isNilpotent_of_injective
    (A : Module.End F V) (T : Module.End R M) (i : M →ₗ[R] V)
    (hi : Function.Injective i) (hcompat : ∀ m, i (T m) = A (i m))
    (hA : IsNilpotent A) : IsNilpotent T := by
  have hpow : ∀ k : ℕ, ∀ m, i ((T ^ k) m) = (A ^ k) (i m) := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      calc
        _ = i (T ((T ^ k) m)) := by rw [pow_succ', Module.End.mul_apply]
        _ = A (i ((T ^ k) m)) := hcompat _
        _ = A ((A ^ k) (i m)) := congrArg A (ih m)
        _ = _ := by rw [pow_succ', Module.End.mul_apply]
  obtain ⟨k, hk⟩ := hA
  refine ⟨k, ?_⟩
  ext m
  apply hi
  simpa only [hk, LinearMap.zero_apply, map_zero] using hpow k m

end Lift

section Functional

variable {R κ M : Type*} [CommRing R] [Field κ] [Algebra R κ]
    [AddCommGroup M] [Module R M]

/-- The identity gamma*l(Tm)=l(m) forces a functional on a nilpotent
operator to be zero. No finite-dimensionality or quotient model is needed. -/
theorem nilpotent_functional_scaling_identity_forces_zero
    (T : Module.End R M) (hT : IsNilpotent T) (l : M →ₗ[R] κ) (γ : κ)
    (htransport : ∀ m, γ * l (T m) = l m) : l = 0 := by
  have hpow : ∀ k : ℕ, ∀ m, γ ^ k * l ((T ^ k) m) = l m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      calc
        _ = γ ^ k * (γ * l (T ((T ^ k) m))) := by
          rw [pow_succ' T k, Module.End.mul_apply, pow_succ γ k]
          ring
        _ = γ ^ k * l ((T ^ k) m) := by rw [htransport]
        _ = _ := ih m
  obtain ⟨k, hk⟩ := hT
  ext m
  have he := hpow k m
  rw [hk, LinearMap.zero_apply, map_zero, mul_zero] at he
  exact he.symm

end Functional

variable {R F κ M V : Type*} [CommRing R] [Field F] [Field κ] [Algebra R κ]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] [Module F V]

/-- The faithful fraction-space realization, lattice stability and
parameter differential identity give the local contradiction in Lemma 4.3.
No quotient dimension, eigenvalue or identification of a lattice quotient
is assumed. -/
theorem no_nilpotent_lattice_covector_transport
    (A : Module.End F V) (hA : IsNilpotent A) (T : Module.End R M)
    (i : M →ₗ[R] V) (hi : Function.Injective i) (hcompat : ∀ m, i (T m) = A (i m))
    (l : M →ₗ[R] κ) (hl : l ≠ 0) (γ : κ) (htransport : ∀ m, γ * l (T m) = l m) : False :=
  hl (nilpotent_functional_scaling_identity_forces_zero T
    (linear_lift_isNilpotent_of_injective A T i hi hcompat hA) l γ htransport)

end DimensionFourDependence
