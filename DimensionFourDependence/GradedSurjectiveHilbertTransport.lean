import DimensionFourDependence.ProjectiveHilbert

/-! # Actual Hilbert quotients under a surjective graded coordinate map

If the coordinate map is onto in each homogeneous degree and its
kernel is already among the original equations, its actual quotient
pieces are isomorphic to those of the image ideal. This covers graph
hyperplane elimination and the invertible linear infinity chart without
assuming a geometric degree-preservation principle.
-/

namespace DimensionFourDependence

open MvPolynomial Module

section Linear

variable {F M N : Type*} [Field F] [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]

/-- A surjective linear map whose relation preimage is exactly the
source relations identifies the actual quotient dimensions. -/
theorem quotient_finrank_eq_of_surjective_relation_comap
    (f : M →ₗ[F] N) (hf : Function.Surjective f) (U : Submodule F M) (V : Submodule F N)
    (hUV : V.comap f = U) : finrank F (M ⧸ U) = finrank F (N ⧸ V) := by
  let fQ : (M ⧸ U) →ₗ[F] (N ⧸ V) := U.mapQ V f (by rw [hUV])
  have hinj : Function.Injective fQ := by
    intro a b hab
    obtain ⟨p, rfl⟩ := U.mkQ_surjective a
    obtain ⟨q, rfl⟩ := U.mkQ_surjective b
    apply (Submodule.Quotient.eq U).mpr
    rw [← hUV]
    change f (p - q) ∈ V
    rw [map_sub]
    exact (Submodule.Quotient.eq V).mp hab
  have hsurj : Function.Surjective fQ := by
    intro a
    obtain ⟨q, rfl⟩ := V.mkQ_surjective a
    obtain ⟨p, hp⟩ := hf q
    exact ⟨U.mkQ p, congrArg V.mkQ hp⟩
  exact (LinearEquiv.ofBijective fQ ⟨hinj, hsurj⟩).finrank_eq

end Linear

variable {F sigma tau : Type*} [Field F]

/-- The actual homogeneous piece map of a degree-preserving
polynomial coefficient-algebra homomorphism. -/
noncomputable def homogeneousPolynomialAlgebraMap
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d) (d : ℕ) :
    homogeneousSubmodule sigma F d →ₗ[F] homogeneousSubmodule tau F d where
  toFun P := ⟨phi (P : MvPolynomial sigma F), hphi d P P.property⟩
  map_add' P Q := Subtype.ext (phi.map_add P Q)
  map_smul' a P := Subtype.ext (phi.toLinearMap.map_smul a P)

/-- The original homogeneous relations are precisely the preimage
of the image ideal's relations when the full coordinate kernel is already included. -/
theorem homogeneousPolynomialAlgebraMap_relation_comap
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hsurj : Function.Surjective phi) (I : Ideal (MvPolynomial sigma F))
    (hker : RingHom.ker phi.toRingHom ≤ I) (d : ℕ) :
    (homogeneousRelationSpace (I.map phi.toRingHom) d).comap (homogeneousPolynomialAlgebraMap phi hphi d) =
      homogeneousRelationSpace I d := by
  ext P
  change phi (P : MvPolynomial sigma F) ∈ I.map phi.toRingHom ↔ (P : MvPolynomial sigma F) ∈ I
  constructor
  · intro hP
    obtain ⟨Q, hQI, hQ⟩ := (Ideal.mem_map_iff_of_surjective phi.toRingHom hsurj).mp hP
    have hdiff : (P : MvPolynomial sigma F) - Q ∈ I := by
      apply hker
      change phi ((P : MvPolynomial sigma F) - Q) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hQ.symm
    simpa only [sub_add_cancel] using I.add_mem hdiff hQI
  · exact Ideal.mem_map_of_mem phi.toRingHom

/-- A graded coordinate map onto each actual homogeneous piece
preserves the actual Hilbert function after eliminating its included kernel. -/
theorem projectiveHilbertFunction_surjective_graded_map
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hsurj : Function.Surjective phi)
    (hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (I : Ideal (MvPolynomial sigma F)) (hker : RingHom.ker phi.toRingHom ≤ I) (d : ℕ) :
    projectiveHilbertFunction I d = projectiveHilbertFunction (I.map phi.toRingHom) d :=
  quotient_finrank_eq_of_surjective_relation_comap (homogeneousPolynomialAlgebraMap phi hphi d)
    (hpieces d) (homogeneousRelationSpace I d) (homogeneousRelationSpace (I.map phi.toRingHom) d)
    (homogeneousPolynomialAlgebraMap_relation_comap phi hphi hsurj I hker d)

end DimensionFourDependence
