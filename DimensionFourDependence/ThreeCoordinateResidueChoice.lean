import DimensionFourDependence.ThreeCoordinateMultiplicity

/-! # Either nonvanishing coordinate may supply the residue parameter -/

namespace DimensionFourDependence

variable {k B L : Type*} [Field k] [CharZero k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- The coordinate multiplicity bound does not prescribe which of the
two other original coordinates supplies the transcendental residue.
Exchanging them preserves both the original equation and its degree. -/
theorem three_coordinate_order_le_of_residue_alternative
    (u z v : B)
    (hres : Transcendental k (IsLocalRing.residue B u) ∨
      Transcendental k (IsLocalRing.residue B v))
    (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B)
    (hgen : IntermediateField.adjoin k
      {algebraMap B L u, algebraMap B L z, algebraMap B L v} = ⊤)
    (f : MvPolynomial (Option (Option Unit)) k) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval (fun i => i.elim (algebraMap B L v)
      (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L u))) f = 0)
    (a : ℕ) (horder : z ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ f.totalDegree := by
  classical
  rcases hres with hu | hv
  · exact three_coordinate_hypersurface_order_le_totalDegree
      u z v hu hz0 hz hgen f hf hroot a horder
  · let τ : Option (Option Unit) ≃ Option (Option Unit) :=
      Equiv.swap none (some (some ()))
    let f' := MvPolynomial.renameEquiv k τ f
    have hf' : f' ≠ 0 := by
      intro h
      apply hf
      apply (MvPolynomial.renameEquiv k τ).injective
      simpa only [map_zero] using h
    have hgen' : IntermediateField.adjoin k
        {algebraMap B L v, algebraMap B L z, algebraMap B L u} = ⊤ := by
      have heq : ({algebraMap B L v, algebraMap B L z, algebraMap B L u} : Set L) =
          {algebraMap B L u, algebraMap B L z, algebraMap B L v} := by
        ext t
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [heq]
    have hroot' : MvPolynomial.aeval (fun i => i.elim (algebraMap B L u)
        (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L v))) f' = 0 := by
      change MvPolynomial.aeval _ (MvPolynomial.rename τ f) = 0
      rw [MvPolynomial.aeval_rename]
      have heq : (fun i : Option (Option Unit) => (τ i).elim (algebraMap B L u)
          (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L v))) =
          (fun i => i.elim (algebraMap B L v)
            (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L u))) := by
        funext i
        cases i with
        | none => simp [τ]
        | some j =>
          cases j with
          | none => simp [τ, Equiv.swap_apply_def]
          | some j => cases j; simp [τ]
      change MvPolynomial.aeval (fun i => (τ i).elim (algebraMap B L u)
        (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L v))) f = 0
      rw [heq]
      exact hroot
    have h := three_coordinate_hypersurface_order_le_totalDegree
      v z u hv hz0 hz hgen' f' hf' hroot' a horder
    simpa only [f', MvPolynomial.totalDegree_renameEquiv] using h

end DimensionFourDependence
