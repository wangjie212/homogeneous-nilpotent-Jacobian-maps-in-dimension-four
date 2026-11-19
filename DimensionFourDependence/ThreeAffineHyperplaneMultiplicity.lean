import DimensionFourDependence.NormalizedAffineLinearMultiplicity

/-! # Every nonzero affine hyperplane has the hypersurface multiplicity bound

A hyperplane vanishing at a prime cannot be a nonzero constant. Its
nonzero variable coefficient supplies a pivot, which is moved to the
distinguished coordinate by a constructed permutation. Thus no pivot or
projection choice remains an assumption in the final affine statement.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

/-- A specified original coordinate is moved to the distinguished pivot. -/
noncomputable def affineThreePivotOrder (j : Fin 3) : Fin 3 ≃ Option (Option Unit) := by
  let r : Fin 3 ≃ Option (Option Unit) := Fintype.equivOfCardEq (by decide)
  exact r.trans (Equiv.swap (r j) (some none))

theorem affineThreePivotOrder_pivot (j : Fin 3) :
    affineThreePivotOrder j j = some none := by
  simp [affineThreePivotOrder]

theorem affineThreePivotOrder_symm_pivot (j : Fin 3) :
    (affineThreePivotOrder j).symm (some none) = j := by
  simpa only [Equiv.symm_apply_apply] using
    (congrArg (affineThreePivotOrder j).symm (affineThreePivotOrder_pivot j)).symm

section LinearForm

variable {k A σ : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype σ] [DecidableEq σ]

/-- The pivot normal form is exactly the whole given affine linear
combination, with its original coefficients and original coordinates. -/
theorem affinePivotCoordinate_pivot_eq_linearForm
    (x : σ → A) (j : σ) (b : k) (c : σ → k) :
    affinePivotCoordinate x j (c j) b c j =
      algebraMap k A b + ∑ i, algebraMap k A (c i) * x i := by
  rw [affinePivotCoordinate_pivot]
  have hs := Finset.sum_erase_add Finset.univ
    (fun i => algebraMap k A (c i) * x i) (Finset.mem_univ j)
  calc
    _ = algebraMap k A b + ((∑ i ∈ Finset.univ.erase j, algebraMap k A (c i) * x i) +
        algebraMap k A (c j) * x j) := by ring
    _ = _ := congrArg (algebraMap k A b + ·) hs

end LinearForm

universe u

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- Every nonzero affine linear section on the canonical normalization
of a three-coordinate surface has order at most the original hypersurface
degree. The nonzero pivot coefficient and all coordinate choices are
derived, including the exclusion of constant nonvanishing hyperplanes. -/
theorem canonical_normalization_affine_linear_order_le_totalDegree
    (x : Fin 3 → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (b : k) (c : Fin 3 → k)
    (f : MvPolynomial (Fin 3) k) (hf : f ≠ 0) (hroot : aeval x f = 0)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (hz0 : algebraMap k A b + ∑ i, algebraMap k A (c i) * x i ≠ 0)
    (hz : algebraMap A (normalizationRing A)
      (algebraMap k A b + ∑ i, algebraMap k A (c i) * x i) ∈ Q)
    (a : ℕ) (horder : algebraMap A (Localization.AtPrime Q)
      (algebraMap k A b + ∑ i, algebraMap k A (c i) * x i) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    a ≤ f.totalDegree := by
  classical
  have hcoeff : ∃ j, c j ≠ 0 := by
    by_contra! hc
    have hb : b ≠ 0 := by
      intro hb
      apply hz0
      simp [hc, hb]
    have hu : IsUnit (algebraMap A (normalizationRing A) (algebraMap k A b)) :=
      ((isUnit_iff_ne_zero.mpr hb).map (algebraMap k A)).map (algebraMap A (normalizationRing A))
    have hz' : algebraMap A (normalizationRing A) (algebraMap k A b) ∈ Q := by
      simpa [hc] using hz
    exact Ideal.IsPrime.ne_top inferInstance (Q.eq_top_of_isUnit_mem hz' hu)
  obtain ⟨j, hj⟩ := hcoeff
  let r := affineThreePivotOrder j
  let x' : Option (Option Unit) → A := fun i => x (r.symm i)
  let c' : Option (Option Unit) → k := fun i => c (r.symm i)
  let f' := MvPolynomial.renameEquiv k r f
  have hrj : r.symm (some none) = j := affineThreePivotOrder_symm_pivot j
  have hc' : c' (some none) ≠ 0 := by simpa only [c', hrj] using hj
  have hx' : Algebra.adjoin k (Set.range x') = ⊤ := by
    have hrange : Set.range x' = Set.range x := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨r.symm i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨r i, by simp [x']⟩
    rwa [hrange]
  have hf' : f' ≠ 0 := by
    intro hzero
    apply hf
    apply (MvPolynomial.renameEquiv k r).injective
    simpa only [map_zero] using hzero
  have hroot' : aeval x' f' = 0 := by
    change aeval x' (rename r f) = 0
    rw [aeval_rename]
    have hcoords : x' ∘ r = x := by funext i; simp [x']
    rwa [hcoords]
  have hlinear : affinePivotCoordinate x' (some none) (c' (some none)) b c' (some none) =
      algebraMap k A b + ∑ i, algebraMap k A (c i) * x i := by
    rw [affinePivotCoordinate_pivot_eq_linearForm]
    exact congrArg (algebraMap k A b + ·)
      (r.symm.sum_comp (fun i => algebraMap k A (c i) * x i))
  have h := canonical_normalization_affine_pivot_order_le_totalDegree
    x' hx' htr b c' hc' f' hf' hroot' Q hQ
    (by rwa [hlinear]) (by rwa [hlinear]) a (by rwa [hlinear])
  simpa only [f', MvPolynomial.totalDegree_renameEquiv] using h

end DimensionFourDependence
