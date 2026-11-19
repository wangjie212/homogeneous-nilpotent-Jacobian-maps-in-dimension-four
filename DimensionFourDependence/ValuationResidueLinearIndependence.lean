import DimensionFourDependence.ValuationResidueCoordinates

/-! # Linear independence of a residue tuple lifts over a valuation ring -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F A κ : Type*} [Field K] [Field F] [CommRing A] [Field κ]
  [Algebra K F]

/-- Independent residue values remain independent in the generic
field. Normalize any alleged relation by a largest-valued nonzero
coefficient; its residue relation then has a coefficient equal to one. -/
theorem valuation_residue_linearIndependent_lifts
    (V : ValuationSubring K) [Algebra V A] [Algebra A F] [Algebra V F]
    [IsScalarTower V A F] [IsScalarTower V K F]
    [Algebra (IsLocalRing.ResidueField V) κ]
    (hinj : Function.Injective (algebraMap A F)) (π : A →+* κ)
    (hcompat : ∀ a : V, π (algebraMap V A a) =
      algebraMap (IsLocalRing.ResidueField V) κ (IsLocalRing.residue V a))
    {n : ℕ} (z : Fin n → A)
    (hres : LinearIndependent (IsLocalRing.ResidueField V) (fun i => π (z i))) :
    LinearIndependent K (fun i => algebraMap A F (z i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hci
  let s := Finset.univ.filter (fun j : Fin n => c j ≠ 0)
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image s (fun j => V.valuation (c j))
    ⟨i, by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hci⟩
  have hck : c k ≠ 0 := (Finset.mem_filter.mp hk).2
  have hmaxall (j : Fin n) : V.valuation (c j) ≤ V.valuation (c k) := by
    by_cases hj : c j = 0
    · simp only [hj, map_zero]
      exact zero_le
    · exact hmax j (by simp [s, hj])
  choose a ha using fun j => (V.valuation_le_iff (c j) (c k)).mp (hmaxall j)
  have hak : a k = 1 := by
    apply Subtype.ext
    apply mul_right_cancel₀ hck
    simpa only [OneMemClass.coe_one, one_mul] using ha k
  have hcoeff : (∑ j, algebraMap K F (c j) * algebraMap A F (z j)) = 0 := by
    simpa only [Algebra.smul_def] using hc
  have hnormalized : algebraMap K F (c k) *
      algebraMap A F (∑ j, algebraMap V A (a j) * z j) = 0 := by
    calc
      _ = ∑ j, algebraMap K F (c j) * algebraMap A F (z j) := by
        simp only [map_sum, Finset.mul_sum, map_mul]
        apply Finset.sum_congr rfl
        intro j _
        have hcoef : algebraMap A F (algebraMap V A (a j)) = algebraMap K F (a j : K) := by
          rw [← IsScalarTower.algebraMap_apply V A F, IsScalarTower.algebraMap_apply V K F]
          rfl
        rw [hcoef]
        have he := congrArg (algebraMap K F) (ha j)
        simp only [map_mul] at he
        rw [← he]
        ring
      _ = 0 := hcoeff
  have hzero : (∑ j, algebraMap V A (a j) * z j) = 0 := by
    apply hinj
    rw [map_zero]
    exact (mul_eq_zero.mp hnormalized).resolve_left ((map_ne_zero _).mpr hck)
  have hzeroResidue := congrArg π hzero
  simp only [map_sum, map_mul, map_zero, hcompat] at hzeroResidue
  have hcoefResidue := Fintype.linearIndependent_iff.mp hres
    (fun j => IsLocalRing.residue V (a j)) (by simpa only [Algebra.smul_def] using hzeroResidue) k
  exact one_ne_zero (by simpa only [hak, map_one] using hcoefResidue)

end DimensionFourDependence
