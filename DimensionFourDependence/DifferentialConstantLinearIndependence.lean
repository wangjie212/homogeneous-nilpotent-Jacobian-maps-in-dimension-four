import DimensionFourDependence.ConstantField
import Mathlib.FieldTheory.LinearDisjoint

/-! # Differential constants preserve linear independence over a curve coefficient field -/

namespace DimensionFourDependence

open Module

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {K J F : Type*} [Field K] [Field J] [Field F]
  [Algebra K J] [Algebra J F] [Algebra K F] [IsScalarTower K J F]

/-- A finite original-constant-independent family annihilated by an
ambient derivation remains independent over a compatible differential
coefficient field whose constants are exactly the original field. -/
theorem differential_constants_fin_linearIndependent
    (D : Derivation K J J) (Δ : Derivation K F F)
    (hcompat : ∀ a : J, Δ (algebraMap J F a) = algebraMap J F (D a))
    (hconstants : ∀ a : J, D a = 0 → ∃ c : K, algebraMap K J c = a)
    {n : ℕ} (v : Fin n → F) (hv : LinearIndependent K v)
    (hzero : ∀ i, Δ (v i) = 0) : LinearIndependent J v := by
  classical
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    obtain ⟨hKi, hKl⟩ := linearIndependent_finSucc'.mp hv
    have hJi : LinearIndependent J (Fin.init v) :=
      ih (Fin.init v) hKi (fun i => hzero i.castSucc)
    apply linearIndependent_finSucc'.mpr
    refine ⟨hJi, ?_⟩
    intro hm
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun J).mp hm
    have hterm (i : Fin n) : Δ (a i • Fin.init v i) = D (a i) • Fin.init v i := by
      simp only [Algebra.smul_def, Fin.init_def]
      rw [Δ.leibniz, hcompat, hzero i.castSucc]
      simp only [smul_eq_mul, zero_mul, zero_add, mul_comm]
    have hd : ∑ i, D (a i) • Fin.init v i = 0 := by
      have he := congrArg Δ ha
      rw [map_sum, hzero (Fin.last n)] at he
      simpa only [hterm] using he
    have hDa : ∀ i, D (a i) = 0 := (Fintype.linearIndependent_iff.mp hJi) _ hd
    choose c hc using fun i => hconstants (a i) (hDa i)
    apply hKl
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨c, ?_⟩
    rw [← ha]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.smul_def, Fin.init_def]
    rw [IsScalarTower.algebraMap_apply K J F, hc i]

/-- The same independence preservation holds for an arbitrary
family, by applying the finite argument to each finite subfamily. -/
theorem differential_constants_linearIndependent
    (D : Derivation K J J) (Δ : Derivation K F F)
    (hcompat : ∀ a : J, Δ (algebraMap J F a) = algebraMap J F (D a))
    (hconstants : ∀ a : J, D a = 0 → ∃ c : K, algebraMap K J c = a)
    {ι : Type*} (v : ι → F) (hv : LinearIndependent K v)
    (hzero : ∀ i, Δ (v i) = 0) : LinearIndependent J v := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  let e := (Fintype.equivFin s).symm
  have he := differential_constants_fin_linearIndependent D Δ hcompat hconstants
    (fun i => v (e i)) ((hv.comp (fun i : s => (i : ι)) Subtype.val_injective).comp e e.injective)
    (fun i => hzero (e i))
  have h := he.comp e.symm e.symm.injective
  simpa only [Function.comp_def, e.apply_symm_apply] using h

end DimensionFourDependence
