import DimensionFourDependence.Defs

/-! # Distinct polynomial degrees and degree-adapted finite families -/

namespace DimensionFourDependence

open Polynomial Module

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- Nonzero polynomials with distinct degrees are linearly independent. -/
theorem polynomial_linearIndependent_of_injective_natDegree
    {ι : Type*} (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    LinearIndependent K p := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  have hpair : Set.Pairwise {j | j ∈ s ∧ c j • p j ≠ 0}
      (fun j k => (c j • p j).degree ≠ (c k • p k).degree) := by
    intro j hj k hk hne he
    have hcj : c j ≠ 0 := (smul_ne_zero_iff.mp hj.2).1
    have hck : c k ≠ 0 := (smul_ne_zero_iff.mp hk.2).1
    have hn := Polynomial.natDegree_eq_of_degree_eq he
    rw [Polynomial.natDegree_smul _ hcj, Polynomial.natDegree_smul _ hck] at hn
    exact hne (hdegree hn)
  have hs := Polynomial.degree_sum_eq_of_disjoint (fun j => c j • p j) s hpair
  rw [hsum, Polynomial.degree_zero] at hs
  have hz : c i • p i = 0 := Polynomial.degree_eq_bot.mp
    (le_bot_iff.mp ((Finset.le_sup hi).trans hs.symm.le))
  exact (smul_eq_zero_iff_left (hp i)).mp hz

/-- A finite-dimensional space embedded in one-variable polynomials
contains a full-size family of nonzero images in strictly increasing degree.
The construction removes the coefficient of a polynomial of minimal degree. -/
theorem polynomial_image_exists_strictMono_natDegree
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (f : V →ₗ[K] Polynomial K) (hf : Function.Injective f) :
    ∃ p : Fin (finrank K V) → V, (∀ i, p i ≠ 0) ∧
      StrictMono (fun i => (f (p i)).natDegree) := by
  classical
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    have hpos : 0 < finrank K V := by omega
    obtain ⟨q, hq⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hfx (x : V) (hx : x ≠ 0) : f x ≠ 0 :=
      fun he => hx (hf (he.trans (map_zero f).symm))
    have hex : ∃ d : ℕ, ∃ x : V, x ≠ 0 ∧ (f x).natDegree = d :=
      ⟨(f q).natDegree, q, hq, rfl⟩
    obtain ⟨p, hp, hpd⟩ := Nat.find_spec hex
    let d := Nat.find hex
    let l : V →ₗ[K] K := (Polynomial.lcoeff K d).comp f
    have hlp : l p ≠ 0 := by
      change (f p).coeff (Nat.find hex) ≠ 0
      rw [← hpd]
      exact Polynomial.leadingCoeff_ne_zero.mpr (hfx p hp)
    have hl : l ≠ 0 := fun he => hlp (by rw [he]; rfl)
    have hsurj : Function.Surjective l :=
      surjective_of_nonzero_of_finrank_eq_one (K := K) (f := l) (by simp) hl
    have hrange : finrank K (LinearMap.range l) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj]
      simp
    have hker : finrank K (LinearMap.ker l) = n := by
      have hr := l.finrank_range_add_finrank_ker
      omega
    obtain ⟨v, hv, hvs⟩ := ih (f.comp (LinearMap.ker l).subtype)
      (hf.comp Subtype.val_injective) hker
    have hvne (i : Fin n) : (v i : V) ≠ 0 :=
      fun he => hv i (Subtype.ext he)
    have hlt (i : Fin n) : (f p).natDegree < (f (v i : V)).natDegree := by
      have hmin : d ≤ (f (v i : V)).natDegree :=
        Nat.find_min' hex ⟨(v i : V), hvne i, rfl⟩
      have hc : (f (v i : V)).coeff d = 0 := (v i).property
      have hneq : d ≠ (f (v i : V)).natDegree := by
        intro he
        rw [he, Polynomial.coeff_natDegree] at hc
        exact (Polynomial.leadingCoeff_ne_zero.mpr (hfx _ (hvne i))) hc
      omega
    refine ⟨Fin.cons p (fun i => (v i : V)), ?_, ?_⟩
    · intro i
      exact Fin.cases hp hvne i
    · have he : (fun i => (f ((Fin.cons p (fun j => (v j : V)) : Fin (n + 1) → V) i)).natDegree) =
          Fin.cons (f p).natDegree (fun i => (f (v i : V)).natDegree) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [he]
      exact Fin.strictMono_cons.mpr ⟨hlt, hvs⟩

end DimensionFourDependence
