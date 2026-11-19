import DimensionFourDependence.TangentScaledPolynomialRelation

/-! # A constant parabolic invariant forces algebraicity of its tangent ratio

The maximum is taken over the actual finite vertex support. The highest
candidate degree is positive; all tied terms give a nonzero polynomial
over the actual coefficient field. Clearing tangent powers therefore
proves algebraicity of T times the quadratic vertex coefficient.
-/

namespace DimensionFourDependence

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The coefficient bounds and constancy construct the maximal tied
support, its nonzero annihilating polynomial, and algebraicity of the
tangent-scaled quadratic coefficient. No maximum or relation is assumed. -/
theorem constant_parabolic_invariant_constructs_algebraic_tangent_ratio
    (s : Finset ℕ) (e : ℕ) (m : ℕ → ℕ) (c : ℕ → F)
    (hpositive : ∃ j ∈ s, 0 < j)
    (hindex : ∀ j ∈ s, j ≤ e) (horder : ∀ j ∈ s, m j ≤ e - j)
    (hc : ∀ j ∈ s, c j ≠ 0)
    (f : ℕ → Polynomial E) (T : E) (hT : T ≠ 0)
    (hf : ∀ j ∈ s, (f j).natDegree ≤ e - j - m j)
    (hcoeff : ∀ j ∈ s, (f j).coeff (e - j - m j) = algebraMap F E (c j) * T ^ m j)
    (w : Polynomial E) (hw : w.natDegree ≤ 2)
    (a : E) (hconstant : (∑ j ∈ s, f j * w ^ j) = Polynomial.C a) :
    ∃ N : ℕ, 0 < N ∧
      (s.filter (fun j => e - j - m j + j * 2 = N)).Nonempty ∧
      (∑ j ∈ s.filter (fun j => e - j - m j + j * 2 = N),
        Polynomial.C (c j) * Polynomial.X ^ j) ≠ 0 ∧
      Polynomial.aeval (T * w.coeff 2)
        (∑ j ∈ s.filter (fun j => e - j - m j + j * 2 = N),
          Polynomial.C (c j) * Polynomial.X ^ j) = 0 ∧
      IsAlgebraic F (T * w.coeff 2) := by
  classical
  obtain ⟨N, hN, hmax, k, hk, hkN⟩ := parabolic_candidate_degree_exists_maximum
    s (fun j => e - j - m j) hpositive
  let top := s.filter (fun j => e - j - m j + j * 2 = N)
  have htop : top.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hkN⟩⟩
  have htopmem (j : ℕ) (hj : j ∈ top) : j ∈ s := (Finset.mem_filter.mp hj).1
  have htoporder (j : ℕ) (hj : j ∈ top) : m j + N = e + j := by
    have he := (Finset.mem_filter.mp hj).2
    have hi := hindex j (htopmem j hj)
    have hm := horder j (htopmem j hj)
    omega
  have hrel : (∑ j ∈ top, algebraMap F E (c j) * T ^ m j * w.coeff 2 ^ j) = 0 := by
    have he := constant_parabolic_sum_maximal_coefficient s f (fun j => e - j - m j)
      hf w hw N hN hmax a hconstant
    calc
      _ = ∑ j ∈ top, (f j).coeff (e - j - m j) * w.coeff 2 ^ j :=
        Finset.sum_congr rfl (fun j hj => by rw [hcoeff j (htopmem j hj)])
      _ = 0 := he
  obtain ⟨hpoly, hroot, halg⟩ := tied_coefficient_relation_constructs_algebraic_tangent_ratio
    top htop c (fun j hj => hc j (htopmem j hj)) m e N htoporder T (w.coeff 2) hT hrel
  exact ⟨N, hN, htop, hpoly, hroot, halg⟩

end DimensionFourDependence
