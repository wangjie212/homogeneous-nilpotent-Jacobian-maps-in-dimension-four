import DimensionFourDependence.PrimitiveTwoAxisQuasiTranslation
import DimensionFourDependence.SourcePencilProjectiveFibers

/-! # All but finitely many members of a reduced homogeneous pencil are squarefree -/

namespace DimensionFourDependence

open MvPolynomial UniqueFactorizationMonoid

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- A square polynomial divisor divides every first partial of the
original polynomial; no characteristic or squarefree hypothesis is used. -/
theorem polynomial_square_divisor_divides_every_partial
    (p f : P₀) (hdiv : p * p ∣ f) (i : Fin n) : p ∣ pderiv i f := by
  obtain ⟨g, hg⟩ := hdiv
  refine ⟨2 * pderiv i p * g + p * pderiv i g, ?_⟩
  rw [hg, pderiv_mul, pderiv_mul]
  ring

/-- A prime divisor can occur in at most one member of a reduced
literal source pencil. Otherwise it divides both original generators. -/
theorem prime_source_pencil_divisor_constant_unique
    (p q δ : P₀) (hrel : IsRelPrime p q) (hδ : Prime δ) (a b : K)
    (ha : δ ∣ p - C a * q) (hb : δ ∣ p - C b * q) : a = b := by
  by_contra hab
  have hdiff : δ ∣ C (b - a) * q := by
    convert dvd_sub ha hb using 1
    rw [map_sub]
    ring
  have hunit : IsUnit (C (b - a) : P₀) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun hba => hab hba.symm))).map C
  have hδq : δ ∣ q := (hδ.dvd_mul.mp hdiff).resolve_left
    (fun h => hδ.not_isUnit (isUnit_of_dvd_unit h hunit))
  exact hδ.not_isUnit ((reduced_source_pencil_member_isRelPrime_denominator p q hrel a) ha hδq)

/-- Every repeated irreducible pencil factor belongs to one fixed
Wronskian divisor. Its finitely many normalized prime factors each
account for at most one parameter, constructing a finite exceptional set. -/
theorem reduced_source_pencil_finitely_many_nonsquarefree_members
    (p q : P₀) (hrel : IsRelPrime p q) (i : Fin n)
    (hW : q * pderiv i p - p * pderiv i q ≠ 0)
    (hmember : ∀ a : K, p - C a * q ≠ 0) :
    ∃ S : Set K, S.Finite ∧ ∀ a ∉ S, Squarefree (p - C a * q) := by
  classical
  letI : NormalizedGCDMonoid P₀ := Classical.arbitrary (NormalizedGCDMonoid P₀)
  let W := q * pderiv i p - p * pderiv i q
  let F : Finset P₀ := (normalizedFactors W).toFinset
  let S : Set K := ⋃ δ ∈ (F : Set P₀), {a : K | δ ∣ p - C a * q}
  have hS : S.Finite := F.finite_toSet.biUnion (fun δ hδF =>
    (show Set.Subsingleton {a : K | δ ∣ p - C a * q} from
      fun a ha b hb => prime_source_pencil_divisor_constant_unique p q δ hrel
        (prime_of_normalized_factor δ (Multiset.mem_toFinset.mp hδF)) a b ha hb).finite)
  refine ⟨S, hS, ?_⟩
  intro a ha
  by_contra hn
  have hnot : ¬∀ δ : P₀, Irreducible δ → ¬δ * δ ∣ p - C a * q := by
    intro h
    exact hn ((squarefree_iff_no_irreducibles (hmember a)).mpr h)
  push Not at hnot
  obtain ⟨δ, hδ, hsq⟩ := hnot
  have hδmember : δ ∣ p - C a * q := (dvd_mul_right δ δ).trans hsq
  have hδder := polynomial_square_divisor_divides_every_partial δ (p - C a * q) hsq i
  have hδW : δ ∣ W := by
    have hdiv := dvd_sub (dvd_mul_of_dvd_right hδder q) (dvd_mul_of_dvd_left hδmember (pderiv i q))
    convert hdiv using 1
    simp only [W, map_sub, pderiv_C_mul]
    ring
  obtain ⟨δ', hδ'F, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hW hδ hδW
  apply ha
  exact Set.mem_iUnion.mpr ⟨δ', Set.mem_iUnion.mpr
    ⟨Multiset.mem_toFinset.mpr hδ'F, hassoc.dvd'.trans hδmember⟩⟩

variable [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A coprime pair of positive homogeneous forms constructs a nonzero
Wronskian coordinate. No separability or moving-ratio assumption is supplied. -/
theorem positive_homogeneous_reduced_pencil_has_nonzero_wronskian
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hp : p ≠ 0)
    (hpH : p.IsHomogeneous D) (hrel : IsRelPrime p q) :
    ∃ i : Fin 4, q * pderiv i p - p * pderiv i q ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hp
  apply eq_zero_of_forall_pderiv_eq_zero hpH hD.ne'
  intro i
  apply pderiv_eq_zero_of_dvd hpH i
  apply hrel.dvd_of_dvd_mul_left
  exact ⟨pderiv i q, sub_eq_zero.mp (hn i)⟩

/-- The actual reduced positive homogeneous source pencil has only
finitely many nonsquarefree members, over the original characteristic-zero
field. Every other member retains the full original homogeneous degree. -/
theorem positive_homogeneous_reduced_pencil_constructs_finite_squarefree_exceptions
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hp : p ≠ 0)
    (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) (hrel : IsRelPrime p q) :
    ∃ S : Set K, S.Finite ∧ ∀ a ∉ S, Squarefree (p - C a * q) ∧
      p - C a * q ≠ 0 ∧ (p - C a * q).IsHomogeneous D ∧ (p - C a * q).totalDegree = D := by
  have hmember (a : K) : p - C a * q ≠ 0 := by
    intro hz
    have hpq : p = C a * q := sub_eq_zero.mp hz
    have hunit : IsUnit q := hrel (by rw [hpq]; exact dvd_mul_left q (C a)) dvd_rfl
    exact positive_homogeneous_polynomial_not_isUnit q hD hqH hunit
  obtain ⟨i, hW⟩ := positive_homogeneous_reduced_pencil_has_nonzero_wronskian p q hD hp hpH hrel
  obtain ⟨S, hS, hgood⟩ := reduced_source_pencil_finitely_many_nonsquarefree_members p q hrel i hW hmember
  refine ⟨S, hS, ?_⟩
  intro a ha
  have hhom : (p - C a * q).IsHomogeneous D := hpH.sub (hqH.C_mul a)
  exact ⟨hgood a ha, hmember a, hhom, hhom.totalDegree (hmember a)⟩

end DimensionFourDependence
