import DimensionFourDependence.RationalClosedGaussCover
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Polynomial factorization descends from a relatively closed field extension

The coefficients of a monic divisor of a monic base-field polynomial
are integral over the base. Relative algebraic closedness puts every
such coefficient back in the base. Thus the divisor descends and every
monic irreducible base polynomial stays irreducible in the source field.
This supplies the factorization input for geometric integrality.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every monic divisor over a relatively closed extension descends
to an actual polynomial over the original field. -/
theorem monic_polynomial_divisor_descends_of_relatively_closed
    (hclosed : algebraicClosure K F = ⊥) (p : Polynomial K) (q : Polynomial F)
    (hp : p.Monic) (hq : q.Monic) (hdiv : q ∣ p.map (algebraMap K F)) :
    ∃ q₀ : Polynomial K, q₀.map (algebraMap K F) = q := by
  have hcoeff (i : ℕ) : q.coeff i ∈ Set.range (algebraMap K F) := by
    have hi := Polynomial.isIntegral_coeff_of_dvd p q hp hq hdiv i
    have hm : q.coeff i ∈ algebraicClosure K F := mem_algebraicClosure_iff'.mpr hi
    rw [hclosed, IntermediateField.mem_bot] at hm
    exact hm
  apply (Polynomial.mem_lifts q).mp
  exact (Polynomial.lifts_iff_coeff_lifts q).mpr hcoeff

/-- A monic irreducible polynomial over a relatively closed field
remains irreducible in the entire extension field. -/
theorem monic_irreducible_map_of_relatively_closed
    (hclosed : algebraicClosure K F = ⊥) (p : Polynomial K)
    (hp : p.Monic) (hirred : Irreducible p) :
    Irreducible (p.map (algebraMap K F)) := by
  have hinj : Function.Injective (Polynomial.map (algebraMap K F)) :=
    Polynomial.map_injective _ (algebraMap K F).injective
  apply (hp.map (algebraMap K F)).irreducible_iff_natDegree.mpr
  refine ⟨?_, ?_⟩
  · intro hz
    apply hirred.not_isUnit
    have hp1 : p = 1 := hinj (by simpa only [Polynomial.map_one] using hz)
    rw [hp1]
    exact isUnit_one
  · intro f g hf hg hfg
    obtain ⟨f₀, hff⟩ := monic_polynomial_divisor_descends_of_relatively_closed hclosed p f hp hf
      ⟨g, hfg.symm⟩
    obtain ⟨g₀, hgg⟩ := monic_polynomial_divisor_descends_of_relatively_closed hclosed p g hp hg
      ⟨f, by rw [mul_comm]; exact hfg.symm⟩
    have hf₀ : f₀.Monic := Polynomial.monic_map_iff.mp (hff ▸ hf)
    have hg₀ : g₀.Monic := Polynomial.monic_map_iff.mp (hgg ▸ hg)
    have heq : f₀ * g₀ = p := by
      apply hinj
      rw [Polynomial.map_mul, hff, hgg]
      exact hfg
    have he := (hp.irreducible_iff_natDegree.mp hirred).2 f₀ g₀ hf₀ hg₀ heq
    have hfd : f.natDegree = f₀.natDegree := by
      rw [← hff, Polynomial.natDegree_map_eq_of_injective (algebraMap K F).injective]
    have hgd : g.natDegree = g₀.natDegree := by
      rw [← hgg, Polynomial.natDegree_map_eq_of_injective (algebraMap K F).injective]
    rwa [hfd, hgd]

universe u

variable {K' : Type u} [Field K']

/-- The actual relatively closed Gauss cover introduces no new
factor of any monic irreducible polynomial in the original source. -/
theorem actual_closed_gauss_cover_irreducible_polynomial_map
    (H : Fin 4 → MvPolynomial (Fin 4) K') (I : ImageRelationWitness H)
    (p : Polynomial (closedGaussParameterField H I)) (hp : p.Monic) (hirred : Irreducible p) :
    Irreducible (p.map (algebraMap (closedGaussParameterField H I)
      (FractionRing (MvPolynomial (Fin 4) K')))) :=
  monic_irreducible_map_of_relatively_closed (closedGaussParameterField_relatively_closed H I) p hp hirred

end DimensionFourDependence
