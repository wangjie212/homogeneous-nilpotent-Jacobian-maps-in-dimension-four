import DimensionFourDependence.GeometricNormalizedTangentField
import DimensionFourDependence.RealizedConeLinearFactor
import DimensionFourDependence.FiniteCoefficientFieldEnlargement

/-! # The actual geometric cone data construct their rational common linear factor

The reduced original pencil constructs compatible source and closed
Gauss embeddings, its entire direction equation and finite tangent
field. Enlarging that field by the algebraic cone coefficients gives
one actual coefficient branch. The cone expression then constructs its
ternary forms and descends them to the actual rational parameter field.
The complete coefficient-branch identities recover the first-three common
linear factor over K(t), together with all three scalar factors there.
Only the specified vertex, moving-normal and cone-expression geometry
is retained; no field realization, ternary expansion or rational covector
is supplied.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

/-- The actual original geometric pencil and fixed-vertex cone
expression construct homogeneous ternary forms over the original
rational Gauss parameter field, with exact original map values.
All compatible field embeddings, the direction equation, finite
coefficient fields and polynomial expansions are constructed internally. -/
theorem geometric_fixed_vertex_cone_constructs_rational_linear_power_forms
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) z₀) (hline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r₀ : MvPolynomial (Fin 4) K) (hr₀ : r₀ = p ∨ r₀ = q) (hrvertex : 0 < r₀.degreeOf (Fin.last 3)) :
    ∃ g : closedGaussParameterField H I →ₐ[K] E,
      ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w0 B C : E),
      (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
      (z₀ (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
      ∀ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 →
      Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 →
      (∑ i : Fin 3, (ν i : E) * A i) = 0 → ∀ (j : Fin 3), A j = 1 →
      ∀ (R : E), R ≠ 0 → ∀ (κ : g.fieldRange), κ ≠ 0 → C = (κ : E) / R →
      ∀ (V : Fin 3 → E) (a b : E), (∀ i, IsAlgebraic g.fieldRange (V i)) →
      IsAlgebraic g.fieldRange a → IsAlgebraic g.fieldRange b →
      (∀ i : Fin 3, aeval z₀ (H i.castSucc) = algebraMap E G₀ (V i) * (algebraMap E G₀ R) ^ d) →
      (aeval z₀ (H (Fin.last 3)) = algebraMap E G₀ a * (algebraMap E G₀ R) ^ d +
        algebraMap E G₀ b * (algebraMap E G₀ R) ^ (d - 1) *
          (∑ i : Fin 3, algebraMap E G₀ (ν i : E) * z₀ i.castSucc)) →
      ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), (∀ i,
        (Q i).IsHomogeneous d ∧
        MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
          (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
            algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
      ∃ ℓ : Fin 3 → RatFunc K, ℓ ≠ 0 ∧ ∃ r : Fin 3 → RatFunc K,
        ∀ i : Fin 3, Q i.castSucc = MvPolynomial.C (r i) * linearFormPolynomial ℓ ^ d := by
  classical
  obtain ⟨g, f, hf, hg, hfield⟩ := geometric_normalized_vertex_pencil_constructs_common_finite_tangent_field
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨Φ, m, _hΦ0, hΦ, _hm, _hirr, hI, _halgRatio, L, hL, hAmem, u, _hu, huR⟩ :=
    hfield t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC
  let J := g.fieldRange
  let S : Finset E := {a, b} ∪ Finset.univ.image V
  have hSalg (z : E) (hz : z ∈ S) : IsAlgebraic J z := by
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz : z = a ∨ z = b) with rfl | rfl
      · exact ha
      · exact hb
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
      exact hV i
  obtain ⟨F, hF, hLF, hSF⟩ := finite_intermediate_field_enlarge_by_algebraic_values L hL S hSalg
  let : Module.Finite J F := hF
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  have haF : a ∈ F := hSF (Finset.mem_union_left _ (by simp))
  have hbF : b ∈ F := hSF (Finset.mem_union_left _ (by simp))
  have hVF (i : Fin 3) : V i ∈ F :=
    hSF (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  let AF : Fin 3 → F := fun i => ⟨A i, hLF (hAmem i)⟩
  let VF : Fin 3 → F := fun i => ⟨V i, hVF i⟩
  let νF : Fin 3 → F := fun i => algebraMap J F (ν i)
  let aF : F := ⟨a, haF⟩
  let bF : F := ⟨b, hbF⟩
  let uF : F := ⟨(u : E), hLF u.property⟩
  have hAF : (fun i => algebraMap F E (AF i)) = A := by funext i; rfl
  have hΦzero : aeval A Φ = 0 :=
    (projectiveFieldPointIdeal_mem_homogeneous A Φ hΦ).mp (by rw [hI]; exact Ideal.subset_span (by simp))
  have hΦF : aeval AF Φ = 0 := by
    apply (algebraMap F E).injective
    have he := comp_aeval_apply AF (IsScalarTower.toAlgHom K F E) Φ
    change algebraMap F E (aeval AF Φ) = aeval (fun i => algebraMap F E (AF i)) Φ at he
    rw [hAF, hΦzero] at he
    exact he.trans (map_zero _).symm
  have hRbase : R = algebraMap F E uF *
      (∑ i : Fin 3, aeval (fun k => algebraMap F E (AF k)) (pderiv i Φ) * x i) := by
    simpa only [hAF, uF, IntermediateField.algebraMap_apply] using huR
  have hxF (i : Fin 3) : f (rationalCoordinate (K := K) i.castSucc) =
      algebraMap E G₀ (x i) + algebraMap F G₀ (AF i) * t := by
    rw [hf]
    exact hx i
  have heval (T : MvPolynomial (Fin 4) K) :
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ T) = aeval z₀ T := by
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f T
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have hfirstF (i : Fin 3) : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap F G₀ (VF i) * (algebraMap E G₀ R) ^ d := by
    rw [heval]
    exact hfirst i
  have hlastF : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap F G₀ aF * (algebraMap E G₀ R) ^ d +
        algebraMap F G₀ bF * (algebraMap E G₀ R) ^ (d - 1) *
          (∑ i : Fin 3, algebraMap F G₀ (νF i) * f (rationalCoordinate (K := K) i.castSucc)) := by
    rw [heval]
    have hmapF (v : F) : algebraMap F G₀ v = algebraMap E G₀ (v : E) := rfl
    simpa only [hf, hmapF, aF, bF, νF, IntermediateField.coe_algebraMap_apply,
      IntermediateField.algebraMap_apply] using hlast
  have hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr₀ with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  obtain ⟨Q, hQ, ℓ, hℓ, c, hc⟩ := compatible_realized_cone_gradient_constructs_rational_linear_factor H I E G₀ hind g f hg F inferInstance
    e p q hp hq hrel hpH hqH hparameter hvertex hd AF Φ hΦ hΦF νF VF uF aF bF x t R hxF hRbase hfirstF hlastF
  exact ⟨Q, (fun i => ⟨(hQ i).2.1, (hQ i).2.2⟩), ℓ, hℓ, c, hc⟩

end DimensionFourDependence
