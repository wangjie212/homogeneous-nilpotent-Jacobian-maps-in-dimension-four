import DimensionFourDependence.PolynomialDegreeIndependence

/-! # Products of finite polynomial spaces have at least the sum of their dimensions minus one -/

namespace DimensionFourDependence

open Polynomial Module

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- If a polynomial space contains every product from two nonzero
finite polynomial spaces, its dimension is at least their dimension sum
minus one. Distinct leading degrees construct the independent products. -/
theorem polynomial_subspace_product_finrank_lower_bound
    (W V U : Submodule K (Polynomial K))
    [Module.Finite K W] [Module.Finite K V] [Module.Finite K U]
    (hW : 0 < finrank K W) (hV : 0 < finrank K V)
    (hmul : ∀ p ∈ W, ∀ q ∈ V, p * q ∈ U) :
    finrank K W + finrank K V ≤ finrank K U + 1 := by
  classical
  obtain ⟨p, hp, hpm⟩ := polynomial_image_exists_strictMono_natDegree W.subtype
    Subtype.val_injective
  obtain ⟨q, hq, hqm⟩ := polynomial_image_exists_strictMono_natDegree V.subtype
    Subtype.val_injective
  change StrictMono (fun i => (p i : Polynomial K).natDegree) at hpm
  change StrictMono (fun i => (q i : Polynomial K).natDegree) at hqm
  have hp0 (i) : (p i : Polynomial K) ≠ 0 := fun h => hp i (Subtype.ext h)
  have hq0 (i) : (q i : Polynomial K) ≠ 0 := fun h => hq i (Subtype.ext h)
  let im : Fin (finrank K W) := ⟨finrank K W - 1, by omega⟩
  let j0 : Fin (finrank K V) := ⟨0, hV⟩
  let jS (j : Fin (finrank K V - 1)) : Fin (finrank K V) :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  let z : Fin (finrank K W) ⊕ Fin (finrank K V - 1) → Polynomial K :=
    Sum.elim (fun i => (p i : Polynomial K) * (q j0 : Polynomial K))
      (fun j => (p im : Polynomial K) * (q (jS j) : Polynomial K))
  have hpmax (i) : (p i : Polynomial K).natDegree ≤ (p im : Polynomial K).natDegree :=
    hpm.monotone (by change i.val ≤ finrank K W - 1; have := i.isLt; omega)
  have hqmin (j) : (q j0 : Polynomial K).natDegree < (q (jS j) : Polynomial K).natDegree :=
    hqm (by change 0 < j.val + 1; omega)
  have hz0 (i) : z i ≠ 0 := by
    cases i with
    | inl i => exact mul_ne_zero (hp0 i) (hq0 j0)
    | inr j => exact mul_ne_zero (hp0 im) (hq0 (jS j))
  have hzdeg : Function.Injective (fun i => (z i).natDegree) := by
    rintro (i | i) (j | j) he
    · change ((p i : Polynomial K) * (q j0 : Polynomial K)).natDegree =
        ((p j : Polynomial K) * (q j0 : Polynomial K)).natDegree at he
      rw [Polynomial.natDegree_mul (hp0 i) (hq0 j0),
        Polynomial.natDegree_mul (hp0 j) (hq0 j0)] at he
      exact congrArg Sum.inl (hpm.injective (by omega))
    · change ((p i : Polynomial K) * (q j0 : Polynomial K)).natDegree =
        ((p im : Polynomial K) * (q (jS j) : Polynomial K)).natDegree at he
      rw [Polynomial.natDegree_mul (hp0 i) (hq0 j0),
        Polynomial.natDegree_mul (hp0 im) (hq0 (jS j))] at he
      have := hpmax i
      have := hqmin j
      omega
    · change ((p im : Polynomial K) * (q (jS i) : Polynomial K)).natDegree =
        ((p j : Polynomial K) * (q j0 : Polynomial K)).natDegree at he
      rw [Polynomial.natDegree_mul (hp0 im) (hq0 (jS i)),
        Polynomial.natDegree_mul (hp0 j) (hq0 j0)] at he
      have := hpmax j
      have := hqmin i
      omega
    · change ((p im : Polynomial K) * (q (jS i) : Polynomial K)).natDegree =
        ((p im : Polynomial K) * (q (jS j) : Polynomial K)).natDegree at he
      rw [Polynomial.natDegree_mul (hp0 im) (hq0 (jS i)),
        Polynomial.natDegree_mul (hp0 im) (hq0 (jS j))] at he
      have heq : jS i = jS j := hqm.injective (by omega)
      have hij : i = j := Fin.ext (by
        have hv := congrArg Fin.val heq
        change i.val + 1 = j.val + 1 at hv
        omega)
      exact congrArg Sum.inr hij
  have hmem (i) : z i ∈ U := by
    cases i with
    | inl i => exact hmul _ (p i).property _ (q j0).property
    | inr j => exact hmul _ (p im).property _ (q (jS j)).property
  let zu (i) : U := ⟨z i, hmem i⟩
  have hLI : LinearIndependent K zu := by
    apply LinearIndependent.of_comp U.subtype
    exact polynomial_linearIndependent_of_injective_natDegree z hz0 hzdeg
  have hb := hLI.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hb
  omega

end DimensionFourDependence
