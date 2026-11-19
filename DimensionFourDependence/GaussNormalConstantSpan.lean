import DimensionFourDependence.GaussCharacteristicNonplanarity

/-! # The exact constant span of the Gauss normal coordinates

A constant relation among the normal coordinates belongs to all three
successive normal kernels. Their characteristic kernel has dimension
one. A constant characteristic therefore gives exactly one original-field
relation; a varying characteristic tangent excludes every such relation.
The normal-coordinate spans have dimensions three and four, respectively.
-/

namespace DimensionFourDependence

open Matrix Module

section LinearAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A constant normal-coordinate relation is annihilated by all three
successive normal covectors. -/
theorem constant_normal_relation_mem_characteristic
    (D : Derivation K F F) (w : Fin 4 → F) (c : Fin 4 → K)
    (hc : w ⬝ᵥ (fun i => algebraMap K F (c i)) = 0) :
    (fun i => algebraMap K F (c i)) ∈ normalCharacteristicSubspace D w := by
  have hc0 : (fun i => algebraMap K F (c i)) ⬝ᵥ w = 0 := by
    rw [dotProduct_comm]
    exact hc
  have hc1 := constant_normal_kills_derived_direction D _ w
    (fun i => D.map_algebraMap (c i)) hc0
  have hc2 := constant_normal_kills_derived_direction D _ (fun i => D (w i))
    (fun i => D.map_algebraMap (c i)) hc1
  change normalCharacteristicMatrix D w *ᵥ (fun i => algebraMap K F (c i)) = 0
  funext r
  fin_cases r
  · exact hc
  · change (fun i => D (w i)) ⬝ᵥ (fun i => algebraMap K F (c i)) = 0
    rw [dotProduct_comm]
    exact hc1
  · change (fun i => D (D (w i))) ⬝ᵥ (fun i => algebraMap K F (c i)) = 0
    rw [dotProduct_comm]
    exact hc2

/-- Proportional original-field vectors over an extension field are
already proportional over the original field. -/
theorem constant_vector_proportionality_descends {n : ℕ}
    (c d : Fin n → K) (hc : c ≠ 0) (s : F)
    (hs : (fun i => algebraMap K F (d i)) = s • (fun i => algebraMap K F (c i))) :
    ∃ a : K, d = a • c := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hc
  have hpF : algebraMap K F (c p) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K F).injective.ne hp
  have hsp : s = algebraMap K F (d p / c p) := by
    rw [map_div₀]
    apply (eq_div_iff hpF).mpr
    exact (congrFun hs p).symm
  refine ⟨d p / c p, ?_⟩
  funext i
  apply (algebraMap K F).injective
  have hi := congrFun hs i
  simpa only [hsp, Pi.smul_apply, smul_eq_mul, map_mul] using hi

/-- A nonzero constant characteristic vector generates the exact
space of original-field relations among the normal coordinates. -/
theorem normal_constant_relation_space_eq_span_characteristic
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (c : Fin 4 → K) (hc : c ≠ 0)
    (hcC : (fun i => algebraMap K F (c i)) ∈ normalCharacteristicSubspace D w) :
    LinearMap.ker (Fintype.linearCombination K w) = Submodule.span K {c} := by
  let C := normalCharacteristicSubspace D w
  let cF : C := ⟨(fun i => algebraMap K F (c i)), hcC⟩
  have hcF : cF ≠ 0 := by
    intro hz
    apply hc
    funext i
    change c i = 0
    apply (algebraMap K F).injective
    have hi := congrFun (congrArg Subtype.val hz) i
    change algebraMap K F (c i) = 0 at hi
    simpa only [map_zero] using hi
  have hdim : finrank F C = 1 := (normal_ruling_characteristic_subspace_dimensions D w hLI).2
  apply le_antisymm
  · intro d hd
    change Fintype.linearCombination K w d = 0 at hd
    have hd0 : w ⬝ᵥ (fun i => algebraMap K F (d i)) = 0 := by
      simpa only [Fintype.linearCombination_apply, Algebra.smul_def, dotProduct, mul_comm] using hd
    have hdC := constant_normal_relation_mem_characteristic D w d hd0
    obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' cF hcF).mp hdim
      (⟨(fun i => algebraMap K F (d i)), hdC⟩ : C)
    have he : (fun i => algebraMap K F (d i)) = s • (fun i => algebraMap K F (c i)) :=
      (congrArg Subtype.val hs).symm
    obtain ⟨a, ha⟩ := constant_vector_proportionality_descends c d hc s he
    exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = c := Set.mem_singleton_iff.mp hx
    subst x
    have h0 : w ⬝ᵥ (fun i => algebraMap K F (c i)) = 0 := congrFun hcC 0
    change Fintype.linearCombination K w c = 0
    simpa only [Fintype.linearCombination_apply, Algebra.smul_def, dotProduct, mul_comm] using h0

/-- In the fixed-characteristic case, the actual normal coordinate
functions span exactly three dimensions over the original field. -/
theorem normal_component_span_finrank_three_of_constant_characteristic
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (c : Fin 4 → K) (hc : c ≠ 0)
    (hcC : (fun i => algebraMap K F (c i)) ∈ normalCharacteristicSubspace D w) :
    finrank K (Submodule.span K (Set.range w)) = 3 := by
  have he := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination K w)
  rw [Fintype.range_linearCombination,
    normal_constant_relation_space_eq_span_characteristic D w hLI c hc hcC,
    finrank_span_singleton hc] at he
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

/-- A varying characteristic tangent excludes a nonzero constant
characteristic vector. Otherwise both tangent vectors lie in a line. -/
theorem characteristic_tangent_excludes_constant_characteristic
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (b : Fin 4 → F) (hb : b ∈ normalCharacteristicSubspace D w)
    (hpair : LinearIndependent F ![b, fun i => D (b i)])
    (c : Fin 4 → K)
    (hcC : (fun i => algebraMap K F (c i)) ∈ normalCharacteristicSubspace D w) : c = 0 := by
  by_contra hc
  let C := normalCharacteristicSubspace D w
  let cF : C := ⟨(fun i => algebraMap K F (c i)), hcC⟩
  have hcF : cF ≠ 0 := by
    intro hz
    apply hc
    funext i
    change c i = 0
    apply (algebraMap K F).injective
    have hi := congrFun (congrArg Subtype.val hz) i
    change algebraMap K F (c i) = 0 at hi
    simpa only [map_zero] using hi
  have hdim : finrank F C = 1 := (normal_ruling_characteristic_subspace_dimensions D w hLI).2
  obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' cF hcF).mp hdim (⟨b, hb⟩ : C)
  have hrep : s • (fun i => algebraMap K F (c i)) = b := congrArg Subtype.val hs
  have hDrep : (fun i => D (b i)) = D s • (fun i => algebraMap K F (c i)) := by
    rw [← hrep]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, D.leibniz, D.map_algebraMap, mul_zero, zero_add]
    ring
  have hDb : (fun i => D (b i)) ∈ C := by
    rw [hDrep]
    exact C.smul_mem (D s) hcC
  have hle : Submodule.span F (Set.range ![b, fun i => D (b i)]) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  have hspan : finrank F (Submodule.span F (Set.range ![b, fun i => D (b i)])) = 2 := by
    simpa using finrank_span_eq_card hpair
  have hbound := Submodule.finrank_mono hle
  rw [hspan, hdim] at hbound
  omega

/-- In the varying-characteristic case, the four normal coordinate
functions are independent over the original coefficient field. -/
theorem normal_components_independent_of_characteristic_tangent
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (b : Fin 4 → F) (hb : b ∈ normalCharacteristicSubspace D w)
    (hpair : LinearIndependent F ![b, fun i => D (b i)]) :
    LinearIndependent K w := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hrel : w ⬝ᵥ (fun i => algebraMap K F (c i)) = 0 := by
    simpa only [dotProduct, Algebra.smul_def, mul_comm] using hc
  have hcC := constant_normal_relation_mem_characteristic D w c hrel
  have hz := characteristic_tangent_excludes_constant_characteristic D w hLI b hb hpair c hcC
  intro i
  exact congrFun hz i

/-- In the varying-characteristic case, the normal coordinate span
has exactly four dimensions over the original coefficient field. -/
theorem normal_component_span_finrank_four_of_characteristic_tangent
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (b : Fin 4 → F) (hb : b ∈ normalCharacteristicSubspace D w)
    (hpair : LinearIndependent F ![b, fun i => D (b i)]) :
    finrank K (Submodule.span K (Set.range w)) = 4 := by
  simpa using finrank_span_eq_card
    (normal_components_independent_of_characteristic_tangent D w hLI b hb hpair)

end LinearAlgebra

end DimensionFourDependence
