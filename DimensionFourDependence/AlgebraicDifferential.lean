import DimensionFourDependence.AlgebraicDerivation

/-! # Gluing derivatives over an arbitrary algebraic extension

The construction on finite subfields is supplied by Mathlib. Compatibility
on inclusions lets us glue these constructions without a finiteness
hypothesis on the whole extension.
-/

namespace DimensionFourDependence

variable {E L : Type*} [Field E] [CharZero E] [Differential E] [Field L] [Algebra E L]

/-- Compatibility of the canonical differentials on nested finite subfields. -/
theorem finiteDifferential_inclusion
    (B C : IntermediateField E L) [FiniteDimensional E B] [FiniteDimensional E C]
    (hBC : B ≤ C) (x : B) :
    algebraMap B L (Differential.deriv x) =
      algebraMap C L (Differential.deriv (IntermediateField.inclusion hBC x)) := by
  have h := Differential.algHom_deriv' (IntermediateField.inclusion hBC)
    (IntermediateField.inclusion hBC).injective x
  exact congrArg (algebraMap C L) h

variable [Algebra.IsAlgebraic E L]

/-- Differentiate an element in the finite simple field it generates. -/
noncomputable def algebraicDifferentialValue (x : L) : L :=
  let B := IntermediateField.adjoin E ({x} : Set L)
  letI : FiniteDimensional E B :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  algebraMap B L (Differential.deriv
    (⟨x, IntermediateField.subset_adjoin E {x} (by simp)⟩ : B))

/-- The value agrees with the differential on any finite intermediate field
containing the element, independently of its chosen presentation. -/
theorem algebraicDifferentialValue_eq
    (B : IntermediateField E L) [FiniteDimensional E B] (x : B) :
    algebraicDifferentialValue (E := E) (x : L) = algebraMap B L (Differential.deriv x) := by
  let C := IntermediateField.adjoin E ({(x : L)} : Set L)
  letI : FiniteDimensional E C :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (x : L)).isIntegral
  have hCB : C ≤ B := IntermediateField.adjoin_le_iff.mpr (by
    intro y hy
    have hy' : y = (x : L) := Set.mem_singleton_iff.mp hy
    subst y
    exact x.property)
  let xc : C := ⟨x, IntermediateField.subset_adjoin E {(x : L)} (by simp)⟩
  have heq : IntermediateField.inclusion hCB xc = x := Subtype.ext rfl
  exact (finiteDifferential_inclusion C B hCB xc).trans (congrArg
    (fun z : B => algebraMap B L (Differential.deriv z)) heq)

theorem algebraicDifferentialValue_add (x y : L) :
    algebraicDifferentialValue (E := E) (x + y) =
      algebraicDifferentialValue (E := E) x + algebraicDifferentialValue (E := E) y := by
  let B := IntermediateField.adjoin E ({x, y} : Set L)
  letI : FiniteDimensional E B := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let bx : B := ⟨x, IntermediateField.subset_adjoin E {x, y} (by simp)⟩
  let by_ : B := ⟨y, IntermediateField.subset_adjoin E {x, y} (by simp)⟩
  have hx := algebraicDifferentialValue_eq B bx
  have hy := algebraicDifferentialValue_eq B by_
  have hxy := algebraicDifferentialValue_eq B (bx + by_)
  exact hxy.trans (by rw [map_add, map_add, ← hx, ← hy])

theorem algebraicDifferentialValue_mul (x y : L) :
    algebraicDifferentialValue (E := E) (x * y) =
      x * algebraicDifferentialValue (E := E) y + y * algebraicDifferentialValue (E := E) x := by
  let B := IntermediateField.adjoin E ({x, y} : Set L)
  letI : FiniteDimensional E B := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let bx : B := ⟨x, IntermediateField.subset_adjoin E {x, y} (by simp)⟩
  let by_ : B := ⟨y, IntermediateField.subset_adjoin E {x, y} (by simp)⟩
  have hx := algebraicDifferentialValue_eq B bx
  have hy := algebraicDifferentialValue_eq B by_
  have hxy := algebraicDifferentialValue_eq B (bx * by_)
  exact hxy.trans (by
    rw [Differential.deriv.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, ← hx, ← hy]
    rfl)

theorem algebraicDifferentialValue_zero : algebraicDifferentialValue (E := E) (0 : L) = 0 := by
  have h := algebraicDifferentialValue_add (E := E) (0 : L) 0
  simp only [add_zero] at h
  exact (add_eq_left (a := algebraicDifferentialValue (E := E) (0 : L))).mp h.symm

/-- The glued integer derivation on the entire algebraic extension. -/
noncomputable def algebraicIntDerivation : Derivation ℤ L L :=
  Derivation.mk'
    ({ toFun := algebraicDifferentialValue (E := E)
       map_zero' := algebraicDifferentialValue_zero
       map_add' := algebraicDifferentialValue_add } : L →+ L).toIntLinearMap
    (by intro x y; exact algebraicDifferentialValue_mul x y)

theorem algebraicIntDerivation_apply (x : L) :
    algebraicIntDerivation (E := E) x = algebraicDifferentialValue (E := E) x := rfl

/-- The glued derivation extends the prescribed differential on `E`. -/
theorem algebraicIntDerivation_extends (a : E) :
    algebraicIntDerivation (E := E) (algebraMap E L a) =
      algebraMap E L (Differential.deriv a) := by
  let B := IntermediateField.adjoin E ({algebraMap E L a} : Set L)
  letI : FiniteDimensional E B := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsAlgebraic.isAlgebraic (algebraMap E L a)).isIntegral
  have h := algebraicDifferentialValue_eq B (algebraMap E B a)
  rw [deriv_algebraMap] at h
  exact h

@[reducible] noncomputable def algebraicDifferential : Differential L :=
  ⟨algebraicIntDerivation (E := E)⟩

theorem algebraicDifferentialAlgebra :
    letI := algebraicDifferential (E := E) (L := L)
    DifferentialAlgebra E L := by
  letI := algebraicDifferential (E := E) (L := L)
  exact ⟨algebraicIntDerivation_extends⟩

variable {K : Type*} [Field K] [CharZero K]
  [Algebra K E] [Algebra K L] [IsScalarTower K E L]

omit [Differential E] [CharZero E] in
/-- A coordinate derivation extends uniquely through every algebraic field
extension in characteristic zero. No finite-dimensional hypothesis is
needed for the coefficient field in Lemma 2.2. -/
theorem existsUnique_derivation_extension_algebraic (D : Derivation K E E) :
    ∃! Δ : Derivation K L L,
      ∀ a : E, Δ (algebraMap E L a) = algebraMap E L (D a) := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  letI : Differential E := ⟨D.restrictScalars ℤ⟩
  letI : Differential L := algebraicDifferential (E := E) (L := L)
  letI : DifferentialAlgebra E L := algebraicDifferentialAlgebra
  have hK : ∀ a : K, Differential.deriv (algebraMap K L a) = 0 := by
    intro a
    rw [IsScalarTower.algebraMap_apply K E L, deriv_algebraMap]
    change algebraMap E L (D (algebraMap K E a)) = 0
    rw [D.map_algebraMap, map_zero]
  let Δ := intDerivationToBase Differential.deriv hK
  have hΔ : ∀ a : E, Δ (algebraMap E L a) = algebraMap E L (D a) := by
    intro a
    exact deriv_algebraMap a
  refine ⟨Δ, hΔ, ?_⟩
  intro Δ' hΔ'
  apply derivation_extension_unique (K := K) (E := E) Δ' Δ
  · intro a
    rw [hΔ', hΔ]
  · exact Algebra.IsAlgebraic.isAlgebraic

end DimensionFourDependence
