import DimensionFourDependence.OutputCoordinates

/-! # The actual coefficient field and its coordinate derivatives, Lemma 2.2

Given algebraically independent outputs `Y` in the ambient source field,
the coefficient field is the relative algebraic closure of the actual
subfield `K(Y)`. Coordinate derivations on that field are constructed,
their mixed derivatives commute, and its elements are characterized as
the constants of a nonzero vertical derivation in relative trdeg one.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- The field `L` in Lemma 2.2, as an actual intermediate field of the source
field over the output field. -/
@[reducible] noncomputable def coefficientField (Y : Fin n → F) :
    IntermediateField (IntermediateField.adjoin K (Set.range Y)) F :=
  algebraicClosure (IntermediateField.adjoin K (Set.range Y)) F

/-- The uniquely extended `Y_i`-coordinate derivation on the actual relative
algebraic closure. -/
noncomputable def coefficientPartial (Y : Fin n → F) (hY : AlgebraicIndependent K Y) (i : Fin n) :
    Derivation K (coefficientField (K := K) Y) (coefficientField (K := K) Y) :=
  Classical.choose (existsUnique_derivation_extension_algebraic
    (K := K) (E := IntermediateField.adjoin K (Set.range Y)) (L := coefficientField (K := K) Y)
    (outputPartial Y hY i))

theorem coefficientPartial_extends (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (i : Fin n) (a : IntermediateField.adjoin K (Set.range Y)) :
    coefficientPartial (K := K) Y hY i
        (algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) a) =
      algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) (outputPartial Y hY i a) :=
  (Classical.choose_spec (existsUnique_derivation_extension_algebraic
    (K := K) (E := IntermediateField.adjoin K (Set.range Y)) (L := coefficientField (K := K) Y)
    (outputPartial Y hY i))).1 a

theorem coefficientPartial_coordinate (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (i j : Fin n) :
    coefficientPartial (K := K) Y hY i
        (algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) (outputCoordinate (K := K) Y j)) =
      if j = i then 1 else 0 := by
  rw [coefficientPartial_extends, outputPartial_coordinate]
  by_cases hji : j = i <;> simp [hji]

theorem coefficientPartial_unique (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (i : Fin n) (D : Derivation K (coefficientField (K := K) Y) (coefficientField (K := K) Y))
    (hD : ∀ a : IntermediateField.adjoin K (Set.range Y),
      D (algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) a) =
        algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) (outputPartial Y hY i a)) :
    D = coefficientPartial (K := K) Y hY i :=
  (Classical.choose_spec (existsUnique_derivation_extension_algebraic
    (K := K) (E := IntermediateField.adjoin K (Set.range Y)) (L := coefficientField (K := K) Y)
    (outputPartial Y hY i))).2 D hD

/-- Symmetry of mixed coordinate derivatives on the actual field `L`. -/
theorem coefficientPartials_commute (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (i j : Fin n) (a : coefficientField (K := K) Y) :
    coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j a) =
      coefficientPartial (K := K) Y hY j (coefficientPartial (K := K) Y hY i a) := by
  apply derivation_extensions_commute (K := K) (E := IntermediateField.adjoin K (Set.range Y))
    (outputPartial Y hY i) (outputPartial Y hY j)
  · exact coefficientPartial_extends Y hY i
  · exact coefficientPartial_extends Y hY j
  · exact outputPartials_commute Y hY i j
  · exact Algebra.IsAlgebraic.isAlgebraic

/-- A vertical derivation kills the entire output field, not only its
chosen generators. -/
theorem vertical_derivation_kills_output_field (Y : Fin n → F) (D : Derivation K F F)
    (hY : ∀ i, D (Y i) = 0) :
    IntermediateField.adjoin K (Set.range Y) ≤ derivationConstants D := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro y ⟨i, rfl⟩
  exact hY i

/-- Every element of the relative algebraic closure is a vertical constant. -/
theorem vertical_derivation_kills_coefficient_field (Y : Fin n → F) (D : Derivation K F F)
    (hY : ∀ i, D (Y i) = 0) (a : coefficientField (K := K) Y) : D (a : F) = 0 := by
  let E := IntermediateField.adjoin K (Set.range Y)
  let d := derivationOverConstantSubfield D E (vertical_derivation_kills_output_field Y D hY)
  exact derivation_zero_of_isAlgebraic d (a : F) (mem_algebraicClosure_iff.mp a.property)

/-- The precise constant-field assertion for the source and output fields
in Lemma 2.2. The relative-transcendence-degree hypothesis is stated explicitly;
its deduction from the rank-three polynomial-map setup is still separate. -/
theorem vertical_constant_iff_mem_coefficient_field (Y : Fin n → F) (D : Derivation K F F)
    (hD : D ≠ 0) (hY : ∀ i, D (Y i) = 0)
    (htr : Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F ≤ 1) (x : F) :
    D x = 0 ↔ x ∈ coefficientField (K := K) Y := by
  let E := IntermediateField.adjoin K (Set.range Y)
  let d := derivationOverConstantSubfield D E (vertical_derivation_kills_output_field Y D hY)
  have hd : d ≠ 0 := by
    intro h
    apply hD
    ext y
    exact congrArg (fun δ : Derivation E F F => δ y) h
  exact (derivation_zero_iff_isAlgebraic_of_trdeg_le_one d hd htr x).trans
    mem_algebraicClosure_iff.symm

/-- Equality of the actual fields of constants in the original source field. -/
theorem vertical_constants_eq_coefficient_field (Y : Fin n → F) (D : Derivation K F F)
    (hD : D ≠ 0) (hY : ∀ i, D (Y i) = 0)
    (htr : Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F ≤ 1) :
    derivationConstants D = (coefficientField (K := K) Y).restrictScalars K := by
  ext x
  exact vertical_constant_iff_mem_coefficient_field Y D hD hY htr x

end DimensionFourDependence
