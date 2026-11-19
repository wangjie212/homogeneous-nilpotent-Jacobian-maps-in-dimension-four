import DimensionFourDependence.LinePairParameters
import DimensionFourDependence.CoveringLineFamilySkewTriple

/-! # The actual incidence determinant between any two line charts

Four linear point equations describe intersection of lines in arbitrary
coordinate-permuted matrix charts. Their coefficient matrix has kernel
equal to the actual line intersection. Its determinant is a polynomial
in the eight parameter coordinates, vanishing exactly on intersecting
pairs, also after extending the original coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The four actual point equations of two coordinate-permuted graph lines. -/
def linePairIncidenceMatrix (p q : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  ![Pi.single (p 2) 1 - B 0 0 • Pi.single (p 0) 1 - B 0 1 • Pi.single (p 1) 1,
    Pi.single (p 3) 1 - B 1 0 • Pi.single (p 0) 1 - B 1 1 • Pi.single (p 1) 1,
    Pi.single (q 2) 1 - D 0 0 • Pi.single (q 0) 1 - D 0 1 • Pi.single (q 1) 1,
    Pi.single (q 3) 1 - D 1 0 • Pi.single (q 0) 1 - D 1 1 • Pi.single (q 1) 1]

/-- These point equations commute with every homomorphism of coefficient rings. -/
theorem linePairIncidenceMatrix_map (f : R →+* S) (p q : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) R) :
    (linePairIncidenceMatrix p q B D).map f = linePairIncidenceMatrix p q (B.map f) (D.map f) := by
  ext i j
  fin_cases i <;> simp [linePairIncidenceMatrix, Matrix.map, Pi.single_apply, smul_eq_mul, apply_ite f]

/-- The matrix acts by the four displayed graph-line equations. -/
theorem linePairIncidenceMatrix_mulVec (p q : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) R) (x : Fin 4 → R) :
    linePairIncidenceMatrix p q B D *ᵥ x =
      ![x (p 2) - B 0 0 * x (p 0) - B 0 1 * x (p 1),
        x (p 3) - B 1 0 * x (p 0) - B 1 1 * x (p 1),
        x (q 2) - D 0 0 * x (q 0) - D 0 1 * x (q 1),
        x (q 3) - D 1 0 * x (q 0) - D 1 1 * x (q 1)] := by
  ext i
  fin_cases i <;> simp [linePairIncidenceMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, smul_eq_mul, Pi.single_apply]

variable {K : Type*} [Field K]

/-- Membership in an actual permuted graph line is exactly its two point equations. -/
theorem lineChartMemberLine_mem_iff_equations
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    x ∈ lineChartMemberLine p B ↔
      x (p 2) - B 0 0 * x (p 0) - B 0 1 * x (p 1) = 0 ∧
      x (p 3) - B 1 0 * x (p 0) - B 1 1 * x (p 1) = 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, rfl⟩ := (mem_graphLineFour B z).mp hz
    simp only [lineCoordinatePermutation, LinearEquiv.symm_mk]
    simp [Matrix.mulVec, dotProduct]
  · intro h
    let u : Fin 2 → K := ![x (p 0), x (p 1)]
    let z : Fin 4 → K := ![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1]
    have hz : z = (lineCoordinatePermutation p) x := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · change (B *ᵥ u) 0 = x (p 2)
        simp [u, Matrix.mulVec, dotProduct]
        linear_combination -h.1
      · change (B *ᵥ u) 1 = x (p 3)
        simp [u, Matrix.mulVec, dotProduct]
        linear_combination -h.2
    refine ⟨z, (mem_graphLineFour B z).mpr ⟨u, rfl⟩, ?_⟩
    change (lineCoordinatePermutation p).symm z = x
    rw [hz, LinearEquiv.symm_apply_apply]

/-- The zero vectors of the actual matrix are exactly the actual common line points. -/
theorem linePairIncidenceMatrix_mulVec_zero_iff
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    linePairIncidenceMatrix p q B D *ᵥ x = 0 ↔
      x ∈ lineChartMemberLine p B ∧ x ∈ lineChartMemberLine q D := by
  rw [linePairIncidenceMatrix_mulVec, lineChartMemberLine_mem_iff_equations,
    lineChartMemberLine_mem_iff_equations]
  constructor
  · intro h
    exact ⟨⟨congrFun h 0, congrFun h 1⟩, congrFun h 2, congrFun h 3⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    funext i
    fin_cases i <;> assumption

/-- Its linear kernel is the actual intersection of the two represented lines. -/
theorem linePairIncidenceMatrix_ker
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.ker (linePairIncidenceMatrix p q B D).toLin' =
      lineChartMemberLine p B ⊓ lineChartMemberLine q D := by
  ext x
  exact linePairIncidenceMatrix_mulVec_zero_iff p q B D x

/-- Skewness in any two actual charts is nonvanishing of the actual incidence determinant. -/
theorem linePairIncidenceMatrix_disjoint_iff_det
    (p q : Equiv.Perm (Fin 4)) (B D : Matrix (Fin 2) (Fin 2) K) :
    Disjoint (lineChartMemberLine p B) (lineChartMemberLine q D) ↔
      (linePairIncidenceMatrix p q B D).det ≠ 0 := by
  have he : Disjoint (lineChartMemberLine p B) (lineChartMemberLine q D) ↔
      ∀ x, linePairIncidenceMatrix p q B D *ᵥ x = 0 → x = 0 := by
    rw [Submodule.disjoint_def]
    constructor
    · intro h x hx
      exact h x ((linePairIncidenceMatrix_mulVec_zero_iff p q B D x).mp hx).1
        ((linePairIncidenceMatrix_mulVec_zero_iff p q B D x).mp hx).2
    · intro h x hx hx'
      exact h x ((linePairIncidenceMatrix_mulVec_zero_iff p q B D x).mpr ⟨hx, hx'⟩)
  rw [he]
  change (∀ x, (linePairIncidenceMatrix p q B D).toLin' x = 0 → x = 0) ↔ _
  rw [← injective_iff_map_eq_zero (linePairIncidenceMatrix p q B D).toLin']
  change Function.Injective (linePairIncidenceMatrix p q B D).mulVec ↔ _
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The original-field polynomial incidence equation in the eight parameter entries. -/
noncomputable def linePairIncidencePolynomial (p q : Equiv.Perm (Fin 4)) : MvPolynomial LinePairIndex K :=
  (linePairIncidenceMatrix p q (fun i j => X (Sum.inl (i, j)))
    (fun i j => X (Sum.inr (i, j)))).det

variable {E : Type*} [Field E] [Algebra K E]

/-- The original incidence polynomial specializes to the actual extension-field determinant. -/
theorem linePairIncidencePolynomial_eval (p q : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) E) :
    aeval (linePairCoordinates B D) (linePairIncidencePolynomial (K := K) p q) =
      (linePairIncidenceMatrix p q B D).det := by
  let U : Matrix (Fin 2) (Fin 2) (MvPolynomial LinePairIndex K) :=
    fun i j => X (Sum.inl (i, j))
  let V : Matrix (Fin 2) (Fin 2) (MvPolynomial LinePairIndex K) :=
    fun i j => X (Sum.inr (i, j))
  let f : MvPolynomial LinePairIndex K →+* E := (aeval (linePairCoordinates B D)).toRingHom
  have hU : U.map f = B := by ext i j; simp [Matrix.map, U, f, linePairCoordinates]
  have hV : V.map f = D := by ext i j; simp [Matrix.map, V, f, linePairCoordinates]
  change f (linePairIncidenceMatrix p q U V).det = _
  rw [f.map_det]
  change ((linePairIncidenceMatrix p q U V).map f).det = _
  rw [linePairIncidenceMatrix_map, hU, hV]

/-- Vanishing of the original polynomial equation means actual projective incidence. -/
theorem linePairIncidencePolynomial_zero_iff (p q : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) E) :
    aeval (linePairCoordinates B D) (linePairIncidencePolynomial (K := K) p q) = 0 ↔
      ¬ Disjoint (lineChartMemberLine p B) (lineChartMemberLine q D) := by
  rw [linePairIncidencePolynomial_eval]
  simpa only [not_not] using (not_congr (linePairIncidenceMatrix_disjoint_iff_det p q B D)).symm

end DimensionFourDependence
