/- Foundation adapted from the neighboring quartic project.
   Only the general-degree algebraic results are used for the present paper.
   The source theorem file with its admitted surface argument is not imported. -/
import DimensionFourDependence.Homogeneous

/-!
# Basic identities and reductions

Elementary results from §2.1, the identities (3.1), the reduction (2.3), and the
rank-one part of Lemma 2.1 of `quartic_dependence.pdf`, all fully proved.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-! ### The identities (3.1) -/

/-- Euler's identity `N X = d·H` for `N = JH` (the first identity in (3.1) of
`quartic_dependence.pdf`, there with `d = 4`). -/
theorem euler_identity {n : ℕ} (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ}
    (hH : IsHomogMap H d) : jac H *ᵥ coordVec = d • H := by
  funext i
  simp only [mulVec, dotProduct, jac, coordVec, of_apply, Pi.smul_apply]
  rw [← (hH i).sum_X_mul_pderiv]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The identity `vᵀ H = 0` for a left kernel vector `v` of `JH` (second identity in (3.1),
also (1.2), of `quartic_dependence.pdf`). -/
theorem left_normal_dot_eq_zero [CharZero K] {n : ℕ} (H v : Fin n → MvPolynomial (Fin n) K)
    {d : ℕ} (hd : d ≠ 0) (hH : IsHomogMap H d) (hv : v ᵥ* jac H = 0) :
    ∑ i, v i * H i = 0 := by
  have h := congrArg (fun w => w ⬝ᵥ (coordVec : Fin n → MvPolynomial (Fin n) K)) hv
  simp only [zero_dotProduct] at h
  rw [← dotProduct_mulVec, euler_identity H hH] at h
  simp only [dotProduct, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum] at h
  rcases smul_eq_zero.mp h with h | h
  · exact absurd h hd
  · exact h

/-- The identity `(Jv)ᵀ H = 0` for a left kernel vector `v` of `JH` (third identity in (3.1),
also (1.2), of `quartic_dependence.pdf`), obtained by differentiating `vᵀ H = 0`. -/
theorem jac_left_normal_dot_eq_zero [CharZero K] {n : ℕ} (H v : Fin n → MvPolynomial (Fin n) K)
    {d : ℕ} (hd : d ≠ 0) (hH : IsHomogMap H d) (hv : v ᵥ* jac H = 0) :
    H ᵥ* jac v = 0 := by
  have h0 := left_normal_dot_eq_zero H v hd hH hv
  funext j
  have h1 := congrArg (pderiv j) h0
  have h2 := congrFun hv j
  simp only [map_sum, Derivation.leibniz, map_zero, smul_eq_mul, Finset.sum_add_distrib] at h1
  simp only [vecMul, dotProduct, jac, of_apply, Pi.zero_apply] at h2 ⊢
  linear_combination h1 - h2

/-- The entries of `JH` are homogeneous of degree `d - 1` when `H` is homogeneous of degree `d`
("`N` … homogeneous … of degree `d − 1`", Lemma 2.3 of `quartic_dependence.pdf`). -/
theorem jac_entry_homog {n : ℕ} (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ}
    (hH : IsHomogMap H d) (i j : Fin n) : ((jac H) i j).IsHomogeneous (d - 1) :=
  (hH i).pderiv

/-- A left normal of degree at most one forces dependence: this is the sentence after (2.3)
in `quartic_dependence.pdf`: "a constant left normal gives dependence. For linear `v = AX`,
Euler and differentiation give `Aᵀ H = 0`." -/
theorem dependent_of_left_normal_deg_le_one [CharZero K] {n : ℕ}
    (H v : Fin n → MvPolynomial (Fin n) K) {d β : ℕ} (hd : d ≠ 0) (hH : IsHomogMap H d)
    (hv0 : v ≠ 0) (hvh : IsHomogMap v β) (hβ : β ≤ 1) (hv : v ᵥ* jac H = 0) :
    ComponentsDependent H := by
  have h0 := left_normal_dot_eq_zero H v hd hH hv
  have h1 := jac_left_normal_dot_eq_zero H v hd hH hv
  interval_cases β
  · refine ⟨fun i => (v i).coeff 0, ?_, ?_⟩
    · intro hc
      apply hv0
      funext i
      rw [eq_C_of_isHomogeneous_zero (hvh i)]
      simpa using congrFun hc i
    · rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [eq_C_of_isHomogeneous_zero (hvh i)]
      rw [smul_eq_C_mul]
  · have hc : ∀ i j, pderiv j (v i) = C ((pderiv j (v i)).coeff 0) := fun i j =>
      eq_C_of_isHomogeneous_zero ((hvh i).pderiv)
    have hex : ∃ i j, (pderiv j (v i)).coeff 0 ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hv0
      funext i
      have := (hvh i).sum_X_mul_pderiv
      simp only [one_smul] at this
      rw [← this]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hc i j, hne i j]; simp
    obtain ⟨i0, j0, hij⟩ := hex
    refine ⟨fun i => (pderiv j0 (v i)).coeff 0, fun h => hij (congrFun h i0), ?_⟩
    have := congrFun h1 j0
    simp only [vecMul, dotProduct, jac, of_apply, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, ← hc, mul_comm]

/-! ### Ranks over `K(X)` -/

/-- A square matrix over a field with a nonzero left kernel vector is not of full rank
(auxiliary linear algebra for the rank statements of §1.2 and §2 of
`quartic_dependence.pdf`). -/
theorem rank_lt_of_vecMul_eq_zero_field {F : Type*} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (w : Fin n → F) (hw : w ≠ 0) (h : w ᵥ* M = 0) :
    M.rank < n := by
  have hA : (replicateRow (Fin 1) w) * M = 0 := by
    ext i j; simpa [mul_apply, vecMul, dotProduct] using congrFun h j
  have h1 := rank_add_rank_le_card_of_mul_eq_zero hA
  have h2 : (replicateRow (Fin 1) w).rank = 1 := by
    have := LinearIndependent.rank_matrix (M := replicateRow (Fin 1) w) ?_
    · simpa using this
    · rw [linearIndependent_unique_iff]
      intro h0; apply hw; funext j; simpa [Matrix.row] using congrFun h0 j
  simp at h1; omega

/-- A polynomial matrix with a nonzero polynomial left kernel vector has rank `< n` over
`K(X)`.  Used in §4.1 of `quartic_dependence.pdf` (`(Jv)ᵀ H = 0` with `H ≠ 0` bounds the
rank of `Jv`). -/
theorem polyRank_lt_of_vecMul_eq_zero {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) (w : Fin n → MvPolynomial σ K)
    (hw : w ≠ 0) (hN : w ᵥ* N = 0) : polyRank N < n := by
  set f := algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  apply rank_lt_of_vecMul_eq_zero_field _ (fun i => f (w i))
  · intro h; apply hw; funext i
    exact hf (by simpa using congrFun h i)
  · funext j
    have := congrArg f (congrFun hN j)
    simpa [vecMul, dotProduct, map_sum] using this

/-- A nilpotent polynomial matrix is not of full rank over `K(X)`: for `N = JH` nilpotent,
`rank N ≤ 3` (implicit in §1.2 of `quartic_dependence.pdf`, "so we may suppose that
`rank N = 3`"). -/
theorem polyRank_lt_of_isNilpotent {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) (hN : IsNilpotent N) (hn : 0 < n) :
    polyRank N < n := by
  have hdet : N.det = 0 := by
    obtain ⟨k, hk⟩ := hN
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h := congrArg det hk
    rw [det_pow, det_zero] at h
    exact (pow_eq_zero_iff'.mp h).1
  obtain ⟨w, hw, h⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  exact polyRank_lt_of_vecMul_eq_zero N w hw h

/-- A polynomial matrix which is not of full rank over `K(X)` has zero determinant
(auxiliary for §2.1 of `quartic_dependence.pdf`). -/
theorem det_eq_zero_of_polyRank_lt {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) (hr : polyRank N < n) : N.det = 0 := by
  by_contra h
  set f := algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hdet : (N.map f).det ≠ 0 := by
    show (f.mapMatrix N).det ≠ 0
    rw [← RingHom.map_det]; exact fun h' => h (hf (by rw [h', map_zero]))
  have := Matrix.rank_of_isUnit (N.map f) ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet))
  unfold polyRank at hr
  rw [this] at hr; simp at hr

/-! ### Primitive homogeneous kernel generators (§2.1) -/

/-- A singular matrix with homogeneous entries has a nonzero homogeneous polynomial kernel
vector (auxiliary for "For a homogeneous matrix, this generator may be chosen homogeneous",
§2.1 of `quartic_dependence.pdf`). -/
theorem exists_homog_mulVec_eq_zero {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    {d : ℕ} (hN : ∀ i j, (N i j).IsHomogeneous d) (hdet : N.det = 0) :
    ∃ (w : Fin n → MvPolynomial σ K) (k : ℕ), w ≠ 0 ∧ IsHomogMap w k ∧ N *ᵥ w = 0 := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨k, hk⟩ : ∃ k, (fun i => homogeneousComponent k (w i)) ≠ 0 := by
    by_contra hne; push Not at hne
    apply hw0; funext i
    rw [← sum_homogeneousComponent (w i)]
    exact Finset.sum_eq_zero fun k _ => congrFun (hne k) i
  refine ⟨_, k, hk, fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  funext i
  have := congrArg (homogeneousComponent (k + d)) (congrFun hw i)
  simp only [mulVec, dotProduct, map_sum, Pi.zero_apply, map_zero] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [homogeneousComponent_mul_of_isHomogeneous (hN i j)]

/-- Existence of a primitive homogeneous right kernel generator of a singular homogeneous
matrix (auxiliary for §2.1 of `quartic_dependence.pdf`). -/
theorem exists_primRightKernel_of_det {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {d : ℕ}
    (hN : ∀ i j, (N i j).IsHomogeneous d) (hdet : N.det = 0) :
    ∃ u α, IsPrimRightKernel N u α := by
  obtain ⟨w, k, hw0, hwh, hw⟩ := exists_homog_mulVec_eq_zero N hN hdet
  obtain ⟨g, P, c, -, hg0, -, hP, hPp, rfl⟩ := exists_primitive_factorization k w hwh hw0
  refine ⟨P, k - c, ⟨?_, hP, hPp, ?_⟩⟩
  · rintro rfl; exact hw0 (by funext i; simp)
  · funext i
    have := congrFun hw i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
    have h2 : g * ∑ j, N i j * P j = 0 := by
      rw [Finset.mul_sum, ← this]; exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.mp h2).resolve_left hg0

/-- The primitive right normal `u` exists: a homogeneous matrix of non-full rank over `K(X)`
has a primitive homogeneous generator of its right kernel (§2.1 of `quartic_dependence.pdf`:
"A rank-one kernel has a primitive polynomial generator … For a homogeneous matrix, this
generator may be chosen homogeneous"; the vector `u` of §1.2). -/
theorem exists_primRightKernel {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {d : ℕ}
    (hN : ∀ i j, (N i j).IsHomogeneous d) (hr : polyRank N < n) :
    ∃ u α, IsPrimRightKernel N u α :=
  exists_primRightKernel_of_det N hN (det_eq_zero_of_polyRank_lt N hr)

/-- The primitive left normal `v` exists (§2.1 of `quartic_dependence.pdf`; the vector `v`
of §1.2 with `vᵀ N = 0`). -/
theorem exists_primLeftKernel {n : ℕ} {σ : Type*}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {d : ℕ}
    (hN : ∀ i j, (N i j).IsHomogeneous d) (hr : polyRank N < n) :
    ∃ v β, IsPrimLeftKernel N v β := by
  obtain ⟨v, β, h⟩ := exists_primRightKernel_of_det Nᵀ (fun i j => hN j i)
    (by rw [det_transpose]; exact det_eq_zero_of_polyRank_lt N hr)
  exact ⟨v, β, ⟨h.ne_zero, h.homog, h.prim, by rw [← mulVec_transpose]; exact h.ker⟩⟩

/-- The decomposition `H = gP` with `P` primitive, `c = deg g`, `e = deg P = 4 − c`, from the
beginning of §4.1 of `quartic_dependence.pdf` (stated for arbitrary degree `d`). -/
theorem exists_content_factorization {n : ℕ} {σ : Type*} (H : Fin n → MvPolynomial σ K)
    {d : ℕ} (hH : IsHomogMap H d) (h0 : H ≠ 0) :
    ∃ (g : MvPolynomial σ K) (P : Fin n → MvPolynomial σ K) (c : ℕ),
      c ≤ d ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧ IsPrimitiveVec P ∧
        H = fun i => g * P i := by
  obtain ⟨g, P, c, hc, -, hg, hP, hPp, hH⟩ := exists_primitive_factorization d H hH h0
  exact ⟨g, P, c, hc, hg, hP, hPp, hH⟩

/-! ### Descent from an extension field (§2.1) -/

/-- The conclusion descends under field extension: if the components of `H` become linearly
dependent over an extension field `L`, they are already dependent over `K`.  This is the
sentence "The conclusion descends under field extension … We may therefore work over an
algebraic closure" in §2.1 of `quartic_dependence.pdf`, used in the last line of the proof of
Theorem 1.1 (§5.6). -/
theorem componentsDependent_of_map {n : ℕ} {σ : Type*} (L : Type*) [Field L] [Algebra K L]
    (H : Fin n → MvPolynomial σ K)
    (h : ComponentsDependent (fun i => MvPolynomial.map (algebraMap K L) (H i))) :
    ComponentsDependent H := by
  obtain ⟨c, hc, hsum⟩ := h
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    by_contra hne; push Not at hne; exact hc (funext hne)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K L, φ (c i0) ≠ 0 := by
    by_contra hne; push Not at hne
    exact hi0 ((Module.forall_dual_apply_eq_zero_iff K (c i0)).mp hne)
  refine ⟨fun i => φ (c i), fun h0 => hφ (congrFun h0 i0), ?_⟩
  ext m
  have := congrArg (fun p : MvPolynomial σ L => φ (p.coeff m)) hsum
  have hzK : (0 : MvPolynomial σ K).coeff m = 0 := rfl
  have hzL : (0 : MvPolynomial σ L).coeff m = 0 := rfl
  simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, map_sum,
    hzK, hzL, map_zero] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (c i), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-! ### Lemma 2.1, rank at most one -/

/-- If a polynomial matrix has rank at most one over `K(X)`, all its `2 × 2` minors vanish
(auxiliary for Lemma 2.1 of `quartic_dependence.pdf`: "`dFᵢ ∧ dFⱼ = 0`"). -/
theorem minor_eq_zero_of_polyRank_le_one {n : ℕ} {σ : Type*}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    (hr : polyRank M ≤ 1) (i j k l : Fin n) : M i k * M j l = M i l * M j k := by
  set f := algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hsub := rank_submatrix_le (M.map f) ![i, j] ![k, l]
  have hdet : ((M.map f).submatrix ![i, j] ![k, l]).det = 0 := by
    by_contra h
    have h2 : ((M.map f).submatrix ![i, j] ![k, l]).rank = 2 := by
      simpa using rank_of_det_ne_zero h
    have hr' : (M.map f).rank ≤ 1 := hr
    omega
  rw [det_fin_two] at hdet
  simp only [submatrix_apply, map_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  apply hf
  rw [map_mul, map_mul]
  exact sub_eq_zero.mp hdet

/-- **Lemma 2.1 (rank at most one)** of `quartic_dependence.pdf`: "In rank at most one all
nonzero components are proportional."  Here `F` is a homogeneous tuple of degree `d > 0`
with `rank JF ≤ 1`; every component is a constant multiple of any nonzero component.
(The rank-two part of Lemma 2.1 is not needed separately in this formalization; it enters
only through Lemma 2.5(a).) -/
theorem lemma_2_1_rank_le_one [CharZero K] {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) {d : ℕ}
    (hd : 0 < d) (hF : IsHomogMap F d) (hr : polyRank (jac F) ≤ 1) (i j : Fin n)
    (hi : F i ≠ 0) : ∃ c : K, F j = c • F i := by
  apply proportional_of_wronskian (hF i) (hF j) hi
  intro k
  have hmin := fun l => minor_eq_zero_of_polyRank_le_one (jac F) hr i j k l
  simp only [jac, of_apply] at hmin
  have hEi := (hF i).sum_X_mul_pderiv
  have hEj := (hF j).sum_X_mul_pderiv
  have hsum : ∑ l, X l * (pderiv k (F i) * pderiv l (F j) - pderiv l (F i) * pderiv k (F j)) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [hmin l, sub_self, mul_zero]
  have hd' : (d : MvPolynomial (Fin n) K) ≠ 0 := by
    rw [← map_natCast C]; exact fun h => by simp at h; omega
  have : (d : MvPolynomial (Fin n) K) * (F i * pderiv k (F j) - F j * pderiv k (F i)) = 0 := by
    have e1 : ∑ l, X l * (pderiv k (F i) * pderiv l (F j) - pderiv l (F i) * pderiv k (F j)) =
        pderiv k (F i) * ∑ l, X l * pderiv l (F j) -
          pderiv k (F j) * ∑ l, X l * pderiv l (F i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, hEi, hEj, nsmul_eq_mul, nsmul_eq_mul] at hsum
    linear_combination -hsum
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd')

/-- A primitive homogeneous vector `v` of positive degree has `rank Jv ≥ 2`.  This is the
sentence "If `rank Jv ≤ 1`, homogeneity and primitivity would make `v` constant" at the
start of §4.1 of `quartic_dependence.pdf` (a consequence of Lemma 2.1). -/
theorem two_le_polyRank_jac_of_isPrimitiveVec [CharZero K] {n : ℕ}
    (v : Fin n → MvPolynomial (Fin n) K) {β : ℕ} (hβ : 0 < β) (hv0 : v ≠ 0)
    (hvh : IsHomogMap v β) (hvp : IsPrimitiveVec v) : 2 ≤ polyRank (jac v) := by
  by_contra hlt
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hne; push Not at hne; exact hv0 (funext hne)
  have hu : IsUnit (v i) := hvp (v i) fun j => by
    obtain ⟨c, hc⟩ := lemma_2_1_rank_le_one v hβ hvh (by omega) i j hi
    exact ⟨C c, by rw [hc, smul_eq_C_mul, mul_comm]⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have := congrArg totalDegree hw
  rw [totalDegree_mul_of_isDomain hi hw0, (hvh i).totalDegree hi, totalDegree_one] at this
  omega

end DimensionFourDependence
