import DimensionFourDependence.HomogeneousRelations

/-! # A nonzero normal covector obtained from an irreducible image relation

Minimality of a homogeneous relation proves both its irreducibility and
nonvanishing of its evaluated gradient. The chain rule then gives the
left normal used in Proposition 2.3 and Sections 3--5.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K σ τ : Type*} [Field K]

/-- A least-degree nonzero homogeneous relation is irreducible. -/
theorem minimal_homogeneous_relation_irreducible (H : σ → MvPolynomial τ K)
    (R : MvPolynomial σ K) {e : ℕ} (hR0 : R ≠ 0) (hRh : R.IsHomogeneous e)
    (hR : aeval H R = 0)
    (hmin : ∀ (S : MvPolynomial σ K) (f : ℕ),
      S ≠ 0 → S.IsHomogeneous f → aeval H S = 0 → e ≤ f) : Irreducible R := by
  constructor
  · intro hu
    have hm := hu.map (aeval H)
    rw [hR] at hm
    exact not_isUnit_zero hm
  · intro a b hab
    have hab0 : a * b ≠ 0 := by rwa [← hab]
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
    obtain ⟨da, hda⟩ := isHomogeneous_of_mul_left (hab ▸ hRh) hab0
    obtain ⟨db, hdb⟩ := isHomogeneous_of_mul_left
      (p := b) (q := a) (by simpa only [mul_comm] using hab ▸ hRh)
      (by simpa only [mul_comm] using hab0)
    have hdeg : da + db = e := (hda.mul hdb).inj_right (hab ▸ hRh) hab0
    have hzero : aeval H a * aeval H b = 0 := by rw [← map_mul, ← hab, hR]
    rcases mul_eq_zero.mp hzero with ha | hb
    · have hle := hmin a da ha0 hda ha
      have hz : db = 0 := by omega
      exact Or.inr (isUnit_of_isHomogeneous_zero (hz ▸ hdb) hb0)
    · have hle := hmin b db hb0 hdb hb
      have hz : da = 0 := by omega
      exact Or.inl (isUnit_of_isHomogeneous_zero (hz ▸ hda) ha0)

/-- A nonzero partial derivative of a minimal relation cannot vanish on the image. -/
theorem minimal_relation_partial_aeval_ne_zero (H : σ → MvPolynomial τ K)
    (R : MvPolynomial σ K) {e : ℕ} (he : 0 < e) (hRh : R.IsHomogeneous e)
    (hmin : ∀ (S : MvPolynomial σ K) (f : ℕ),
      S ≠ 0 → S.IsHomogeneous f → aeval H S = 0 → e ≤ f)
    (i : σ) (hi : pderiv i R ≠ 0) : aeval H (pderiv i R) ≠ 0 := by
  intro hz
  have hle := hmin (pderiv i R) (e - 1) hi hRh.pderiv hz
  omega

/-- The gradient of a target equation evaluated on the polynomial map. -/
noncomputable def imageRelationNormal {n m : ℕ}
    (H : Fin m → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin m) K) :
    Fin m → MvPolynomial (Fin n) K := fun i => aeval H (pderiv i R)

/-- The evaluated gradient of a minimal homogeneous relation is nonzero. -/
theorem minimal_relation_normal_ne_zero [CharZero K] {n m : ℕ}
    (H : Fin m → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin m) K) {e : ℕ}
    (hR0 : R ≠ 0) (he : 0 < e) (hRh : R.IsHomogeneous e)
    (hmin : ∀ (S : MvPolynomial (Fin m) K) (f : ℕ),
      S ≠ 0 → S.IsHomogeneous f → aeval H S = 0 → e ≤ f) :
    imageRelationNormal H R ≠ 0 := by
  intro hzero
  apply hR0
  apply eq_zero_of_forall_pderiv_eq_zero hRh (by omega)
  intro i
  by_contra hi
  apply minimal_relation_partial_aeval_ne_zero H R he hRh hmin i hi
  exact congrFun hzero i

/-- The polynomial chain rule puts the evaluated gradient in the left kernel. -/
theorem imageRelationNormal_left_kernel {n : ℕ}
    (H : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    (hR : aeval H R = 0) : imageRelationNormal H R ᵥ* jac H = 0 := by
  funext j
  have he := congrArg (pderiv j) hR
  rw [pderiv_aeval, map_zero] at he
  exact he

/-- The normal is itself homogeneous in the source variables. -/
theorem imageRelationNormal_homogeneous {n m d e : ℕ}
    (H : Fin m → MvPolynomial (Fin n) K) (hH : IsHomogMap H d)
    (R : MvPolynomial (Fin m) K) (hR : R.IsHomogeneous e) :
    IsHomogMap (imageRelationNormal H R) (d * (e - 1)) :=
  fun i => (hR.pderiv (i := i)).aeval H hH

end DimensionFourDependence
