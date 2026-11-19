import DimensionFourDependence.GeometricFiberComponents

/-! # Homogeneous pullback for an affine graph hyperplane

The graph of `c + ∑ aᵢxᵢ` embeds projective `n`-space as a hyperplane
in projective `(n+1)`-space. Its pullback preserves homogeneous degree
and has the coordinate inclusion as a right inverse.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L] {n : ℕ}

/-- The homogeneous linear expression for the extra graph coordinate. -/
noncomputable def projectiveGraphLinear (c : L) (a : Fin n → L) : MvPolynomial (Option (Fin n)) L :=
  C c * X none + ∑ i, C (a i) * X (some i)

theorem projectiveGraphLinear_isHomogeneous (c : L) (a : Fin n → L) :
    (projectiveGraphLinear c a).IsHomogeneous 1 := by
  apply (isHomogeneous_C_mul_X c none).add
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X (a i) (some i))

/-- Pullback from the ambient projective space to the graph hyperplane. -/
noncomputable def projectiveGraphPullback (c : L) (a : Fin n → L) :
    MvPolynomial (Option (Fin (n + 1))) L →ₐ[L] MvPolynomial (Option (Fin n)) L :=
  aeval (fun j => j.elim (X none)
    (Fin.snoc (fun i : Fin n => X (some i)) (projectiveGraphLinear c a)))

theorem projectiveGraphPullback_X_none (c : L) (a : Fin n → L) :
    projectiveGraphPullback c a (X none) = X none := by simp [projectiveGraphPullback]

theorem projectiveGraphPullback_X_castSucc (c : L) (a : Fin n → L) (i : Fin n) :
    projectiveGraphPullback c a (X (some i.castSucc)) = X (some i) := by simp [projectiveGraphPullback]

theorem projectiveGraphPullback_X_last (c : L) (a : Fin n → L) :
    projectiveGraphPullback c a (X (some (Fin.last n))) = projectiveGraphLinear c a := by
  simp [projectiveGraphPullback]

/-- Pullback along the graph preserves the specified homogeneous degree. -/
theorem projectiveGraphPullback_isHomogeneous (c : L) (a : Fin n → L)
    {p : MvPolynomial (Option (Fin (n + 1))) L} {d : ℕ} (hp : p.IsHomogeneous d) :
    (projectiveGraphPullback c a p).IsHomogeneous d := by
  have hv : ∀ j : Option (Fin (n + 1)),
      (j.elim (X none) (Fin.snoc (fun i : Fin n => X (some i)) (projectiveGraphLinear c a))).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact isHomogeneous_X _ none
    | some j =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using projectiveGraphLinear_isHomogeneous c a
      · simpa using isHomogeneous_X L (some i)
  simpa only [one_mul, projectiveGraphPullback] using hp.aeval _ hv

/-- Keeping the first homogeneous coordinates is a section of graph pullback. -/
theorem projectiveGraphPullback_rename (c : L) (a : Fin n → L)
    (p : MvPolynomial (Option (Fin n)) L) :
    projectiveGraphPullback c a (rename (Option.map Fin.castSucc) p) = p := by
  have he : (projectiveGraphPullback c a).comp (rename (Option.map Fin.castSucc)) = AlgHom.id L _ := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [projectiveGraphPullback]
  exact DFunLike.congr_fun he p

/-- The graph pullback on one homogeneous polynomial piece. -/
noncomputable def homogeneousGraphPullback (c : L) (a : Fin n → L) (d : ℕ) :
    homogeneousSubmodule (Option (Fin (n + 1))) L d →ₗ[L]
      homogeneousSubmodule (Option (Fin n)) L d where
  toFun p := ⟨projectiveGraphPullback c a p, projectiveGraphPullback_isHomogeneous c a p.property⟩
  map_add' p q := Subtype.ext ((projectiveGraphPullback c a).map_add p q)
  map_smul' r p := Subtype.ext ((projectiveGraphPullback c a).toLinearMap.map_smul r p)

theorem homogeneousGraphPullback_surjective (c : L) (a : Fin n → L) (d : ℕ) :
    Function.Surjective (homogeneousGraphPullback c a d) := by
  intro p
  refine ⟨⟨rename (Option.map Fin.castSucc) (p : MvPolynomial (Option (Fin n)) L),
    p.property.rename_isHomogeneous⟩, ?_⟩
  exact Subtype.ext (projectiveGraphPullback_rename c a p)

variable {F : Type*} [Field F] [Algebra L F]

/-- The actual affine graph point over the coefficient field. -/
noncomputable def affineGraphPoint (c : L) (a : Fin n → L) (x : Fin n → F) : Fin (n + 1) → F :=
  Fin.snoc x (algebraMap L F c + ∑ i, algebraMap L F (a i) * x i)

/-- Evaluation on the graph agrees with evaluation after graph pullback. -/
theorem projectiveGraphPullback_aeval (c : L) (a : Fin n → L) (x : Fin n → F)
    (p : MvPolynomial (Option (Fin (n + 1))) L) :
    aeval (fun j : Option (Fin (n + 1)) => j.elim 1 (affineGraphPoint c a x)) p =
      aeval (fun j : Option (Fin n) => j.elim 1 x) (projectiveGraphPullback c a p) := by
  have he : (aeval (fun j : Option (Fin n) => j.elim 1 x)).comp (projectiveGraphPullback c a) =
      aeval (fun j : Option (Fin (n + 1)) => j.elim 1 (affineGraphPoint c a x)) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp [projectiveGraphPullback]
    | some j =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [projectiveGraphPullback, projectiveGraphLinear, affineGraphPoint]
      · simp [projectiveGraphPullback, affineGraphPoint]
  exact (DFunLike.congr_fun he p).symm

end DimensionFourDependence
