import DimensionFourDependence.Tame

/-! # Adjoining a fixed polynomial coordinate -/

namespace DimensionFourDependence.Tame

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "A" => MvPolynomial (Fin n) R
local notation "B" => MvPolynomial (Fin (n + 1)) R
local notation "ι" => (rename (Fin.castSucc : Fin n → Fin (n + 1)) : A →ₐ[R] B)

/-- Extend an algebra endomorphism by the identity on an additional variable. -/
noncomputable def extendEndomorphism (e : A →ₐ[R] A) : B →ₐ[R] B :=
  aeval (Fin.lastCases (X (Fin.last n)) fun i => ι (e (X i)))

theorem extendEndomorphism_X_castSucc (e : A →ₐ[R] A) (i : Fin n) :
    extendEndomorphism e (X i.castSucc) = ι (e (X i)) := by
  simp only [extendEndomorphism, aeval_X, Fin.lastCases_castSucc]

theorem extendEndomorphism_X_last (e : A →ₐ[R] A) :
    extendEndomorphism e (X (Fin.last n)) = X (Fin.last n) := by
  simp only [extendEndomorphism, aeval_X, Fin.lastCases_last]

theorem extendEndomorphism_comp_rename (e : A →ₐ[R] A) :
    (extendEndomorphism e).comp ι = (ι).comp e := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, rename_X, extendEndomorphism_X_castSucc]

theorem extendEndomorphism_rename (e : A →ₐ[R] A) (p : A) :
    extendEndomorphism e (ι p) = ι (e p) :=
  AlgHom.congr_fun (extendEndomorphism_comp_rename e) p

theorem extendEndomorphism_comp (f g : A →ₐ[R] A) :
    extendEndomorphism (f.comp g) = (extendEndomorphism f).comp (extendEndomorphism g) := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [AlgHom.comp_apply, extendEndomorphism_X_last]
  · simp only [AlgHom.comp_apply, extendEndomorphism_X_castSucc, extendEndomorphism_rename]

theorem extendEndomorphism_id :
    extendEndomorphism (AlgHom.id R A) = AlgHom.id R B := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact extendEndomorphism_X_last _
  · simp only [extendEndomorphism_X_castSucc, AlgHom.id_apply, rename_X]

/-- Stabilization is a group homomorphism because the additional variable
is fixed under both compositions. -/
noncomputable def stabilize : (A ≃ₐ[R] A) →* (B ≃ₐ[R] B) where
  toFun e := AlgEquiv.ofAlgHom (extendEndomorphism e.toAlgHom)
    (extendEndomorphism e.symm.toAlgHom)
    (by rw [← extendEndomorphism_comp, AlgEquiv.comp_symm, extendEndomorphism_id])
    (by rw [← extendEndomorphism_comp, AlgEquiv.symm_comp, extendEndomorphism_id])
  map_one' := by
    apply AlgEquiv.ext
    exact AlgHom.congr_fun extendEndomorphism_id
  map_mul' e f := by
    apply AlgEquiv.ext
    exact AlgHom.congr_fun (extendEndomorphism_comp e.toAlgHom f.toAlgHom)

theorem stabilize_X_last (e : A ≃ₐ[R] A) :
    stabilize e (X (Fin.last n)) = X (Fin.last n) :=
  extendEndomorphism_X_last e.toAlgHom

theorem stabilize_X_castSucc (e : A ≃ₐ[R] A) (i : Fin n) :
    stabilize e (X i.castSucc) = ι (e (X i)) :=
  extendEndomorphism_X_castSucc e.toAlgHom i

theorem stabilize_comp_rename (e : A ≃ₐ[R] A) :
    (stabilize e).toAlgHom.comp ι = (ι).comp e.toAlgHom :=
  extendEndomorphism_comp_rename e.toAlgHom

end DimensionFourDependence.Tame
