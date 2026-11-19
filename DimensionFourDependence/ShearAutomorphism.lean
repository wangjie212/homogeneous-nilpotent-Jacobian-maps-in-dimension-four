import DimensionFourDependence.ShearSubstitution

/-! # The actual four-variable shear automorphism -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

theorem substitution4_add (a b : MvPolynomial (Fin 2) K)
    (f g : MvPolynomial (Fin 3) K) :
    (substitution4 a b f).comp (substitution4 a b g) = substitution4 a b (f + g) := by
  apply Tame.comp_shear4 (substitution4 a b f) (substitution4 a b g)
    (substitution4 a b (f + g)) (base4 a) (base4 b)
    (parameter4 a b f) (parameter4 a b g)
  · exact substitution4_X a b f
  · exact substitution4_X a b g
  · intro j
    rw [substitution4_X, parameter4_add]
  · exact substitution4_base a b a f
  · exact substitution4_base a b b f
  · exact substitution4_parameter a b f g

theorem substitution4_zero (a b : MvPolynomial (Fin 2) K) :
    substitution4 a b (0 : MvPolynomial (Fin 3) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [substitution4_X]
  fin_cases j <;> simp [parameter4]

/-- The actual automorphism of `K[x,y,z,t]` given in (6.8), with inverse
specified by (6.10). -/
noncomputable def automorphism4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  AlgEquiv.ofAlgHom (substitution4 a b f) (substitution4 a b (-f))
    (by rw [substitution4_add, add_neg_cancel, substitution4_zero])
    (by rw [substitution4_add, neg_add_cancel, substitution4_zero])

theorem automorphism4_X (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) (j : Fin 4) :
    automorphism4 a b f (X j) = X j + perturbation4 a b f j := by
  change substitution4 a b f (X j) = _
  rw [substitution4_X]
  fin_cases j <;> simp [perturbation4, sub_eq_add_neg]

theorem automorphism4_inverse (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (automorphism4 a b f).symm = automorphism4 a b (-f) := by
  ext p
  rfl

end DimensionFourDependence.Shear
