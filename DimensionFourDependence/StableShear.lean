import DimensionFourDependence.Shear

/-! # The auxiliary-coordinate word in equation (6.11)

The identity is proved over every commutative ring, for arbitrary polynomial
parameters. Taking `R = K[z,t]` recovers the point-map factorization of the
five-variable shear. Membership in the tame subgroup, including the
coefficient-ring identification, is not asserted by this module.
-/

namespace DimensionFourDependence.Shear

variable {R : Type*} [CommRing R]

/-- `A₀` in (6.11). -/
def auxA (a b : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![v 0 + b * v 2, v 1 - a * v 2, v 2]

/-- `B₀` in (6.11). -/
def auxB (a b : R) (f : Polynomial R) (v : Fin 3 → R) : Fin 3 → R :=
  ![v 0, v 1, v 2 + f.eval (a * v 0 + b * v 1)]

/-- The stabilized point map `(Ψ,w)`. -/
def stable (a b : R) (f : Polynomial R) (v : Fin 3 → R) : Fin 3 → R :=
  ![v 0 + b * f.eval (a * v 0 + b * v 1),
    v 1 - a * f.eval (a * v 0 + b * v 1), v 2]

theorem auxA_inverse (a b : R) (v : Fin 3 → R) :
    auxA a b (auxA (-a) (-b) v) = v := by
  funext i
  fin_cases i <;> simp [auxA] <;> ring

theorem auxB_inverse (a b : R) (f : Polynomial R) (v : Fin 3 → R) :
    auxB a b f (auxB a b (-f) v) = v := by
  funext i
  fin_cases i <;> simp [auxB]

/-- `A₀` preserves the input of the coefficient polynomial. -/
theorem auxA_preserves (a b : R) (v : Fin 3 → R) :
    a * auxA a b v 0 + b * auxA a b v 1 = a * v 0 + b * v 1 := by
  simp [auxA]
  ring

/-- Equation (6.11), with rightmost factor acting first as specified in the paper. -/
theorem stable_commutator (a b : R) (f : Polynomial R) (v : Fin 3 → R) :
    auxA a b (auxB a b f (auxA (-a) (-b) (auxB a b (-f) v))) =
      stable a b f v := by
  have hInv : ∀ x y w : R, a * (x + -b * w) + b * (y - -a * w) = a * x + b * y := by
    intros
    ring
  funext i
  fin_cases i <;> simp [auxA, auxB, stable, hInv] <;> ring

end DimensionFourDependence.Shear
