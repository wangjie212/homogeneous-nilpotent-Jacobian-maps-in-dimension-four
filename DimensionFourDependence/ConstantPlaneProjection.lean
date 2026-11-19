import DimensionFourDependence.TwoDirectionNormal

/-! # Constant projections complementary to an independent direction plane -/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K]

/-- The matrix with the two specified direction columns. -/
noncomputable def directionPlaneMatrix (v w : Fin 4 → K) : Matrix (Fin 4) (Fin 2) K :=
  fun i j => ![v, w] j i

/-- Two independent constant directions have a constant left inverse. -/
theorem directionPlaneMatrix_has_left_inverse (v w : Fin 4 → K)
    (hvw : LinearIndependent K ![v, w]) :
    ∃ C : Matrix (Fin 2) (Fin 4) K, C * directionPlaneMatrix v w = 1 := by
  rcases linear_dichotomy (directionPlaneMatrix v w) with ⟨a, ha, hzero⟩ | hC
  · exfalso
    apply ha
    have he : ∑ j : Fin 2, a j • ![v, w] j = 0 := by
      funext i
      have hi := congrFun hzero i
      simpa only [Matrix.mulVec, dotProduct, directionPlaneMatrix, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using hi
    exact funext (Fintype.linearIndependent_iff.mp hvw a he)
  · exact hC

variable {R : Type*} [CommRing R]

/-- The complementary projection determined by a left inverse. -/
noncomputable def directionPlaneProjection (B : Matrix (Fin 4) (Fin 2) R)
    (C : Matrix (Fin 2) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R := 1 - B * C

theorem directionPlaneProjection_mul (B : Matrix (Fin 4) (Fin 2) R)
    (C : Matrix (Fin 2) (Fin 4) R) (hCB : C * B = 1) :
    directionPlaneProjection B C * B = 0 := by
  rw [directionPlaneProjection, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hCB, Matrix.mul_one, sub_self]

theorem directionPlaneProjection_decompose (B : Matrix (Fin 4) (Fin 2) R)
    (C : Matrix (Fin 2) (Fin 4) R) (x : Fin 4 → R) :
    x = directionPlaneProjection B C *ᵥ x + B *ᵥ (C *ᵥ x) := by
  rw [directionPlaneProjection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  abel

/-- A constant complementary projection commutes with extension of coefficients. -/
theorem directionPlaneProjection_map {S : Type*} [CommRing S] (f : R →+* S)
    (B : Matrix (Fin 4) (Fin 2) R) (C : Matrix (Fin 2) (Fin 4) R) :
    (directionPlaneProjection B C).map f = directionPlaneProjection (B.map f) (C.map f) := by
  ext i j
  by_cases hij : i = j <;>
    simp [directionPlaneProjection, Matrix.mul_apply, Matrix.one_apply, hij]

end DimensionFourDependence
