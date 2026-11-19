import DimensionFourDependence.NilpotentFunctionalTransport

/-! # Faithful invariant matrix realizations and regular specialization preserve nilpotence -/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F] {m n : ℕ}

/-- A faithful rectangular matrix intertwiner transfers nilpotence
from the ambient operator to the constructed invariant operator. -/
theorem matrix_isNilpotent_of_injective_intertwiner
    (A : Matrix (Fin n) (Fin n) F) (B : Matrix (Fin m) (Fin m) F)
    (P : Matrix (Fin n) (Fin m) F) (hP : Function.Injective P.toLin')
    (hcompat : P * B = A * P) (hA : IsNilpotent A) : IsNilpotent B := by
  have hnil : IsNilpotent A.toLin' := by
    obtain ⟨k, hk⟩ := hA
    exact ⟨k, by rw [← Matrix.toLin'_pow, hk]; simp⟩
  have hcomm (v : Fin m → F) : P.toLin' (B.toLin' v) = A.toLin' (P.toLin' v) := by
    change P *ᵥ (B *ᵥ v) = A *ᵥ (P *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcompat]
  obtain ⟨k, hk⟩ := linear_lift_isNilpotent_of_injective A.toLin' B.toLin' P.toLin' hP hcomm hnil
  refine ⟨k, ?_⟩
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_pow, map_zero] using hk

/-- A regular matrix whose faithful generic realization is nilpotent
is nilpotent before specialization and remains so after every specified
ring specialization, including its actual local residue map. -/
theorem matrix_isNilpotent_specialization_of_generic
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* T) (hφ : Function.Injective φ) (σ : R →+* S)
    (M : Matrix (Fin n) (Fin n) R) (hN : IsNilpotent (M.map φ)) :
    IsNilpotent (M.map σ) := by
  have hφM : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) T) := by
    intro A B hAB
    ext i j
    exact hφ (congrFun (congrFun hAB i) j)
  have hreg : IsNilpotent M := by
    obtain ⟨k, hk⟩ := hN
    refine ⟨k, hφM ?_⟩
    rw [map_pow, map_zero]
    exact hk
  exact hreg.map σ.mapMatrix

end DimensionFourDependence
