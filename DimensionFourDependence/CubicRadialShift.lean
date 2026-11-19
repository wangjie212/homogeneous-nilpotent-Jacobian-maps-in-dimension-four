import DimensionFourDependence.HomogeneousResidueSpecialization

/-! # Removing a radial shift from an isotropic cubic direction

The radial identities in Section 3.2 imply that the cubic self-value of
`Z+lambda Y` equals that of `Z` whenever `Z` is Hessian-isotropic.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F] {n : ℕ}

/-- Trilinear contraction of a third derivative coefficient tensor. -/
noncomputable def tensorTrilinearPairing (C : Fin n → Fin n → Fin n → F)
    (x y z : Fin n → F) : F := ∑ i, ∑ j, ∑ k, C i j k * x i * y j * z k

theorem tensorTrilinearPairing_add_left (C : Fin n → Fin n → Fin n → F) (x x' y z : Fin n → F) :
    tensorTrilinearPairing C (fun i => x i + x' i) y z =
      tensorTrilinearPairing C x y z + tensorTrilinearPairing C x' y z := by
  simp only [tensorTrilinearPairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem tensorTrilinearPairing_add_middle (C : Fin n → Fin n → Fin n → F) (x y y' z : Fin n → F) :
    tensorTrilinearPairing C x (fun i => y i + y' i) z =
      tensorTrilinearPairing C x y z + tensorTrilinearPairing C x y' z := by
  simp only [tensorTrilinearPairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem tensorTrilinearPairing_add_right (C : Fin n → Fin n → Fin n → F) (x y z z' : Fin n → F) :
    tensorTrilinearPairing C x y (fun i => z i + z' i) =
      tensorTrilinearPairing C x y z + tensorTrilinearPairing C x y z' := by
  simp only [tensorTrilinearPairing, mul_add, Finset.sum_add_distrib]

theorem tensorTrilinearPairing_scale_left (C : Fin n → Fin n → Fin n → F) (x y z : Fin n → F) (r : F) :
    tensorTrilinearPairing C (fun i => r * x i) y z = r * tensorTrilinearPairing C x y z := by
  simp only [tensorTrilinearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tensorTrilinearPairing_scale_middle (C : Fin n → Fin n → Fin n → F) (x y z : Fin n → F) (r : F) :
    tensorTrilinearPairing C x (fun i => r * y i) z = r * tensorTrilinearPairing C x y z := by
  simp only [tensorTrilinearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tensorTrilinearPairing_scale_right (C : Fin n → Fin n → Fin n → F) (x y z : Fin n → F) (r : F) :
    tensorTrilinearPairing C x y (fun i => r * z i) = r * tensorTrilinearPairing C x y z := by
  simp only [tensorTrilinearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tensorTrilinearPairing_swap12 (C : Fin n → Fin n → Fin n → F)
    (hC : ∀ i j k, C i j k = C j i k) (x y z : Fin n → F) :
    tensorTrilinearPairing C x y z = tensorTrilinearPairing C y x z := by
  unfold tensorTrilinearPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hC j i k]
  ring

theorem tensorTrilinearPairing_swap23 (C : Fin n → Fin n → Fin n → F)
    (hC : ∀ i j k, C i j k = C i k j) (x y z : Fin n → F) :
    tensorTrilinearPairing C x y z = tensorTrilinearPairing C x z y := by
  unfold tensorTrilinearPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hC i k j]
  ring

/-- Euler's radial identities remove every radial cross term of the
cubic on the isotropic plane spanned by `Y` and `Z`. -/
theorem symmetric_cubic_radial_shift
    (T : Matrix (Fin n) (Fin n) F) (C : Fin n → Fin n → Fin n → F)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (Y Z : Fin n → F)
    (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hCY : ∀ v w, tensorTrilinearPairing C Y v w = -matrixBilinearPairing T v w)
    (hZ : matrixBilinearPairing T Z Z = 0) (r : F) :
    tensorTrilinearPairing C (fun i => Z i + r * Y i)
      (fun i => Z i + r * Y i) (fun i => Z i + r * Y i) = tensorTrilinearPairing C Z Z Z := by
  have hYZZ : tensorTrilinearPairing C Y Z Z = 0 := by rw [hCY, hZ, neg_zero]
  have hYYZ : tensorTrilinearPairing C Y Y Z = 0 := by rw [hCY, hY, neg_zero]
  have hYYY : tensorTrilinearPairing C Y Y Y = 0 := by rw [hCY, hY, neg_zero]
  have hZYZ : tensorTrilinearPairing C Z Y Z = 0 :=
    (tensorTrilinearPairing_swap12 C h12 Z Y Z).trans hYZZ
  have hZZY : tensorTrilinearPairing C Z Z Y = 0 :=
    (tensorTrilinearPairing_swap23 C h23 Z Z Y).trans hZYZ
  have hYZY : tensorTrilinearPairing C Y Z Y = 0 :=
    (tensorTrilinearPairing_swap23 C h23 Y Z Y).trans hYYZ
  have hZYY : tensorTrilinearPairing C Z Y Y = 0 :=
    (tensorTrilinearPairing_swap12 C h12 Z Y Y).trans hYZY
  simp only [tensorTrilinearPairing_add_left, tensorTrilinearPairing_add_middle,
    tensorTrilinearPairing_add_right, tensorTrilinearPairing_scale_left,
    tensorTrilinearPairing_scale_middle, tensorTrilinearPairing_scale_right,
    hYZZ, hYYZ, hYYY, hZYZ, hZZY, hYZY, hZYY, mul_zero, add_zero]

end DimensionFourDependence
