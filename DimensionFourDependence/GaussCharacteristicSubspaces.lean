import DimensionFourDependence.GaussCurveJetIndependence
import DimensionFourDependence.ImageNormalDerivation

/-! # Actual ruling and characteristic subspaces of the Gauss curve

The first two successive normal covectors define a two-dimensional
kernel; all three define a one-dimensional characteristic kernel.
Differentiating its first two annihilation equations shows that the
derivative of every characteristic vector lies in the ruling kernel.
These actual subspaces and a nonzero characteristic vector are constructed
for the original Gauss curve, without a dimension or independence assumption.
-/

namespace DimensionFourDependence

open Matrix Module

section LinearAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual first two parameter-normal covectors. -/
noncomputable def normalRulingMatrix (D : Derivation K F F) (v : Fin 4 → F) :
    Matrix (Fin 2) (Fin 4) F := fun r i => ![v i, D (v i)] r

/-- The actual first three successive parameter-normal covectors. -/
noncomputable def normalCharacteristicMatrix (D : Derivation K F F) (v : Fin 4 → F) :
    Matrix (Fin 3) (Fin 4) F := fun r i => ![v i, D (v i), D (D (v i))] r

/-- The common kernel of the actual normal and its first derivative. -/
noncomputable def normalRulingSubspace (D : Derivation K F F) (v : Fin 4 → F) :
    Submodule F (Fin 4 → F) := LinearMap.ker (normalRulingMatrix D v).toLin'

/-- The common kernel of the actual normal and its first two derivatives. -/
noncomputable def normalCharacteristicSubspace (D : Derivation K F F) (v : Fin 4 → F) :
    Submodule F (Fin 4 → F) := LinearMap.ker (normalCharacteristicMatrix D v).toLin'

/-- Three independent actual normal covectors give a two-dimensional
ruling subspace and a one-dimensional characteristic subspace. -/
theorem normal_ruling_characteristic_subspace_dimensions
    (D : Derivation K F F) (v : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D v).row) :
    finrank F (normalRulingSubspace D v) = 2 ∧ finrank F (normalCharacteristicSubspace D v) = 1 := by
  have hpair : LinearIndependent F (normalRulingMatrix D v).row := by
    have he := hLI.comp (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)
    convert he using 1
    funext r
    fin_cases r <;> rfl
  have h3 : (normalCharacteristicMatrix D v).rank = 3 := hLI.rank_matrix
  have h2 : (normalRulingMatrix D v).rank = 2 := hpair.rank_matrix
  have he3 := LinearMap.finrank_range_add_finrank_ker (normalCharacteristicMatrix D v).toLin'
  have he2 := LinearMap.finrank_range_add_finrank_ker (normalRulingMatrix D v).toLin'
  have hr3 : finrank F (LinearMap.range (normalCharacteristicMatrix D v).toLin') = 3 := h3
  have hr2 : finrank F (LinearMap.range (normalRulingMatrix D v).toLin') = 2 := h2
  simp only [Module.finrank_pi, Fintype.card_fin] at he3 he2
  change finrank F (LinearMap.ker (normalRulingMatrix D v).toLin') = 2 ∧
    finrank F (LinearMap.ker (normalCharacteristicMatrix D v).toLin') = 1
  omega

/-- Every actual characteristic vector lies in the actual ruling kernel. -/
theorem normalCharacteristicSubspace_le_ruling (D : Derivation K F F) (v : Fin 4 → F) :
    normalCharacteristicSubspace D v ≤ normalRulingSubspace D v := by
  intro b hb
  change normalCharacteristicMatrix D v *ᵥ b = 0 at hb
  change normalRulingMatrix D v *ᵥ b = 0
  funext r
  fin_cases r
  · exact congrFun hb 0
  · exact congrFun hb 1

/-- The actual derivative of a characteristic vector belongs to the
ruling kernel, by differentiating its first two annihilation equations. -/
theorem normal_characteristic_derivative_mem_ruling
    (D : Derivation K F F) (v b : Fin 4 → F) (hb : b ∈ normalCharacteristicSubspace D v) :
    (fun i => D (b i)) ∈ normalRulingSubspace D v := by
  change normalCharacteristicMatrix D v *ᵥ b = 0 at hb
  have h0 : v ⬝ᵥ b = 0 := congrFun hb 0
  have h1 : (fun i => D (v i)) ⬝ᵥ b = 0 := congrFun hb 1
  have h2 : (fun i => D (D (v i))) ⬝ᵥ b = 0 := congrFun hb 2
  have he0 := congrArg D h0
  have he1 := congrArg D h1
  rw [derivation_dotProduct, map_zero, h1, zero_add] at he0
  rw [derivation_dotProduct, map_zero, h2, zero_add] at he1
  change normalRulingMatrix D v *ᵥ (fun i => D (b i)) = 0
  funext r
  fin_cases r
  · exact he0
  · exact he1

/-- Independent actual successive normal covectors construct a
nonzero characteristic vector whose derivative lies in the ruling kernel. -/
theorem exists_normal_characteristic_vector
    (D : Derivation K F F) (v : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D v).row) :
    ∃ b : Fin 4 → F, b ≠ 0 ∧ b ∈ normalCharacteristicSubspace D v ∧
      (fun i => D (b i)) ∈ normalRulingSubspace D v := by
  have hd := (normal_ruling_characteristic_subspace_dimensions D v hLI).2
  obtain ⟨b, hb⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (R := F) (M := normalCharacteristicSubspace D v)).mp (by rw [hd]; omega)
  have hb0 : (b : Fin 4 → F) ≠ 0 := fun hz => hb (Subtype.ext hz)
  exact ⟨b, hb0, b.property, normal_characteristic_derivative_mem_ruling D v b b.property⟩

end LinearAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The original nonplanar homogeneous map with actual Gauss dimension
one supplies its actual two-dimensional ruling kernel, one-dimensional
characteristic kernel, and a nonzero characteristic vector with derivative
in the ruling kernel, over its constructed rational Gauss parameter. -/
theorem actual_gauss_ruling_and_characteristic_subspaces
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w : Fin 4 → RatFunc K := fun i => e.symm (fullOutputCoordinate (K := K)
        (fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I)) i)
      finrank (RatFunc K) (normalRulingSubspace (rationalParameterDerivative K) w) = 2 ∧
      finrank (RatFunc K) (normalCharacteristicSubspace (rationalParameterDerivative K) w) = 1 ∧
      normalCharacteristicSubspace (rationalParameterDerivative K) w ≤ normalRulingSubspace (rationalParameterDerivative K) w ∧
      ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧ b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
        (fun i => rationalParameterDerivative K (b i)) ∈ normalRulingSubspace (rationalParameterDerivative K) w := by
  obtain ⟨e, _, _, _, hLI⟩ := actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  let w : Fin 4 → RatFunc K := fun i => e.symm (fullOutputCoordinate (K := K)
    (fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I)) i)
  have hLI' : LinearIndependent (RatFunc K) (normalCharacteristicMatrix (rationalParameterDerivative K) w).row := hLI
  obtain ⟨hR, hC⟩ := normal_ruling_characteristic_subspace_dimensions (rationalParameterDerivative K) w hLI'
  exact ⟨e, hR, hC, normalCharacteristicSubspace_le_ruling _ _, exists_normal_characteristic_vector _ _ hLI'⟩

end DimensionFourDependence
