import DimensionFourDependence.GaussCharacteristicAlternative
import DimensionFourDependence.GaussRulingIncidence
import DimensionFourDependence.MatrixKernelScalarExtension

/-! # A varying actual characteristic curve is nonplanar

A constant hyperplane containing a characteristic curve also contains
its derivative, hence every tangent ruling. Kernel factorization
transfers this relation to the actual image point and then to the
original polynomial map. Component independence therefore excludes
every nonzero original-field hyperplane containing the characteristic.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- An original-field hyperplane containing the actual ruling forces
an actual component relation over the original coefficient field. -/
theorem ImageRelationWitness.dependent_of_ruling_constant_hyperplane
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (c : Fin 4 → K) (hc : c ≠ 0)
    (hplane : ∀ v ∈ normalRulingSubspace (rationalParameterDerivative K) (gaussParameterNormal H I e),
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ v = 0) :
    ComponentsDependent H := by
  let F := FractionRing (MvPolynomial (Fin 4) K)
  let f : RatFunc K →ₐ[K] F := gaussParameterSourceHom H I e
  let : Algebra (RatFunc K) F := f.toRingHom.toAlgebra
  let A := normalRulingMatrix (rationalParameterDerivative K) (gaussParameterNormal H I e)
  let B : Matrix (Fin 1) (Fin 4) (RatFunc K) := fun _ i => algebraMap K (RatFunc K) (c i)
  let Q : Fin 4 → F := fun i => algebraMap (MvPolynomial (Fin 4) K) F (H i)
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin' := by
    intro v hv
    change B *ᵥ v = 0
    funext r
    exact hplane v hv
  have hAQ : A.map (algebraMap (RatFunc K) F) *ᵥ Q = 0 :=
    I.output_mem_parameter_ruling H hd hH e
  have hBQ : B.map (algebraMap (RatFunc K) F) *ᵥ Q = 0 :=
    matrix_kernel_le_after_scalar_extension A B hker hAQ
  have hs : (∑ i, algebraMap K F (c i) * Q i) = 0 := by
    have hh := congrFun hBQ 0
    change (∑ i, f (algebraMap K (RatFunc K) (c i)) * Q i) = 0 at hh
    simpa only [f.commutes] using hh
  refine ⟨c, hc, ?_⟩
  apply IsFractionRing.injective (MvPolynomial (Fin 4) K) F
  rw [map_zero]
  simpa only [map_sum, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] using hs

/-- A characteristic whose actual derivative spans its ruling cannot
lie in any nonzero constant hyperplane for a nonplanar original map. -/
theorem actual_characteristic_tangent_has_no_constant_hyperplane
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (b : Fin 4 → RatFunc K)
    (hspan : normalRulingSubspace (rationalParameterDerivative K) (gaussParameterNormal H I e) =
      Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)])) :
    ∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0 := by
  intro c hc
  by_contra hc0
  apply hind
  apply I.dependent_of_ruling_constant_hyperplane H hd hH e c hc0
  have hcD : (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ
      (fun i => rationalParameterDerivative K (b i)) = 0 :=
    constant_normal_kills_derived_direction (rationalParameterDerivative K) _ b
      (fun i => Derivation.map_algebraMap _ (c i)) hc
  have hker : Submodule.span (RatFunc K)
      (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ≤
      LinearMap.ker ((dotProductBilin (RatFunc K) (RatFunc K))
        (fun i => algebraMap K (RatFunc K) (c i))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hc
    · exact hcD
  intro v hv
  rw [hspan] at hv
  exact hker hv

/-- The constructed characteristic of the actual Gauss curve is a
fixed original-field projective point, or a nonplanar curve whose
actual tangent spans the ruling. -/
theorem actual_gauss_characteristic_constant_or_nonplanar_tangent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w := gaussParameterNormal H I e
      ((∃ c : Fin 4 → K, c ≠ 0 ∧
        (fun i => algebraMap K (RatFunc K) (c i)) ∈
          normalCharacteristicSubspace (rationalParameterDerivative K) w) ∨
      ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧
        b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
        LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)] ∧
        normalRulingSubspace (rationalParameterDerivative K) w =
          Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ∧
        ∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) := by
  obtain ⟨e, b, hb0, hbC, _, halt⟩ :=
    actual_gauss_ruling_constant_vertex_or_characteristic_tangent H hd hH hind I hGauss
  refine ⟨e, ?_⟩
  rcases halt with ⟨c, hc, _, _, _, hcC⟩ | ⟨hpair, hspan⟩
  · exact Or.inl ⟨c, hc, hcC⟩
  · exact Or.inr ⟨b, hb0, hbC, hpair, hspan,
      actual_characteristic_tangent_has_no_constant_hyperplane H hd hH hind I e b hspan⟩

end DimensionFourDependence
