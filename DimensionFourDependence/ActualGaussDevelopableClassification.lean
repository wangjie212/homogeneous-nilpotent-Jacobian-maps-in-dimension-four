import DimensionFourDependence.ActualGaussNormalSpan
import DimensionFourDependence.CharacteristicImageDegreeLowerBound
import DimensionFourDependence.RulingScalarExtensionDensity

/-! # The actual developable image as a cone or tangent developable -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 130000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "D" => rationalParameterDerivative K

omit [CharZero K] in
private theorem normal_ruling_map_point_iff
    {M : Type u} [Field M] [Algebra K M] (e : RatFunc K ≃ₐ[K] M) (n z : Fin 4 → RatFunc K) :
    e ∘ z ∈ LinearMap.ker ((normalRulingMatrix D n).map e).toLin' ↔ z ∈ normalRulingSubspace D n := by
  change ((normalRulingMatrix D n).map e) *ᵥ (e ∘ z) = 0 ↔ normalRulingMatrix D n *ᵥ z = 0
  have he : ((normalRulingMatrix D n).map e) *ᵥ (e ∘ z) = e ∘ (normalRulingMatrix D n *ᵥ z) := by
    funext i
    exact (RingHom.map_mulVec e.toRingHom (normalRulingMatrix D n) z i).symm
  rw [he]
  constructor
  · intro h
    funext i
    exact e.injective ((congrFun h i).trans (map_zero e).symm)
  · intro h
    funext i
    simp only [h, Function.comp_apply, Pi.zero_apply, map_zero]

/-- The complete original image ideal is the ideal of the closure of
the generic Gauss ruling family, evaluated over its rational parameter. -/
theorem actual_image_ideal_eq_generic_gauss_ruling_relations
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hr : polyRank (jac H) = 3) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hLI : LinearIndependent (RatFunc K) (normalCharacteristicMatrix D (gaussParameterNormal H I e)).row)
    (P : R₄) : P ∈ imageRelationIdeal H ↔
      ∀ z ∈ normalRulingSubspace D (gaussParameterNormal H I e), aeval z P = 0 := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let F := FractionRing R₄
  let Q : Fin 4 → F := fun i => algebraMap R₄ F (H i)
  let N := gaussParameterNormal H I e
  let A := actualGaussRulingMatrix H I e
  have hA : Module.finrank M (LinearMap.ker A.toLin') = 2 := actualGaussRulingMatrix_kernel_finrank _ _ _ hLI
  have hQ : A.map (algebraMap M F) *ᵥ Q = 0 := I.output_mem_actual_gauss_ruling H hd hH e
  have hdim := actual_gauss_fiber_output_trdeg_two H hr I hGauss
  have hpart (z : Fin 4 → RatFunc K) : e ∘ z ∈ LinearMap.ker A.toLin' ↔ z ∈ normalRulingSubspace D N :=
    normal_ruling_map_point_iff e N z
  let P₀ := MvPolynomial.map (algebraMap K M) P
  have hEval (z : Fin 4 → RatFunc K) : aeval (e ∘ z) P₀ = e (aeval z P) := by
    change aeval (e ∘ z) (MvPolynomial.map (algebraMap K M) P) = _
    rw [aeval_map_algebra_extension]
    exact (comp_aeval_apply z e.toAlgHom P).symm
  rw [imageRelationIdeal_eq_rational_relations]
  change aeval Q P = 0 ↔ _
  constructor
  · intro hP z hz
    have h₀ : aeval Q P₀ = 0 := (aeval_map_algebra_extension (E := M) P Q).trans hP
    have h₁ := two_dimensional_matrix_kernel_generic_point_density A hA Q hQ hdim P₀ h₀ _ ((hpart z).mpr hz)
    rw [hEval] at h₁
    exact e.injective (h₁.trans (map_zero e).symm)
  · intro hP
    have h₀ (z : Fin 4 → M) (hz : z ∈ LinearMap.ker A.toLin') : aeval z P₀ = 0 := by
      let z₀ := e.symm ∘ z
      have he : e ∘ z₀ = z := funext (fun i => e.apply_symm_apply (z i))
      have hz₀ := (hpart z₀).mp (he.symm ▸ hz)
      rw [← he, hEval, hP z₀ hz₀, map_zero]
    exact (aeval_map_algebra_extension (E := M) P Q).symm.trans
      (two_dimensional_matrix_kernel_vanishing_scalar_extension A hA P₀ h₀ Q hQ)

private theorem span_pair_eq_linear_combinations {L : Type u} [Field L]
    {n : ℕ} (b c : Fin n → L) :
    (Submodule.span L (Set.range ![b, c]) : Set (Fin n → L)) =
      Set.range (fun tu : L × L => tu.1 • b + tu.2 • c) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := L)).mp hz
    exact ⟨(a 0, a 1), by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using ha⟩
  · rintro ⟨tu, rfl⟩
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)

/-- The original nonplanar Gauss-dimension-one image is the closure of
its generic ruling family. A fixed apex lies on every ruling in the
cone case. In the other case the ruling is exactly the tangent to the
nonplanar characteristic curve, and its full tangent-family ideal is
the original image ideal. -/
theorem actual_developable_image_cone_or_tangent_surface
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hr : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let N := gaussParameterNormal H I e
      let W := normalRulingSubspace D N
      Module.finrank (RatFunc K) W = 2 ∧
      (∀ P : R₄, P ∈ imageRelationIdeal H ↔ ∀ z ∈ W, aeval z P = 0) ∧
      ((∃ c : Fin 4 → K, c ≠ 0 ∧ (algebraMap K (RatFunc K) ∘ c) ∈ W ∧
        finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) = 3) ∨
      ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧ b ∈ normalCharacteristicSubspace D N ∧
        LinearIndependent (RatFunc K) ![b, fun i => D (b i)] ∧
        (∀ P : R₄, P ∈ imageRelationIdeal H ↔
          ∀ s t : RatFunc K, aeval (s • b + t • (fun i => D (b i))) P = 0) ∧
        (∀ c : Fin 4 → K, (algebraMap K (RatFunc K) ∘ c) ⬝ᵥ b = 0 → c = 0) ∧
        (∀ n, 3 * n + 1 ≤ projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) b).toIdeal n) ∧
        finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) = 4) := by
  obtain ⟨e, hLI, hcases⟩ := actual_gauss_characteristic_alternative_exact_normal_spans H hd hH hind I hGauss
  have hbound := (normal_ruling_characteristic_subspace_dimensions D (gaussParameterNormal H I e) hLI).1
  have hrel := actual_image_ideal_eq_generic_gauss_ruling_relations H hd hH hr I hGauss e hLI
  refine ⟨e, hbound, hrel, ?_⟩
  rcases hcases with ⟨c, hc, hcN, hspan⟩ | ⟨b, hb, hbN, hpair, hspan, hplanar, _, hspanN⟩
  · exact Or.inl ⟨c, hc, normalCharacteristicSubspace_le_ruling _ _ hcN, hspan⟩
  · refine Or.inr ⟨b, hb, hbN, hpair, ?_, hplanar,
      nonplanar_rational_curve_projective_hilbert_lower_bound b hb hplanar, hspanN⟩
    intro P
    rw [hrel, hspan]
    change (∀ z ∈ (Submodule.span (RatFunc K) (Set.range ![b, fun i => D (b i)]) : Set (Fin 4 → RatFunc K)),
      aeval z P = 0) ↔ _
    rw [span_pair_eq_linear_combinations]
    simp only [Set.forall_mem_range, Prod.forall]

end DimensionFourDependence
