import DimensionFourDependence.FixedLastGeometricFiberValue
import DimensionFourDependence.AffinePlaneCurveElimination
import DimensionFourDependence.TernaryGraphRelationIdeal
import DimensionFourDependence.ComponentSourceAlgebraicity

/-! # Each geometric generic component has a literal affine plane chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 145000

private theorem map_aeval_of_compatible_scalar_maps
    {L E F G : Type u} [Field L] [Field E] [Field F] [Field G] [Algebra L F] [Algebra E G]
    (g : L →+* E) (f : F →+* G)
    (h : ∀ a : L, algebraMap E G (g a) = f (algebraMap L F a))
    {n : ℕ} (x : Fin n → F) (P : MvPolynomial (Fin n) L) :
    aeval (f ∘ x) (MvPolynomial.map g P) = f (aeval x P) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  change _ = f (eval₂ (algebraMap L F) x P)
  rw [MvPolynomial.hom_eval₂, show (algebraMap E G).comp g = f.comp (algebraMap L F) from RingHom.ext h]
  rfl

private theorem coefficient_map_totalDegree_le {L E : Type u} [Field L] [Field E]
    {n : ℕ} (g : L →+* E) (P : MvPolynomial (Fin n) L) :
    (MvPolynomial.map g P).totalDegree ≤ P.totalDegree := by
  unfold totalDegree
  exact Finset.sup_mono (support_map_subset g P)

/-- A faithful affine plane chart of an original coordinate family,
with its full principal relation ideal of degree one or two. -/
structure AffinePlaneCurveChart {E F : Type u} [Field E] [Field F] [Algebra E F] {n : ℕ}
    (y : Fin n → F) where
  projection : Fin 2 ↪ Fin n
  coordinate : Fin n → MvPolynomial (Fin 2) E
  degree_le_one : ∀ i, (coordinate i).totalDegree ≤ 1
  projection_identity : ∀ i, coordinate (projection i) = X i
  coordinate_value : ∀ i, aeval (fun j => y (projection j)) (coordinate i) = y i
  equation : MvPolynomial (Fin 2) E
  equation_irreducible : Irreducible equation
  equation_degree : equation.totalDegree = 1 ∨ equation.totalDegree = 2
  relation_ideal : fiberVanishingIdeal (L := E) (fun j => y (projection j)) = Ideal.span {equation}

variable {K : Type u} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The fixed-coordinate invariants give a genuine affine plane chart
on every geometric component. The equation generates its full ideal
in that plane and has degree one or two. -/
theorem fixed_last_geometric_component_constructs_affine_plane_chart
    (H : Fin 4 → F) (W : FixedLastFiberEquations H) (hN : IsNilpotent (rationalJacobian H))
    (hr : (rationalJacobian H).rank = 3)
    (E : Type u) [Field E] [Algebra (fullOutputField (K := K) H) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := fullOutputField (K := K) H) x)).minimalPrimes) :
    Nonempty (AffinePlaneCurveChart (E := E) (primeQuotientCoordinate P)) := by
  let M := fullOutputField (K := K) H
  let Y := fun i : Fin 3 => H (W.chart i.castSucc)
  let L := coefficientField (K := K) Y
  let T := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let z := primeQuotientCoordinate P
  let : Algebra M L := fullOutputCoefficientAlgebra H hr W.chart W.independent
  let : IsScalarTower M L F := IsScalarTower.of_algebraMap_eq (R := M) (S := L) (A := F) (fun _ => rfl)
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  obtain ⟨f, hf, g, hg⟩ := full_output_independent_chart_geometric_coefficient_embedding H hr W.chart W.independent E P hP
  obtain ⟨p, v, B, hv, hdeg, he, hB, hBd, hz⟩ := affine_plane_restricts_quadric_to_nonzero_binary_equation
    (fun i : Fin 3 => x (W.chart i.castSucc)) W.plane W.quadric W.plane_degree W.quadric_degree
    W.plane_zero W.quadric_zero W.gradients_independent
  let j : Fin 2 ↪ Fin 4 := ⟨fun i => W.chart (p i.castSucc).castSucc,
    W.chart.injective.comp ((Fin.castSucc_injective 3).comp (p.injective.comp (Fin.castSucc_injective 2)))⟩
  let w₀ : Fin 2 → F := fun i => x (j i)
  let w : Fin 2 → T := fun i => z (j i)
  have hW : f.toRingHom ∘ w₀ = w := funext (fun i => hf (j i))
  have hMap (A : MvPolynomial (Fin 2) L) : aeval w (MvPolynomial.map g.toRingHom A) = f (aeval w₀ A) := by
    rw [← hW]
    exact map_aeval_of_compatible_scalar_maps g.toRingHom f.toRingHom hg w₀ A
  let U : Fin 4 → MvPolynomial (Fin 2) E := fun i =>
    Fin.lastCases (C (g W.lastValue)) (fun j => MvPolynomial.map g.toRingHom (v (p.symm j))) (W.chart.symm i)
  have hUlast : U (W.chart (Fin.last 3)) = C (g W.lastValue) := by
    simp only [U, W.chart.symm_apply_apply, Fin.lastCases_last]
  have hUcast (i : Fin 3) : U (W.chart i.castSucc) = MvPolynomial.map g.toRingHom (v (p.symm i)) := by
    simp only [U, W.chart.symm_apply_apply, Fin.lastCases_castSucc]
  have hU (i : Fin 4) : aeval w (U i) = z i := by
    obtain ⟨i, rfl⟩ := W.chart.surjective i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hUlast, aeval_C, hg, W.chart_last]
      exact (congrArg f W.lastValue_eq).trans (hf (Fin.last 3))
    · rw [hUcast, hMap]
      have hi := he (p.symm i)
      change aeval w₀ (v (p.symm i)) = x (W.chart (p (p.symm i)).castSucc) at hi
      rw [p.apply_symm_apply] at hi
      rw [hi, hf]
  have hUdegree (i : Fin 4) : (U i).totalDegree ≤ 1 := by
    obtain ⟨i, rfl⟩ := W.chart.surjective i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hUlast, totalDegree_C]
      omega
    · rw [hUcast]
      exact (coefficient_map_totalDegree_le _ _).trans (hdeg _)
  have hUproj (i : Fin 2) : U (j i) = X i := by
    change U (W.chart (p i.castSucc).castSucc) = _
    rw [hUcast, p.symm_apply_apply, hv, MvPolynomial.map_X]
  have hB₀ : MvPolynomial.map g.toRingHom B ≠ 0 := fun he => hB
    (MvPolynomial.map_injective _ g.injective (he.trans (map_zero _).symm))
  have hBzero : aeval w (MvPolynomial.map g.toRingHom B) = 0 := by
    rw [hMap, show aeval w₀ B = 0 from hz, map_zero]
  let A := IntermediateField.adjoin E (Set.range w)
  have hgen : A = ⊤ := by
    apply top_unique
    rw [← primeQuotientCoordinate_adjoin_eq_top P]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change z i ∈ A
    rw [← hU i]
    have hf (p : MvPolynomial (Fin 2) E) : aeval w p ∈ A := by
      induction p using MvPolynomial.induction_on with
      | C a => simpa only [aeval_C] using A.algebraMap_mem a
      | add p q hp hq => simpa only [map_add] using A.add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, aeval_X]
        exact A.mul_mem hp (IntermediateField.subset_adjoin E _ ⟨i, rfl⟩)
    exact hf (U i)
  have htr : Algebra.trdeg E T ≠ 0 := by
    obtain ⟨u, hu, hku⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
    have hkerY : rationalJacobian Y *ᵥ u = 0 := by
      funext i
      exact congrFun hku (W.chart i.castSucc)
    have htrL := rational_coefficientField_trdeg_eq_one Y W.independent u hu hkerY
    obtain ⟨i, hi⟩ := exists_transcendental_coordinate x (rationalSource_adjoin_coordinates_eq_top L)
      (htrL.trans_ne one_ne_zero)
    have hiM : Transcendental M (x i) := fun h => hi (h.tower_top L)
    have htrE := componentGenericPoint_transcendental x P hP i hiM
    intro h
    let : Algebra.IsAlgebraic E T := trdeg_eq_zero_iff.mp h
    exact htrE (Algebra.IsAlgebraic.isAlgebraic _)
  let J := fiberVanishingIdeal (L := E) w
  have hJ : ¬ J.IsMaximal := fiberVanishingIdeal_not_isMaximal w hgen htr
  obtain ⟨Q, hQ⟩ := prime_height_le_one_exists_generator J (affine_two_prime_height_le_one J hJ)
  have hMem : MvPolynomial.map g.toRingHom B ∈ J := hBzero
  have hQB : Q ∣ MvPolynomial.map g.toRingHom B := Ideal.mem_span_singleton.mp (hQ ▸ hMem)
  have hQ₀ : Q ≠ 0 := fun he => hB₀ (zero_dvd_iff.mp (he ▸ hQB))
  have hQprime : Irreducible Q := ((Ideal.span_singleton_prime hQ₀).mp (hQ ▸ (inferInstance : J.IsPrime))).irreducible
  have hQeval : aeval w Q = 0 := by
    change Q ∈ J
    rw [hQ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hd₀ := totalDegree_pos_of_aeval_zero w Q hQ₀ hQeval
  have hd₂ := (totalDegree_le_of_dvd_of_isDomain hQB hB₀).trans ((coefficient_map_totalDegree_le _ _).trans hBd)
  exact ⟨⟨j, U, hUdegree, hUproj, hU, Q, hQprime, by omega, hQ⟩⟩

end DimensionFourDependence
