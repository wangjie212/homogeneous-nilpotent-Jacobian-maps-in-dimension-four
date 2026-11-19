import DimensionFourDependence.ReindexedResidueProjectionBound
import DimensionFourDependence.SelectedProjectionCoordinates
import DimensionFourDependence.CanonicalOriginalChartSectionBound
import DimensionFourDependence.CanonicalProjectionResidueParameter

/-! # The arbitrary original-chart section bound for an actual finite projection

The finite surface projection and actual height-one normalization prime
select their independent residue parameter internally. Reindexing only
the two base variables preserves the original equation and its degree.
The section order bound therefore applies without a chosen residue
parameter, rational scalar action or prescribed projection order.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- An actual finite linear projection of a surface bounds every
original-chart normalized section at its given height-one normalization
prime by the original full-fiber equation degree. The residue parameter,
its ordering, all scalar actions and local base polynomial are derived. -/
theorem canonical_finite_projection_original_section_order_le_degree
    (c : Fin 3 → A) (hc : Algebra.adjoin k (Set.range c) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k))
    (g : MvPolynomial (Option (Fin 2)) k) (hg : g ≠ 0)
    (hfull : g.degreeOf none = g.totalDegree)
    (hroot : aeval (linearProjectionOptionCoordinate T c) g = 0)
    (hfinite : Module.Finite (affineProjectionAlgebra (k := k)
      (linearProjectionOptionCoordinate T c)) A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (x : Fin 4 → FractionRing A) (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i)))
    (b : Localization.AtPrime Q) (hb : b ≠ 0)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    (sectionValue.coefficient (s.symm none) : FractionRing A) =
      algebraMap (Localization.AtPrime Q) (FractionRing A) b → a ≤ g.totalDegree := by
  classical
  let B := Localization.AtPrime Q
  let L := FractionRing A
  let : Algebra B L := normalizationPrimeFractionAlgebra Q
  let : IsFractionRing B L := normalizationPrimeFractionAlgebra_isFractionRing Q
  let : IsScalarTower A B L := normalizationPrimeFractionAlgebra_source_scalarTower Q
  let : IsScalarTower k B L := normalizationPrimeFractionAlgebra_base_scalarTower Q
  let : IsIntegrallyClosed B := normalization_prime_local_isIntegrallyClosed Q
  change (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b → a ≤ g.totalDegree
  intro hvalue
  let y := linearProjectionOptionCoordinate T c
  let φ : A →ₐ[k] L := IsScalarTower.toAlgHom k A L
  have hind : AlgebraicIndependent k (fun i : Fin 2 => y (some i)) :=
    affine_finite_surface_projection_algebraicIndependent y htr hfinite
  obtain ⟨j, hu⟩ := canonical_normalization_finite_projection_transcendental_residue y hfinite htr Q hQ
  let inner := y (some j)
  let outer := y (some (Equiv.swap (0 : Fin 2) j 1))
  have hpair : AlgebraicIndependent k ![inner, outer] := by
    have hs := hind.comp (Equiv.swap (0 : Fin 2) j) (Equiv.swap (0 : Fin 2) j).injective
    change AlgebraicIndependent k (fun i => y (some (Equiv.swap (0 : Fin 2) j i))) at hs
    have heq : (fun i => y (some (Equiv.swap (0 : Fin 2) j i))) = ![inner, outer] := by
      funext i
      fin_cases i <;> simp [inner, outer]
    exact Eq.mp (congrArg (fun f : Fin 2 → A => AlgebraicIndependent k f) heq) hs
  have hp : AlgebraicIndependent k ![algebraMap B L (algebraMap A B inner),
      algebraMap B L (algebraMap A B outer)] := by
    simp only [← IsScalarTower.algebraMap_apply A B L]
    have hm : AlgebraicIndependent k (fun i => φ (![inner, outer] i)) :=
      hpair.map' (f := φ) (IsFractionRing.injective A L)
    have heq : (fun i => φ (![inner, outer] i)) = ![φ inner, φ outer] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp (congrArg (fun f : Fin 2 → L => AlgebraicIndependent k f) heq) hm
  let ρ : Fin 2 ≃ Fin 2 := (Equiv.swap (0 : Fin 2) 1).trans (Equiv.swap (0 : Fin 2) j)
  have hρ0 : ρ 0 = Equiv.swap (0 : Fin 2) j 1 := by simp [ρ]
  have hρ1 : ρ 1 = j := by simp [ρ]
  let g' := renameEquiv k (Equiv.optionCongr ρ).symm g
  have hd := projection_base_reindexed_equation y ρ g hg hfull hroot
  let v := φ (y none)
  have hcoordinates : (fun i => linearProjectionCoordinate T
      (fun l => x (s.symm (some l)) / x (s.symm none)) (projectionCoordinateBaseReindex ρ i)) =
      ![v, φ outer, φ inner] := by
    rw [hratios]
    funext i
    change linearProjectionCoordinate T (fun l => φ (c l)) (projectionCoordinateBaseReindex ρ i) = _
    rw [← linearProjectionCoordinate_algHom T c φ]
    rw [projectionCoordinateBaseReindex_coordinate]
    fin_cases i
    · rfl
    · change φ (y (some (ρ 0))) = φ outer
      rw [hρ0]
    · change φ (y (some (ρ 1))) = φ inner
      rw [hρ1]
  have hvalues : (fun i => φ (y (Equiv.optionCongr ρ i))) =
      (fun i : Option (Fin 2) => i.elim v (fun l => ![φ outer, φ inner] l)) := by
    funext i
    cases i with
    | none => rfl
    | some l =>
      fin_cases l
      · change φ (y (some (ρ 0))) = φ outer
        rw [hρ0]
      · change φ (y (some (ρ 1))) = φ inner
        rw [hρ1]
  have hmap : φ.comp (aeval (fun i => y (Equiv.optionCongr ρ i))) =
      aeval (fun i => φ (y (Equiv.optionCongr ρ i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hrootL : aeval (fun i : Option (Fin 2) => i.elim v
      (fun l => ![φ outer, φ inner] l)) g' = 0 := by
    rw [← hvalues, ← AlgHom.congr_fun hmap g']
    change φ (aeval (fun i => y (Equiv.optionCongr ρ i)) g') = 0
    rw [hd.2.2.2, map_zero]
  have hfield : IntermediateField.adjoin k
      (Set.range (fun i => x (s.symm (some i)) / x (s.symm none))) = ⊤ := by
    rw [hratios]
    exact fraction_field_adjoin_original_coordinates c hc
  have hcoordinates' : (fun i => linearProjectionCoordinate T
      (fun l => x (s.symm (some l)) / x (s.symm none)) (projectionCoordinateBaseReindex ρ i)) =
      ![v, algebraMap B L (algebraMap A B outer), algebraMap B L (algebraMap A B inner)] := by
    change (fun i => linearProjectionCoordinate T
      (fun l => x (s.symm (some l)) / x (s.symm none)) (projectionCoordinateBaseReindex ρ i)) =
      ![v, algebraMap A L outer, algebraMap A L inner] at hcoordinates
    simpa only [← IsScalarTower.algebraMap_apply A B L] using hcoordinates
  have hrootL' : aeval (fun i : Option (Fin 2) => i.elim v
      (fun l => ![algebraMap B L (algebraMap A B outer),
        algebraMap B L (algebraMap A B inner)] l)) g' = 0 := by
    change aeval (fun i : Option (Fin 2) => i.elim v
      (fun l => ![algebraMap A L outer, algebraMap A L inner] l)) g' = 0 at hrootL
    simpa only [← IsScalarTower.algebraMap_apply A B L] using hrootL
  exact (original_chart_reindexed_residue_projection_section_order_le_hypersurface_degree
    (normalization_prime_local_maximalIdeal_ne_bot Q hQ)
    (algebraMap A B inner) (algebraMap A B outer) hu hp x sectionValue s hbase hfield
    T (projectionCoordinateBaseReindex ρ) v hcoordinates' g' hd.1 hd.2.2.1 hrootL'
    b hb hvalue a horder).trans_eq hd.2.1

end DimensionFourDependence
