import DimensionFourDependence.RationalFrameLocalPredicate
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Positive-power regularity extends actual rational sections on normal schemes -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) [IsIntegral X]

/-- A rational function whose positive power is regular in a normal
stalk is represented by an actual regular section on a neighborhood of
that point, with exactly its original rational value everywhere. -/
theorem normal_stalk_rational_root_local_representative
    (p : X) [IsIntegrallyClosed (X.presheaf.stalk p)]
    (r : X.functionField) {d : ℕ} (hd : 0 < d) (a : X.presheaf.stalk p)
    (hpow : r ^ d = algebraMap (X.presheaf.stalk p) X.functionField a) :
    ∃ (V : X.Opens) (_ : p ∈ V) (s : Γ(X, V)),
      ∀ q : V, schemeRationalSectionFunction X V s q = r := by
  have hi : IsIntegral (X.presheaf.stalk p) (r ^ d) :=
    hpow.symm ▸ isIntegral_algebraMap
  obtain ⟨a', ha'⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hd hi
  obtain ⟨V, hpV, s, hs⟩ := X.presheaf.exists_germ_eq a'
  let s' : Γ(X, V) := s
  let : Nonempty V := ⟨⟨p, hpV⟩⟩
  refine ⟨V, hpV, s', ?_⟩
  intro q
  exact (schemeRationalSectionFunction_eq_generic X V s' q).trans
    ((Scheme.algebraMap_germ_eq_germToFunctionField X hpV s').symm.trans
      ((congrArg (algebraMap (X.presheaf.stalk p) X.functionField) hs).trans ha'))

/-- If a rational numerator's positive power is regular in the
corresponding powered frames, normality makes the numerator regular in
the original actual frames, without assuming local root representatives. -/
theorem rationalFrameRegular_of_positive_power
    (hnormal : ∀ p : X, IsIntegrallyClosed (X.presheaf.stalk p))
    {ι : Type v} (frameOpen : ι → X.Opens) (weight : ι → X.functionField)
    (hweight : ∀ i, weight i ≠ 0)
    {U : X.Opens} (r : X.functionField) {d : ℕ} (hd : 0 < d)
    (hpow : RationalFrameRegular X frameOpen (fun i => weight i ^ d)
      (fun _ : U => r ^ d)) :
    RationalFrameRegular X frameOpen weight (fun _ : U => r) := by
  intro p i hpi
  let : IsIntegrallyClosed (X.presheaf.stalk p.1) := hnormal p.1
  obtain ⟨V, hpV, hVU, hVi, c, hc⟩ := hpow p i hpi
  have hvalue : r ^ d = weight i ^ d * schemeRationalSectionFunction X V c ⟨p.1, hpV⟩ :=
    hc ⟨p.1, hpV⟩
  have hroot : (r / weight i) ^ d =
      algebraMap (X.presheaf.stalk p.1) X.functionField (X.presheaf.germ V p.1 hpV c) := by
    change (r / weight i) ^ d = schemeRationalSectionFunction X V c ⟨p.1, hpV⟩
    rw [div_pow, hvalue]
    field_simp [hweight i]
  obtain ⟨W, hpW, s, hs⟩ := normal_stalk_rational_root_local_representative X p.1
    (r / weight i) hd (X.presheaf.germ V p.1 hpV c) hroot
  refine ⟨W ⊓ V, ⟨hpW, hpV⟩, inf_le_right.trans hVU, inf_le_right.trans hVi,
    X.presheaf.map (Opens.infLELeft W V).op s, ?_⟩
  intro q
  change r = weight i * schemeRationalSectionFunction X (W ⊓ V)
    (X.presheaf.map (Opens.infLELeft W V).op s) q
  rw [schemeRationalSectionFunction_res, hs]
  field_simp [hweight i]

end DimensionFourDependence
