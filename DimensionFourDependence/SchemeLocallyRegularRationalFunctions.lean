import DimensionFourDependence.SchemeRationalSectionFunctions

/-! # Actual local regular representatives glue to a unique regular scheme section -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (X : Scheme.{u}) [IsIntegral X]

/-- Actual pointwise rational values distinguish regular sections on
every open, including the empty open. -/
theorem schemeRationalSectionFunction_injective_all (U : X.Opens) :
    Function.Injective (schemeRationalSectionFunction X U) := by
  intro r s hrs
  apply TopCat.Presheaf.section_ext X.sheaf U r s
  intro p hp
  apply IsFractionRing.injective (X.presheaf.stalk p) X.functionField
  exact congrFun hrs ⟨p, hp⟩

/-- Local regular representatives of a rational-valued coefficient
glue to a unique actual structure-sheaf section, with the same values.
The construction handles empty opens and has no gluing assumption. -/
theorem existsUnique_regular_section_of_local_rational_values
    (U : X.Opens) (f : U → X.functionField)
    (hf : ∀ p : U, ∃ (V : X.Opens) (_ : p.1 ∈ V) (hVU : V ≤ U)
      (r : Γ(X, V)), ∀ q : V,
        f ⟨q.1, hVU q.2⟩ = schemeRationalSectionFunction X V r q) :
    ∃! r : Γ(X, U), schemeRationalSectionFunction X U r = f := by
  classical
  choose V hpV hVU r hr using hf
  have hcover : U ≤ iSup V := by
    intro p hp
    exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf V r := by
    intro p q
    apply schemeRationalSectionFunction_injective_all X (V p ⊓ V q)
    funext t
    rw [schemeRationalSectionFunction_res, schemeRationalSectionFunction_res]
    exact (hr p ⟨t.1, t.2.1⟩).symm.trans (hr q ⟨t.1, t.2.2⟩)
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' V U (fun p => homOfLE (hVU p)) hcover r hcompatible
  let s' : Γ(X, U) := s
  have hs' (p : U) : X.presheaf.map (homOfLE (hVU p)).op s' = r p := hs p
  have hvalue : schemeRationalSectionFunction X U s' = f := by
    funext p
    have h := congrArg (fun a : Γ(X, V p) =>
      schemeRationalSectionFunction X (V p) a ⟨p.1, hpV p⟩) (hs' p)
    exact (schemeRationalSectionFunction_res X (homOfLE (hVU p)) s'
      ⟨p.1, hpV p⟩).symm.trans (h.trans (hr p ⟨p.1, hpV p⟩).symm)
  refine ⟨s', hvalue, ?_⟩
  intro t ht
  exact schemeRationalSectionFunction_injective_all X U (ht.trans hvalue.symm)

end DimensionFourDependence
