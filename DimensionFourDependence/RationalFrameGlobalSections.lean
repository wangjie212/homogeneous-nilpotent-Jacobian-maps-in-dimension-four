import DimensionFourDependence.RationalFrameLineBundle

/-! # Actual global line-sheaf sections supply a common rational numerator

The constructed module sheaf's global section is an actual sheaf section.
Its local regular representatives, irreducibility and the frame cover
force one common rational value. The original local frame coefficients
are subsequently derived by regular-section gluing.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- The common rational numerator of an actual global section of the
constructed module sheaf, taken at the actual generic point. -/
noncomputable def rationalFrameGlobalSectionValue
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) : X.functionField :=
  (rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤ s).1 ⟨genericPoint X, trivial⟩

/-- Every pointwise representative of an actual global sheaf section
equals its common original rational numerator. -/
theorem rationalFrameGlobalSectionValue_at_point
    (hcover : iSup frameOpen = ⊤)
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (p : X) :
    (rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤ s).1 ⟨p, trivial⟩ =
      rationalFrameGlobalSectionValue X frameOpen weight s := by
  let f := rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤ s
  have hp : p ∈ iSup frameOpen := by rw [hcover]; trivial
  obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp hp
  obtain ⟨V, hpV, hVtop, _, r, hr⟩ := f.2 ⟨p, trivial⟩ i hpi
  let : Nonempty V := ⟨⟨p, hpV⟩⟩
  have hη : genericPoint X ∈ V :=
    (genericPoint_spec X).mem_open_set_iff V.isOpen |>.mpr (by simpa using (show Nonempty V from inferInstance))
  have hpoint := hr ⟨p, hpV⟩
  have hgeneric := hr ⟨genericPoint X, hη⟩
  rw [schemeRationalSectionFunction_eq_generic] at hpoint hgeneric
  exact hpoint.trans hgeneric.symm

/-- The common rational value faithfully represents actual global
sections, rather than imposing a rational representative as input. -/
theorem rationalFrameGlobalSectionValue_injective
    (hcover : iSup frameOpen = ⊤) :
    Function.Injective (rationalFrameGlobalSectionValue X frameOpen weight) := by
  intro s t hst
  apply (rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤).injective
  apply Subtype.ext
  funext p
  exact (rationalFrameGlobalSectionValue_at_point X frameOpen weight hcover s p.1).trans
    (hst.trans (rationalFrameGlobalSectionValue_at_point X frameOpen weight hcover t p.1).symm)

/-- Every actual global sheaf section supplies its unique actual
regular coefficient on each nonzero frame chart. -/
theorem rationalFrameGlobalSection_existsUnique_coefficient
    (hcover : iSup frameOpen = ⊤)
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤))
    (i : ι) (hi : weight i ≠ 0) :
    ∃! r : Γ(X, frameOpen i), ∀ p : frameOpen i,
      rationalFrameGlobalSectionValue X frameOpen weight s =
        weight i * schemeRationalSectionFunction X (frameOpen i) r p := by
  let f := rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤ s
  have hlocal : RationalFrameRegular X frameOpen weight
      (fun p : frameOpen i => f.1 ⟨p.1, trivial⟩) :=
    rationalFrameRegular_res X frameOpen weight (homOfLE le_top) f.1 f.2
  obtain ⟨r, hr, huniq⟩ := existsUnique_rational_frame_regular_coefficient X frameOpen weight i le_rfl hi
    (fun p : frameOpen i => f.1 ⟨p.1, trivial⟩) hlocal
  refine ⟨r, ?_, ?_⟩
  · intro p
    exact (rationalFrameGlobalSectionValue_at_point X frameOpen weight hcover s p.1).symm.trans (congrFun hr p)
  · intro t ht
    apply huniq
    funext p
    exact (rationalFrameGlobalSectionValue_at_point X frameOpen weight hcover s p.1).trans (ht p)

end DimensionFourDependence
