import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # A point in a locally closed closure has an actual branch specializing to it -/

namespace DimensionFourDependence

open TopologicalSpace

/-- In a Noetherian sober space, a point in the closure of an open
part of a closed set is a specialization of an actual point of that
open part. A generic point of a closed irreducible piece is constructed. -/
theorem locally_closed_closure_constructs_specializing_point
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (U Z : Set X) (hU : IsOpen U) (hZ : IsClosed Z) (z : X)
    (hz : z ∈ closure (U ∩ Z)) :
    ∃ x : X, x ∈ U ∩ Z ∧ x ⤳ z := by
  obtain ⟨C, hCfinite, hCclosed, hCirred, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have he : U ∩ Z = ⋃ T ∈ C, U ∩ T := by
    rw [hcover]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_iUnion]
    aesop
  rw [he, hCfinite.closure_biUnion] at hz
  obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hTC, hzT⟩ := Set.mem_iUnion.mp hT
  have hgen := (hCirred T hTC).isGenericPoint_genericPoint (hCclosed T hTC)
  have hnonempty : (T ∩ U).Nonempty := by
    have hh : (U ∩ T).Nonempty := closure_nonempty_iff.mp ⟨z, hzT⟩
    simpa only [Set.inter_comm] using hh
  have hxU := (hgen.mem_open_set_iff hU).mpr hnonempty
  have hxZ : (hCirred T hTC).genericPoint ∈ Z := by
    rw [hcover]
    exact ⟨T, hTC, hgen.mem⟩
  have hzT' : z ∈ T := closure_minimal Set.inter_subset_right (hCclosed T hTC) hzT
  exact ⟨_, ⟨hxU, hxZ⟩, hgen.specializes hzT'⟩

end DimensionFourDependence
