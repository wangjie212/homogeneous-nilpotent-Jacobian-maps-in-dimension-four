import DimensionFourDependence.UnramifiedDvrBaseChange

/-! # Rational source orders on the constructed horizontal base change

The inclusion of the source DVR extends to its actual function field in
the fraction field of the coefficient base change. With that constructed
map, the normalized valuations agree on every source rational function.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k A F E : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field F] [Field E]
  [Algebra k A] [Algebra k F] [Algebra k E] [Algebra A F]
  [IsScalarTower k A F] [IsFractionRing A F] [Module.Finite k E]

/-- The actual source fraction field embeds in the fraction field of the
finite coefficient base change, extending the given source local map. -/
noncomputable def relativelyClosedDvrBaseChangeFractionHom
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    F →ₐ[A] FractionRing (A ⊗[k] E) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  exact IsFractionRing.liftAlgHom (g := Algebra.ofId A (FractionRing (A ⊗[k] E)))
    (FaithfulSMul.algebraMap_injective A (FractionRing (A ⊗[k] E)))

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The constructed source field embedding is the existing local map on
every regular source function. -/
theorem relativelyClosedDvrBaseChangeFractionHom_algebraMap
    (hclosed : algebraicClosure k F = ⊥) (a : A) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    relativelyClosedDvrBaseChangeFractionHom (E := E) hclosed (algebraMap A F a) =
      algebraMap A (FractionRing (A ⊗[k] E)) a := by
  exact (relativelyClosedDvrBaseChangeFractionHom (E := E) hclosed).commutes a

/-- Rational functions, and hence rational sections in any chosen local
frame, have unchanged normalized divisor order under the constructed
finite coefficient extension of a horizontal source DVR. -/
theorem relatively_closed_dvr_base_change_rational_valuation
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (A ⊗[k] E))
      [w.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)] (x : F),
      (⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩ :
        IsDedekindDomain.HeightOneSpectrum A).valuation F x =
        w.valuation (FractionRing (A ⊗[k] E))
          (relativelyClosedDvrBaseChangeFractionHom hclosed x) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Module.Finite A (A ⊗[k] E) := hfinite
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  let j := relativelyClosedDvrBaseChangeFractionHom (A := A) (E := E) hclosed
  let : Algebra F (FractionRing (A ⊗[k] E)) := j.toRingHom.toAlgebra
  let : IsScalarTower A F (FractionRing (A ⊗[k] E)) :=
    IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
  intro w hlie x
  exact unramified_divisor_rational_valuation _ w x

end DimensionFourDependence
