import DimensionFourDependence.AffineChartStalkNaturality

/-! # Actual affine stalks in specified coordinate rings

An affine section-coordinate isomorphism identifies the actual stalk
with the specified coordinate prime localization, preserving section
germs. Source-map compatibility on those germs determines the complete
map on the actual stalk.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual stalk of an affine open in its specified original
coordinate ring, at the specified original coordinate prime. -/
noncomputable def affineOpenCoordinateStalkEquiv
    {X : Scheme.{u}} (U : X.affineOpens) (R : CommRingCat.{u})
    (e : Γ(X, U.1) ≃+* R) (x : U.1) (Q : PrimeSpectrum R)
    (hQ : (U.2.primeIdealOf x).asIdeal = Q.asIdeal.comap e.toRingHom) :
    X.presheaf.stalk x.1 ≃+* Localization.AtPrime Q.asIdeal := by
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x.1) :=
    X.presheaf.algebra_section_stalk x
  let : IsLocalization.AtPrime (X.presheaf.stalk x.1) (U.2.primeIdealOf x).asIdeal :=
    U.2.isLocalization_stalk x
  exact (IsLocalization.algEquiv (U.2.primeIdealOf x).asIdeal.primeCompl
    (X.presheaf.stalk x.1) (Localization.AtPrime (U.2.primeIdealOf x).asIdeal)).toRingEquiv.trans
      (Localization.localRingEquiv (U.2.primeIdealOf x).asIdeal Q.asIdeal e hQ)

/-- The specified stalk coordinates send every actual section germ
to the localization of its original coordinate value. -/
theorem affineOpenCoordinateStalkEquiv_germ
    {X : Scheme.{u}} (U : X.affineOpens) (R : CommRingCat.{u})
    (e : Γ(X, U.1) ≃+* R) (x : U.1) (Q : PrimeSpectrum R)
    (hQ : (U.2.primeIdealOf x).asIdeal = Q.asIdeal.comap e.toRingHom)
    (r : Γ(X, U.1)) :
    affineOpenCoordinateStalkEquiv U R e x Q hQ
        (X.presheaf.germ U.1 x.1 x.2 r) =
      algebraMap R (Localization.AtPrime Q.asIdeal) (e r) := by
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x.1) :=
    X.presheaf.algebra_section_stalk x
  let : IsLocalization.AtPrime (X.presheaf.stalk x.1) (U.2.primeIdealOf x).asIdeal :=
    U.2.isLocalization_stalk x
  change Localization.localRingHom (U.2.primeIdealOf x).asIdeal Q.asIdeal e.toRingHom hQ
    ((IsLocalization.algEquiv (U.2.primeIdealOf x).asIdeal.primeCompl
      (X.presheaf.stalk x.1) (Localization.AtPrime (U.2.primeIdealOf x).asIdeal))
        (algebraMap Γ(X, U.1) (X.presheaf.stalk x.1) r)) = _
  rw [AlgEquiv.commutes, Localization.localRingHom_to_map]
  rfl

/-- Compatibility with every section germ identifies the entire
actual geometric stalk map with the specified canonical local map. -/
theorem affineOpenCoordinateStalkEquiv_stalkMap
    {X Y : Scheme.{u}} (U : X.affineOpens) (R B : CommRingCat.{u})
    (e : Γ(X, U.1) ≃+* R) (f : Y ⟶ X) (y : Y) (hy : f y ∈ U.1)
    (Q : PrimeSpectrum R) (q : PrimeSpectrum B)
    (hQ : (U.2.primeIdealOf ⟨f y, hy⟩).asIdeal = Q.asIdeal.comap e.toRingHom)
    (ψ : R →+* B) (hψ : Q.asIdeal = q.asIdeal.comap ψ)
    (b : Y.presheaf.stalk y ≃+* Localization.AtPrime q.asIdeal)
    (h : ∀ r : Γ(X, U.1),
      b (f.stalkMap y (X.presheaf.germ U.1 (f y) hy r)) =
        algebraMap B (Localization.AtPrime q.asIdeal) (ψ (e r)))
    (z : X.presheaf.stalk (f y)) :
    b (f.stalkMap y z) = Localization.localRingHom Q.asIdeal q.asIdeal ψ hψ
      (affineOpenCoordinateStalkEquiv U R e ⟨f y, hy⟩ Q hQ z) := by
  let : Algebra Γ(X, U.1) (X.presheaf.stalk (f y)) :=
    X.presheaf.algebra_section_stalk ⟨f y, hy⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (f y))
      (U.2.primeIdealOf ⟨f y, hy⟩).asIdeal := U.2.isLocalization_stalk ⟨f y, hy⟩
  have heq : b.toRingHom.comp (f.stalkMap y).hom =
      (Localization.localRingHom Q.asIdeal q.asIdeal ψ hψ).comp
        (affineOpenCoordinateStalkEquiv U R e ⟨f y, hy⟩ Q hQ).toRingHom := by
    apply IsLocalization.ringHom_ext (U.2.primeIdealOf ⟨f y, hy⟩).asIdeal.primeCompl
    ext r
    change b (f.stalkMap y (X.presheaf.germ U.1 (f y) hy r)) =
      Localization.localRingHom Q.asIdeal q.asIdeal ψ hψ
        (affineOpenCoordinateStalkEquiv U R e ⟨f y, hy⟩ Q hQ
          (X.presheaf.germ U.1 (f y) hy r))
    rw [affineOpenCoordinateStalkEquiv_germ, Localization.localRingHom_to_map]
    exact h r
  exact RingHom.congr_fun heq z

end DimensionFourDependence
