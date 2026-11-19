import DimensionFourDependence.CanonicalSourceLocalMap

/-! # Canonical local maps retain equality of their specified source maps -/

namespace DimensionFourDependence

/-- Equal source homomorphisms induce the same canonical local map,
independently of the chosen proofs of prime contraction. -/
theorem canonical_localRingHom_congr
    {R T : Type*} [CommRing R] [CommRing T]
    (Q : Ideal R) [Q.IsPrime] (q : Ideal T) [q.IsPrime]
    (f g : R →+* T) (hf : Q = q.comap f) (hg : Q = q.comap g) (hfg : f = g) :
    Localization.localRingHom Q q f hf = Localization.localRingHom Q q g hg := by
  subst g
  rfl

end DimensionFourDependence
