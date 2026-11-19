import DimensionFourDependence.ParabolaFieldEmbedding

/-! # A compatible constant parameter supplies an exact polynomial relation -/

namespace DimensionFourDependence

open MvPolynomial

variable {K F E G sigma : Type*} [Field K] [Field F] [Field E] [Field G]
    [Algebra K E] [Algebra E G]

/-- The exact source fraction equation transports through compatible
field maps to a polynomial cross relation, including denominator zeros. -/
theorem compatible_parameter_fraction_polynomial_relation
    (f : F →+* G)
    (u : MvPolynomial sigma K →+* F) (v : MvPolynomial sigma E →ₐ[E] G)
    (heval : ∀ R : MvPolynomial sigma K, f (u R) = v (MvPolynomial.map (algebraMap K E) R))
    (t : F) (c : E) (hcvalue : algebraMap E G c = f t)
    (p q : MvPolynomial sigma K) (hq : u q ≠ 0) (ht : t = u p / u q) :
    v (MvPolynomial.map (algebraMap K E) p - C c * MvPolynomial.map (algebraMap K E) q) = 0 := by
  have hpq : u p = t * u q := ((eq_div_iff hq).mp ht).symm
  have hc : v (MvPolynomial.map (algebraMap K E) p) =
      algebraMap E G c * v (MvPolynomial.map (algebraMap K E) q) := by
    calc
      v (MvPolynomial.map (algebraMap K E) p) = f (u p) := (heval p).symm
      _ = f (t * u q) := congrArg f hpq
      _ = f t * f (u q) := f.map_mul _ _
      _ = algebraMap E G c * v (MvPolynomial.map (algebraMap K E) q) :=
        congrArg₂ (fun a b : G => a * b) hcvalue.symm (heval q)
  have hC (r : E) : v (C r) = algebraMap E G r := v.commutes r
  simpa only [map_sub, map_mul, hC] using sub_eq_zero.mpr hc

end DimensionFourDependence
