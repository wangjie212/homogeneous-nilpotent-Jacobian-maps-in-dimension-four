import DimensionFourDependence.GraphIsotropicNormalForm

/-! # Transporting actual fiber invariants through compatible field embeddings

The source-field embedding and the embedding of its algebraic
coefficient field agree inside the component function field. Hence all
three invariant equations, and their Euler radial data, hold on that
component with coefficients in its constant field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Field G] [Algebra E G]

section

variable (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (f : FractionRing (MvPolynomial (Fin 4) K) →+* G)
    (g : coefficientField (K := K) Y →+* E)
    (hcomp : ∀ l : coefficientField (K := K) Y,
      algebraMap E G (g l) = f (l : FractionRing (MvPolynomial (Fin 4) K)))

include hcomp

omit [CharZero K] in
/-- The selected output coordinates have their actual constant images. -/
theorem coefficientCoordinate_compatible_image (y : Fin 3 → E)
    (hy : ∀ i, algebraMap E G (y i) = f (Y i)) (i : Fin 3) :
    g (coefficientCoordinate (K := K) Y i) = y i := by
  apply (algebraMap E G).injective
  rw [hcomp, coefficientCoordinate_coe, hy]

/-- The first invariant becomes the affine graph equation on the
embedded source point, with its actual coefficient images. -/
theorem firstFiberInvariant_transport
    (p : Equiv.Perm (Fin 4)) (h c : coefficientField (K := K) Y)
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h)
    (x : Fin 4 → G) (hx : ∀ j, f (rationalCoordinate (K := K) j) = x j) :
    x (p 3) = (∑ i : Fin 3, algebraMap E G (g (coefficientPartial Y hY i h)) *
      x (p i.castSucc)) + algebraMap E G (g c) := by
  have he := congrArg f hc
  simp only [firstFiberInvariantInChart, map_sub, map_sum, map_mul, ← hcomp, hx] at he
  linear_combination -he

/-- The second invariant becomes the quadratic equation on the
embedded source point over the constant field. -/
theorem secondFiberInvariant_transport
    (p : Equiv.Perm (Fin 4)) (h c q : coefficientField (K := K) Y)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant p Y hY h c)
    (x : Fin 4 → G) (hx : ∀ j, f (rationalCoordinate (K := K) j) = x j) :
    algebraMap E G (g q) = quadraticExpression
      (fun i => algebraMap E G (g (coefficientPartial Y hY i c)))
      ((coefficientHessian Y hY h).map g |>.map (algebraMap E G))
      (fun i : Fin 3 => x (p i.castSucc)) := by
  have he := congrArg f hq
  simpa only [secondFiberInvariant, quadraticExpression, fiberHessian, coefficientHessian,
    Matrix.of_apply, Matrix.map_apply, map_add, map_sum, map_mul, map_inv₀, map_ofNat,
    ← hcomp, hx] using he

/-- The third invariant becomes the actual cubic polynomial relation
on the embedded source point, including lower-degree degenerations. -/
theorem thirdFiberInvariant_transport
    (p : Equiv.Perm (Fin 4)) (h c q k : coefficientField (K := K) Y)
    (hk : (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant p Y hY h c q)
    (x : Fin 4 → G) (hx : ∀ j, f (rationalCoordinate (K := K) j) = x j) :
    aeval (fun i : Fin 3 => x (p i.castSucc))
      (cubicFiberPolynomial (fun i => g (coefficientPartial Y hY i q))
        ((coefficientHessian Y hY c).map g)
        (fun i j l => g (coefficientCubicTensor Y hY h i j l)) (g k)) = 0 := by
  rw [cubicFiberPolynomial_aeval]
  apply sub_eq_zero.mpr
  have he := congrArg f hk
  simpa only [thirdFiberInvariant, cubicExpression, fiberHessian, fiberThirdDerivative,
    coefficientHessian, coefficientCubicTensor, Matrix.of_apply, Matrix.map_apply,
    map_sub, map_sum, map_mul, map_inv₀, map_ofNat, ← hcomp, hx] using he.symm

omit f hcomp in
/-- The output Euler weights and radial Hessian/cubic identities
transport to the actual constant images under every coefficient embedding. -/
theorem coefficient_radial_data_transport
    (h c r : coefficientField (K := K) Y)
    (hh : coefficientEuler Y hY h = h) (hc : coefficientEuler Y hY c = r * c) :
    g h = (∑ i : Fin 3, g (coefficientPartial Y hY i h) * g (coefficientCoordinate (K := K) Y i)) ∧
      (∑ i : Fin 3, g (coefficientPartial Y hY i c) * g (coefficientCoordinate (K := K) Y i)) = g r * g c ∧
      (∀ j, (∑ i, g (coefficientCoordinate (K := K) Y i) * g (coefficientHessian Y hY h i j)) = 0) ∧
      (∀ j k, (∑ i, g (coefficientCoordinate (K := K) Y i) *
        g (coefficientCubicTensor Y hY h i j k)) = -g (coefficientHessian Y hY h j k)) := by
  have hs (z : coefficientField (K := K) Y) :
      (∑ i : Fin 3, g (coefficientPartial Y hY i z) * g (coefficientCoordinate (K := K) Y i)) =
        g (coefficientEuler Y hY z) := by
    rw [coefficientEuler_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs, hh]
  · rw [hs, hc, map_mul]
  · intro j
    simpa only [map_sum, map_mul, map_zero] using congrArg g (coefficientHessian_radial_contraction Y hY h hh j)
  · intro j k
    simpa only [map_sum, map_mul, map_neg] using congrArg g (coefficientCubicTensor_radial_contraction Y hY h hh j k)

end

end DimensionFourDependence
