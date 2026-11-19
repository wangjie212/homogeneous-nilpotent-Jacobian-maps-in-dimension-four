import DimensionFourDependence.GeometricCoefficientRealization

/-! # The isotropic normal form from realized actual coefficients

A realization of the actual invariants transports the Euler radial
identities. A rank-two hypothesis only on the original coefficient
Hessian then constructs the full-source isotropic quadratic normal form.
-/

namespace DimensionFourDependence

open Matrix

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]

section

variable {p : Equiv.Perm (Fin 4)}
    {Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)} {hY : AlgebraicIndependent K Y}
    {h c q k : coefficientField (K := K) Y} {x : Fin 4 → G} {y : Fin 4 → E}
    (R : FiberCoefficientRealization p Y hY h c q k x y)

/-- A realization carries the actual Euler and radial tensor data
to the component's constant field and its actual generic output value. -/
theorem FiberCoefficientRealization.radial_data
    (θ : K) (hh : coefficientEuler Y hY h = h)
    (hc : coefficientEuler Y hY c = algebraMap K (coefficientField (K := K) Y) θ * c) :
    y (p 3) = (∑ i : Fin 3, R.coefficientMap (coefficientPartial Y hY i h) * y (p i.castSucc)) ∧
      (∑ i : Fin 3, R.coefficientMap (coefficientPartial Y hY i c) * y (p i.castSucc)) =
        algebraMap K E θ * R.coefficientMap c ∧
      (∀ j, (∑ i : Fin 3, y (p i.castSucc) * R.coefficientMap (coefficientHessian Y hY h i j)) = 0) ∧
      (∀ j l, (∑ i : Fin 3, y (p i.castSucc) * R.coefficientMap (coefficientCubicTensor Y hY h i j l)) =
        -R.coefficientMap (coefficientHessian Y hY h j l)) := by
  have hd := coefficient_radial_data_transport Y hY R.coefficientMap h c
    (algebraMap K (coefficientField (K := K) Y) θ) hh hc
  simpa only [R.coordinate_image, R.last_output_image, R.scalar_image] using hd

variable [CharZero E] [IsAlgClosed E]

/-- Construct the normal-form coordinates from the actual realized
invariant equations and the rank-two coefficient Hessian. No normal-form,
direction, mapped-rank or parameter hypothesis remains. -/
theorem FiberCoefficientRealization.exists_isotropic_normal_form
    (θ : K) (hh : coefficientEuler Y hY h = h)
    (hc : coefficientEuler Y hY c = algebraMap K (coefficientField (K := K) Y) θ * c)
    (hrank : (coefficientHessian Y hY h).rank = 2) :
    let T := (coefficientHessian Y hY h).map R.coefficientMap
    let a : Fin 3 → E := fun i => R.coefficientMap (coefficientPartial Y hY i c)
    ∃ (Z W : Fin 4 → E) (τ s t : G),
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => Z (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => W (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) ≠ 0 ∧
      LinearIndependent E ![(fun i : Fin 3 => y (p i.castSucc)),
        (fun i : Fin 3 => Z (p i.castSucc)), (fun i : Fin 3 => W (p i.castSucc))] ∧
      (∀ j, x j = τ * algebraMap E G (y j) + s * algebraMap E G (Z j) +
        t * algebraMap E G (W j) + algebraMap E G ((Pi.single (p 3) (R.coefficientMap c) : Fin 4 → E) j)) ∧
      algebraMap E G (R.coefficientMap q) = algebraMap E G (algebraMap K E θ) *
        algebraMap E G (R.coefficientMap c) * τ +
        algebraMap E G (∑ i : Fin 3, a i * Z (p i.castSucc)) * s +
        algebraMap E G (∑ i : Fin 3, a i * W (p i.castSucc)) * t +
        algebraMap E G (matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc))
          (fun i : Fin 3 => W (p i.castSucc))) * s * t := by
  let L := coefficientField (K := K) Y
  let : Algebra L E := R.coefficientMap.toAlgebra
  let T := (coefficientHessian Y hY h).map R.coefficientMap
  let a : Fin 3 → E := fun i => R.coefficientMap (coefficientPartial Y hY i c)
  obtain ⟨Z₀, W₀, hZ, hW, hκ, _⟩ := coefficientHessian_exists_isotropic_basis_over Y hY h hh hrank E
  change matrixBilinearPairing T Z₀ Z₀ = 0 at hZ
  change matrixBilinearPairing T W₀ W₀ = 0 at hW
  change matrixBilinearPairing T Z₀ W₀ ≠ 0 at hκ
  have hT (i j : Fin 3) : T i j = T j i :=
    congrArg R.coefficientMap (coefficientHessian_symmetric Y hY h i j)
  have hy0 : (fun i : Fin 3 => y (p i.castSucc)) ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    have he : R.coefficientMap (coefficientCoordinate (K := K) Y 0) = 0 :=
      (R.coordinate_image 0).trans (congrFun hz 0)
    have hzero : coefficientCoordinate (K := K) Y 0 = 0 := R.coefficientMap.injective
      (by simpa only [map_zero] using he)
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun z : L => (z : FractionRing (MvPolynomial (Fin 4) K))) hzero
  obtain ⟨hLast, hWeight, hRad, _⟩ := R.radial_data θ hh hc
  exact graph_isotropic_quadratic_normal_form_of_directions p x y
    (fun i => R.coefficientMap (coefficientPartial Y hY i h)) a T hT Z₀ W₀ hZ hW hκ hy0
    hRad (algebraMap K E θ) (R.coefficientMap c) (R.coefficientMap q)
    hLast R.graph_equation hWeight R.quadratic_equation

end

end DimensionFourDependence
