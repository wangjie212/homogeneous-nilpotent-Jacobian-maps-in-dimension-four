import DimensionFourDependence.PrimitiveLinearIncidence

/-! # Recovering the linear quotient of a known linear power

For P=L^r M and L(e_j)=1, the quotient coefficients are
M_i=(partial_i P)(e_j)-r L_i P(e_j). An injective coefficient realization
therefore descends the entire linear quotient over arbitrary commutative
rings. A unit pivot is normalized using its inverse inside the original
ring, so no rational coefficient denominator is introduced.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The generic coefficient-linear form retains every coordinate-point value. -/
theorem coefficientLinearForm_eval_coordinate_point (a : Fin n → R) (j : Fin n) :
    MvPolynomial.eval (Pi.single j 1) (coefficientLinearForm a) = a j := by
  classical
  simp [coefficientLinearForm, Pi.single_apply]

/-- Its partial derivative is the corresponding original coefficient. -/
theorem coefficientLinearForm_pderiv (a : Fin n → R) (i : Fin n) :
    pderiv i (coefficientLinearForm a) = C (a i) := by
  classical
  simp [coefficientLinearForm, pderiv_X, Pi.single_apply]

/-- Coefficient realization preserves the full generic linear form. -/
theorem coefficientLinearForm_map (f : R →+* S) (a : Fin n → R) :
    MvPolynomial.map f (coefficientLinearForm a) = coefficientLinearForm (fun i => f (a i)) := by
  simp only [coefficientLinearForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/-- A scalar multiplying every coefficient multiplies the whole linear form. -/
theorem coefficientLinearForm_mul_coefficients (s : R) (a : Fin n → R) :
    coefficientLinearForm (fun i => s * a i) = C s * coefficientLinearForm a := by
  simp only [coefficientLinearForm, map_mul, Finset.mul_sum, mul_assoc]

/-- Ring coefficient realization commutes with evaluation at a coordinate point. -/
theorem coefficient_ring_map_eval_coordinate_point (f : R →+* S)
    (P : MvPolynomial (Fin n) R) (j : Fin n) :
    MvPolynomial.eval (Pi.single j 1) (MvPolynomial.map f P) =
      f (MvPolynomial.eval (Pi.single j 1) P) := by
  classical
  have hs : f ∘ (Pi.single j (1 : R)) = Pi.single j (1 : S) := by
    funext i
    simp [Pi.single_apply]
  simpa only [hs] using (MvPolynomial.map_eval f (Pi.single j 1) P).symm

/-- The exact coordinate-point gradient of L^r M. -/
theorem linear_power_linear_quotient_gradient_value
    (a b : Fin n → R) (r : ℕ) (i j : Fin n) :
    MvPolynomial.eval (Pi.single j 1)
      (pderiv i (coefficientLinearForm a ^ r * coefficientLinearForm b)) =
      (r : R) * a j ^ (r - 1) * a i * b j + a j ^ r * b i := by
  rw [pderiv_mul, pderiv_pow, coefficientLinearForm_pderiv, coefficientLinearForm_pderiv]
  simp only [map_add, map_mul, map_pow, map_natCast, eval_C, coefficientLinearForm_eval_coordinate_point]

/-- With a normalized pivot, the whole quotient linear form and all
its coefficients are recovered in the original coefficient ring. -/
theorem normalized_linear_power_quotient_descends
    (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial (Fin n) R) (a : Fin n → R) (j : Fin n) (hj : a j = 1)
    (r : ℕ) (b : Fin n → S)
    (hP : MvPolynomial.map f P =
      coefficientLinearForm (fun i => f (a i)) ^ r * coefficientLinearForm b) :
    ∃ c : Fin n → R, (∀ i, f (c i) = b i) ∧
      P = coefficientLinearForm a ^ r * coefficientLinearForm c := by
  classical
  let c : Fin n → R := fun i => MvPolynomial.eval (Pi.single j 1) (pderiv i P) -
    (r : R) * a i * MvPolynomial.eval (Pi.single j 1) P
  have hvalue : f (MvPolynomial.eval (Pi.single j 1) P) = b j := by
    rw [← coefficient_ring_map_eval_coordinate_point, hP]
    simp only [map_mul, map_pow, coefficientLinearForm_eval_coordinate_point, hj, map_one, one_pow, one_mul]
  have hgradient (i : Fin n) : f (MvPolynomial.eval (Pi.single j 1) (pderiv i P)) =
      (r : S) * f (a i) * b j + b i := by
    rw [← coefficient_ring_map_eval_coordinate_point, ← pderiv_map, hP,
      linear_power_linear_quotient_gradient_value]
    simp only [hj, map_one, one_pow, mul_one, one_mul]
  have hc (i : Fin n) : f (c i) = b i := by
    simp only [c, map_sub, map_mul, map_natCast, hgradient, hvalue]
    ring
  refine ⟨c, hc, ?_⟩
  apply MvPolynomial.map_injective f hf
  rw [map_mul, map_pow, coefficientLinearForm_map, coefficientLinearForm_map]
  simpa only [hc] using hP

/-- Any unit pivot suffices, so the recovered quotient has coefficients
in the original ring itself. -/
theorem unit_pivot_linear_power_quotient_descends
    (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial (Fin n) R) (a : Fin n → R) (j : Fin n) (hj : IsUnit (a j))
    (r : ℕ) (b : Fin n → S)
    (hP : MvPolynomial.map f P =
      coefficientLinearForm (fun i => f (a i)) ^ r * coefficientLinearForm b) :
    ∃ c : Fin n → R, (∀ i, f (c i) = b i) ∧
      P = coefficientLinearForm a ^ r * coefficientLinearForm c := by
  classical
  obtain ⟨u, hu⟩ := hj
  let a' : Fin n → R := fun i => (↑(u⁻¹) : R) * a i
  have ha' : a' j = 1 := by simp only [a', ← hu, Units.inv_mul]
  have hscaleR : coefficientLinearForm a = C (u : R) * coefficientLinearForm a' := by
    have ha : a = fun i => (u : R) * a' i := by
      funext i
      simp [a', ← mul_assoc]
    exact (congrArg coefficientLinearForm ha).trans (coefficientLinearForm_mul_coefficients _ _)
  have hscaleS : coefficientLinearForm (fun i => f (a i)) =
      C (f (u : R)) * coefficientLinearForm (fun i => f (a' i)) := by
    simpa only [coefficientLinearForm_map, map_mul, MvPolynomial.map_C] using
      congrArg (MvPolynomial.map f) hscaleR
  have hP' : MvPolynomial.map f P = coefficientLinearForm (fun i => f (a' i)) ^ r *
      coefficientLinearForm (fun i => f (u : R) ^ r * b i) := by
    rw [hP, hscaleS, mul_pow, coefficientLinearForm_mul_coefficients, ← map_pow]
    ring
  obtain ⟨c', hc', hPc'⟩ := normalized_linear_power_quotient_descends f hf P a' j ha' r _ hP'
  let c : Fin n → R := fun i => (↑(u⁻¹) : R) ^ r * c' i
  have hc (i : Fin n) : f (c i) = b i := by
    simp only [c, map_mul, map_pow, hc']
    rw [← mul_assoc, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow, one_mul]
  refine ⟨c, hc, ?_⟩
  rw [hPc']
  dsimp only [a', c]
  rw [coefficientLinearForm_mul_coefficients, mul_pow, coefficientLinearForm_mul_coefficients, ← map_pow]
  ring

end DimensionFourDependence
