import DimensionFourDependence.SpanningCoordinates

/-! # Small constant span of a polynomial normal forces component dependence

The components of a normal spanning at most two dimensions over the
original field give either a constant left kernel or the checked
constant-plane normal criterion. No change of source coordinates is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- A polynomial left normal whose component span has dimension at most
two forces a constant relation among homogeneous positive-degree outputs. -/
theorem dependent_of_normal_component_span_le_two
    (H ν : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hν : ν ≠ 0) (hker : ν ᵥ* jac H = 0)
    (hspan : finrank K (Submodule.span K (Set.range ν)) ≤ 2) : ComponentsDependent H := by
  classical
  let U := Submodule.span K (Set.range ν)
  let : Module.Finite K U := Module.Finite.span_of_finite K (Set.finite_range ν)
  let x : Fin n → U := fun i => ⟨ν i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hx : Submodule.span K (Set.range x) = ⊤ := generators_span_subtype_top ν
  have hpos : 0 < finrank K U := by
    by_contra hn
    have hU : U = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    apply hν
    funext i
    have hi : ν i ∈ U := (x i).property
    rw [hU, Submodule.mem_bot] at hi
    exact hi
  have hdim : finrank K U = 1 ∨ finrank K U = 2 := by change finrank K U ≤ 2 at hspan; omega
  rcases hdim with hdim | hdim
  · let b := Module.finBasisOfFinrankEq K U hdim
    let f : MvPolynomial (Fin n) K := (b 0 : U)
    let v : Fin n → K := fun i => b.repr (x i) 0
    have hf : f ≠ 0 := fun hz => b.ne_zero 0 (Subtype.ext hz)
    have hrep (i : Fin n) : ν i = C (v i) * f := by
      simpa [f, v, x, MvPolynomial.smul_eq_C_mul] using
        (congrArg Subtype.val (b.sum_repr (x i))).symm
    have hv : v ≠ 0 := by
      intro hz
      apply hν
      funext i
      rw [hrep, show v i = 0 from congrFun hz i, C_0, zero_mul]
      rfl
    apply dependent_of_constant_left_kernel H hd hH v hv
    funext j
    have he := congrFun hker j
    have hfker : f * (∑ i, C (v i) * pderiv j (H i)) = 0 := by
      calc
        _ = ∑ i, ν i * pderiv j (H i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hrep]
          ring
        _ = 0 := he
    exact (mul_eq_zero.mp hfker).resolve_left hf
  · let b := Module.finBasisOfFinrankEq K U hdim
    let f : MvPolynomial (Fin n) K := (b 0 : U)
    let g : MvPolynomial (Fin n) K := (b 1 : U)
    let v : Fin n → K := fun i => b.repr (x i) 0
    let w : Fin n → K := fun i => b.repr (x i) 1
    have hf : f ≠ 0 := fun hz => b.ne_zero 0 (Subtype.ext hz)
    have hrep (i : Fin n) : ν i = C (v i) * f + C (w i) * g := by
      simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
        MvPolynomial.smul_eq_C_mul] using
        (congrArg Subtype.val (b.sum_repr (x i))).symm
    have hvw : LinearIndependent K ![v, w] := by
      convert basis_coordinate_rows_independent b x hx using 1
      funext j
      fin_cases j <;> rfl
    apply dependent_of_left_normal_in_constant_plane H hd hH v w hvw f g (Or.inl hf)
    have he : (fun i => f * C (v i) + g * C (w i)) = ν := by
      funext i
      rw [hrep]
      ring
    rwa [he]

end DimensionFourDependence
