import DimensionFourDependence.MatrixKernelDescent
import DimensionFourDependence.NowhereZeroCollinearPolynomialVector

/-! # A primitive direction along an actual rank-three polynomial line is constant -/

namespace DimensionFourDependence

open Matrix Module

variable {E G : Type*} [Field E] [IsAlgClosed E] [Field G] [Algebra E G]

/-- A nowhere-zero polynomial kernel vector on a line is a constant
multiple of its direction when the actual Jacobian has rank three. -/
theorem polynomial_line_rank_three_kernel_nowhere_zero_constant
    (A : Matrix (Fin 4) (Fin 4) (Polynomial E)) (U : Fin 4 → Polynomial E)
    (v : Fin 4 → E) (hv : v ≠ 0) (t : G) (ht : Transcendental E t)
    (hrank : (A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G)).rank = 3)
    (hAv : A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G) *ᵥ
      (fun i => algebraMap E G (v i)) = 0)
    (hAU : A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G) *ᵥ
      (fun i => Polynomial.aeval t (U i)) = 0)
    (hnozero : ∀ s : E, (fun i => (U i).eval s) ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ ∀ i, U i = Polynomial.C (c * v i) := by
  have hvG : (fun i => algebraMap E G (v i)) ≠ 0 := by
    intro hz
    apply hv
    funext i
    apply (algebraMap E G).injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hz i
  let w : LinearMap.ker (A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G)).toLin' :=
    ⟨(fun i => algebraMap E G (v i)), hAv⟩
  have hw : w ≠ 0 := fun hz => hvG (congrArg Subtype.val hz)
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp
    (rank_three_matrix_kernel_finrank _ hrank) ⟨(fun i => Polynomial.aeval t (U i)), hAU⟩
  have hrep (i : Fin 4) : Polynomial.aeval t (U i) = r * algebraMap E G (v i) :=
    (congrFun (congrArg Subtype.val hr) i).symm
  apply nowhere_zero_collinear_polynomial_vector_constant U v hv _ hnozero
  intro i j
  apply (transcendental_iff_injective.mp ht)
  simp only [map_mul, Polynomial.aeval_C]
  rw [hrep, hrep]
  ring

end DimensionFourDependence
