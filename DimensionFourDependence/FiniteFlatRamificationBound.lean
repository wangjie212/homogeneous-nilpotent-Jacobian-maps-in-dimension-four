import DimensionFourDependence.Defs
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # Each ramification index is bounded by the finite projection degree

The ramification-inertia identity for a finite flat extension bounds
each local ramification index. This is used for the hyperplane-section
multiplicity bound on a normalized surface via a finite projection.
-/

namespace DimensionFourDependence

variable {A S : Type*} [CommRing A] [IsDomain A]
  [CommRing S] [Algebra A S] [Module.Finite A S] [Module.Flat A S]

/-- Every prime above a fixed source prime has ramification index at
most the rank of the finite flat algebra. -/
theorem finite_flat_ramification_index_le_rank
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx A ≤ Module.finrank A S := by
  classical
  let : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver (S := S) p).fintype
  let Q : p.primesOver S := ⟨q, inferInstance, inferInstance⟩
  have hterm : q.ramificationIdx A * q.inertiaDeg A ≤
      ∑ P : p.primesOver S, P.1.ramificationIdx A * P.1.inertiaDeg A :=
    Finset.single_le_sum (f := fun P : p.primesOver S =>
      P.1.ramificationIdx A * P.1.inertiaDeg A)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
  calc
    q.ramificationIdx A ≤ q.ramificationIdx A * q.inertiaDeg A :=
      Nat.le_mul_of_pos_right _ (q.inertiaDeg_pos A)
    _ ≤ ∑ P : p.primesOver S, P.1.ramificationIdx A * P.1.inertiaDeg A := hterm
    _ = Module.finrank A S := Ideal.sum_ramification_inertia_eq_finrank p S

end DimensionFourDependence
