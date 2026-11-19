import DimensionFourDependence.ClosedGaussPencilDegreeBound
import DimensionFourDependence.ClosedGaussCoordinateIntegrality
import DimensionFourDependence.GenericSourcePencilKernel

/-! # The actual closed Gauss pencil is geometrically integral

The reduced homogeneous equation generates the whole original-coordinate
relation ideal over the actual closed parameter field. Its quotient is
therefore exactly the checked coordinate algebra. Every algebraic
coefficient extension, including an algebraic closure, preserves its
integrality. The equation has the actual positive pencil degree.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual homogeneous pencil equation over the actual relatively
closed Gauss parameter field, in the original four source variables. -/
noncomputable def closedGaussPencilEquation
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) :
    MvPolynomial (Fin 4) (closedGaussParameterField H I) :=
  MvPolynomial.map e.toRingHom (genericSourcePencilEquation p q)

omit [CharZero K] in
/-- The equation is literally the original homogeneous pencil `p - t q`
with the covering parameter as its coefficient. -/
theorem closedGaussPencilEquation_eq
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) :
    closedGaussPencilEquation H I e p q =
      MvPolynomial.map (algebraMap K (closedGaussParameterField H I)) p -
        C (e RatFunc.X) * MvPolynomial.map (algebraMap K (closedGaussParameterField H I)) q := by
  have hc : e.toRingHom.comp (algebraMap K (RatFunc K)) =
      algebraMap K (closedGaussParameterField H I) := by
    apply RingHom.ext
    intro k
    exact e.commutes k
  simp only [closedGaussPencilEquation, genericSourcePencilEquation, map_sub, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_map, hc]
  rfl

omit [CharZero K] in
/-- All exact source relations over the closed Gauss field are generated
by the actual single reduced pencil equation. -/
theorem actual_closed_gauss_pencil_relation_ideal
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q) :
    fiberVanishingIdeal (L := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4)) =
        Ideal.span {closedGaussPencilEquation H I e p q} := by
  let E := MvPolynomial.mapEquiv (Fin 4) e.toRingEquiv
  ext P
  let P0 := E.symm P
  have hP : E P0 = P := E.apply_symm_apply P
  have heval : MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (rationalCoordinate (K := K) (n := 4)) P0 =
      aeval (rationalCoordinate (K := K) (n := 4)) P := by
    rw [← hP]
    change _ = MvPolynomial.eval₂ (algebraMap (closedGaussParameterField H I) F)
      (rationalCoordinate (K := K) (n := 4)) (MvPolynomial.map e.toRingHom P0)
    rw [eval₂_map]
    rfl
  have hdiv : E (genericSourcePencilEquation p q) ∣ P ↔ genericSourcePencilEquation p q ∣ P0 := by
    constructor
    · intro h
      simpa only [RingEquiv.symm_apply_apply] using map_dvd E.symm h
    · intro h
      simpa only [hP] using map_dvd E h
  change aeval (rationalCoordinate (K := K) (n := 4)) P = 0 ↔ _
  rw [Ideal.mem_span_singleton, ← heval,
    ← genericSourcePencilEquation_dvd_iff_evaluation_zero p q hq hrel _ ht P0]
  exact hdiv.symm

omit [CharZero K] in
/-- The actual pencil is nonzero and has exactly the common homogeneous
source degree of its reduced numerator and denominator. -/
theorem actual_closed_gauss_pencil_homogeneous_degree
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) {D : ℕ} (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) :
    closedGaussPencilEquation H I e p q ≠ 0 ∧
      (closedGaussPencilEquation H I e p q).IsHomogeneous D ∧
      (closedGaussPencilEquation H I e p q).totalDegree = D := by
  have hn : closedGaussPencilEquation H I e p q ≠ 0 := by
    have hi := MvPolynomial.map_injective (σ := Fin 4) e.toRingHom e.injective
    exact fun hz => genericSourcePencilEquation_ne_zero p q hq hrel
      (hi (hz.trans (map_zero _).symm))
  have hh : (closedGaussPencilEquation H I e p q).IsHomogeneous D :=
    (genericSourcePencilEquation_isHomogeneous p q hpH hqH).map e.toRingHom
  exact ⟨hn, hh, hh.totalDegree hn⟩

/-- The actual generic homogeneous pencil stays an integral hypersurface
after every algebraic coefficient extension, in particular over an
algebraic closure of the actual closed Gauss parameter field. -/
theorem actual_closed_gauss_pencil_geometrically_integral
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q)
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    IsDomain (MvPolynomial (Fin 4) E ⧸ Ideal.span
      {MvPolynomial.map (algebraMap (closedGaussParameterField H I) E)
        (closedGaussPencilEquation H I e p q)}) := by
  let C := closedGaussParameterField H I
  let J := fiberVanishingIdeal (L := C) (rationalCoordinate (K := K) (n := 4))
  let : IsDomain ((MvPolynomial (Fin 4) C ⧸ J) ⊗[C] E) :=
    actual_closed_gauss_coordinate_quotient_algebraic_base_change_isDomain H I E
  let c := Algebra.TensorProduct.comm C E (MvPolynomial (Fin 4) C ⧸ J)
  let : IsDomain (E ⊗[C] (MvPolynomial (Fin 4) C ⧸ J)) :=
    Function.Injective.isDomain c c.injective
  let b := polynomialQuotientBaseChangeEquiv E J
  have hJ : extendCoefficientIdeal E J = Ideal.span
      {MvPolynomial.map (algebraMap C E) (closedGaussPencilEquation H I e p q)} := by
    rw [show J = Ideal.span {closedGaussPencilEquation H I e p q} from
      actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht]
    simp only [extendCoefficientIdeal, Ideal.map_span, Set.image_singleton]
  rw [← hJ]
  exact Function.Injective.isDomain b.symm b.symm.injective

/-- The actual pencil quotient is the actual original-source coordinate
algebra, with its natural algebra structure over the closed Gauss field. -/
noncomputable def closedGaussPencilCoordinateEquiv
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q) :
    (MvPolynomial (Fin 4) (closedGaussParameterField H I) ⧸
      Ideal.span {closedGaussPencilEquation H I e p q}) ≃ₐ[closedGaussParameterField H I]
        closedGaussCoordinateAlgebra H I := by
  rw [← actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht]
  exact fiberCoordinateQuotientEquiv (L := closedGaussParameterField H I) _

/-- The actual generic pencil has the original rational source field
as its fraction field over the actual closed parameter field. -/
noncomputable def closedGaussPencilFractionEquiv
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q) :
    FractionRing (MvPolynomial (Fin 4) (closedGaussParameterField H I) ⧸
      Ideal.span {closedGaussPencilEquation H I e p q}) ≃ₐ[closedGaussParameterField H I] F := by
  rw [← actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht]
  exact closedGaussCoordinateQuotientFractionEquiv H I

/-- The actual nonzero homogeneous generic pencil equation remains
irreducible over every algebraic extension of the closed parameter field. -/
theorem actual_closed_gauss_pencil_geometrically_irreducible
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R) {D : ℕ} (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q)
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    Irreducible (MvPolynomial.map (algebraMap (closedGaussParameterField H I) E)
      (closedGaussPencilEquation H I e p q)) := by
  have hn := (actual_closed_gauss_pencil_homogeneous_degree H I e p q hq hrel hpH hqH).1
  have hi := MvPolynomial.map_injective (σ := Fin 4)
    (algebraMap (closedGaussParameterField H I) E) (algebraMap (closedGaussParameterField H I) E).injective
  have hnE : MvPolynomial.map (algebraMap (closedGaussParameterField H I) E)
      (closedGaussPencilEquation H I e p q) ≠ 0 :=
    fun hz => hn (hi (hz.trans (map_zero _).symm))
  exact ((Ideal.span_singleton_prime hnE).mp ((Ideal.Quotient.isDomain_iff_prime _).mp
    (actual_closed_gauss_pencil_geometrically_integral H I e p q hq hrel ht E))).irreducible

end DimensionFourDependence
