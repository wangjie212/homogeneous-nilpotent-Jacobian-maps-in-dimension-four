import DimensionFourDependence.CoveringIncidenceAlgebraic
import DimensionFourDependence.OutputCoordinateFieldEquiv
import DimensionFourDependence.GenericLineCoveringComponent

/-! # One-dimensional actual covering line families

The exact image relations identify the generic output field with the
original rank-three image field. Finite geometric generic line fibers
make the incidence field algebraic over that output field. The universal
incidence has two free line coordinates, so its parameter component has
function-field transcendence degree one.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

variable {K : Type*} [Field K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

local notation "ParamRing" => (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)
local notation "IncRing" => MvPolynomial (Fin 2) ParamRing
local notation "IncField" => FractionRing IncRing

/-- The universal line family has two more transcendental coordinates
than its actual quotient parameter ring. -/
theorem componentLineIncidence_trdeg_eq_parameter_add_two :
    Algebra.trdeg K ParamRing + 2 = Algebra.trdeg K IncField := by
  have : Algebra.IsAlgebraic IncRing IncField :=
    IsLocalization.isAlgebraic IncField (nonZeroDivisors IncRing)
  have hfrac := trdeg_add_eq (A := IncField) K IncRing
  rw [show Algebra.trdeg IncRing IncField = 0 from trdeg_eq_zero, add_zero] at hfrac
  have hpoly := trdeg_add_eq (A := IncRing) K ParamRing
  have hp : Algebra.trdeg ParamRing IncRing = 2 := by simp
  rw [hp] at hpoly
  exact hpoly.trans hfrac

/-- Passing to the fraction field of the actual parameter quotient
preserves its transcendence degree over the original field. -/
theorem componentLineParameter_trdeg_fraction :
    Algebra.trdeg K ParamRing = Algebra.trdeg K (FractionRing ParamRing) := by
  have : Algebra.IsAlgebraic ParamRing (FractionRing ParamRing) :=
    IsLocalization.isAlgebraic (FractionRing ParamRing) (nonZeroDivisors ParamRing)
  have he := trdeg_add_eq (A := FractionRing ParamRing) K ParamRing
  simpa only [trdeg_eq_zero, add_zero] using he

variable [CharZero K]

/-- The output field of the actual generic covering incidence has the
same transcendence degree three as the original polynomial image. -/
theorem covering_component_output_field_trdeg_three
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    Algebra.trdeg K (fullOutputField (K := K) (componentLineGenericPoint Q p)) = 3 := by
  have hrel : fiberVanishingIdeal (L := K) (componentLineGenericPoint Q p) =
      fiberVanishingIdeal (L := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) := by
    rw [← imageRelationIdeal_eq_rational_relations]
    ext P
    exact componentLineGenericPoint_relations Q H p hk P
  have he := (outputFieldEquivOfRelations (componentLineGenericPoint Q p)
    (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) hrel).trdeg_eq
  exact he.trans ((polynomialOutputField_trdeg_eq_rank H).trans (by rw [hrank]; norm_num))

/-- The actual universal incidence field of a covering component has
transcendence degree three, derived from the finite generic line fiber. -/
theorem covering_component_incidence_trdeg_three
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    Algebra.trdeg K IncField = 3 := by
  let M := fullOutputField (K := K) (componentLineGenericPoint Q p)
  let : FaithfulSMul K M :=
    (faithfulSMul_iff_algebraMap_injective K M).mpr (algebraMap K M).injective
  let : FaithfulSMul M IncField :=
    (faithfulSMul_iff_algebraMap_injective M IncField).mpr (algebraMap M IncField).injective
  have : Algebra.IsAlgebraic M IncField :=
    covering_component_incidence_isAlgebraic Q H hd hH hrank hind I p heq hk
  have he := trdeg_add_eq (A := IncField) K M
  rw [show Algebra.trdeg M IncField = 0 from trdeg_eq_zero, add_zero] at he
  exact he.symm.trans (covering_component_output_field_trdeg_three Q H hrank p hk)

/-- The actual parameter quotient of a covering line component has
function-field dimension one. No family-dimension assumption is used. -/
theorem covering_line_component_trdeg_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    Algebra.trdeg K (FractionRing ParamRing) = 1 := by
  have he := componentLineIncidence_trdeg_eq_parameter_add_two Q
  rw [covering_component_incidence_trdeg_three Q H hd hH hrank hind I p heq hk] at he
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := K) (S := ParamRing))
  rw [hn] at he
  have hn' : n + 2 = 3 := by exact_mod_cast he
  have hn1 : n = 1 := by omega
  rw [← componentLineParameter_trdeg_fraction Q, hn, hn1]
  rfl

variable {E : Type*} [Field E] [Algebra K E]

omit [Q.IsPrime] in
/-- Every actual line through the generic image point belongs to an
original-field minimal-prime chart component which covers the actual image
and whose parameter function field has dimension exactly one. -/
theorem generic_image_line_exists_one_dimensional_covering_component
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) :
    ∃ Q ∈ (graphLineEquationIdeal (rename s.1.symm I.equation)).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal ∧
      RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H ∧
      closure (Set.range (PrimeSpectrum.comap (componentLineIncidenceHom s.1 Q).toRingHom)) =
        PrimeSpectrum.zeroLocus (imageRelationIdeal H : Set (MvPolynomial (Fin 4) K)) ∧
      Algebra.trdeg K (FractionRing (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)) = 1 := by
  obtain ⟨Q, hQ, hparameter, hk, hclosure⟩ :=
    generic_image_line_exists_covering_chart_component H hrank I s hpoint
  let : Q.IsPrime := hQ.isPrime
  exact ⟨Q, hQ, hparameter, hk, hclosure,
    covering_line_component_trdeg_one Q H hd hH hrank hind I s.1 hQ.le hk⟩

end DimensionFourDependence
