import DimensionFourDependence.CoveringLineFamilyObstructions
import DimensionFourDependence.CoveringLineFamilyDimension

/-! # Three actual skew members of an actual covering line component

The original-field matrix points are a nonempty irreducible family.
Skewness stays open after the actual coordinate permutation. Component
independence excludes a common plane, and Gauss dimension two excludes a
common vertex. Thus each such covering family supplies three pairwise
skew members, also in every prescribed nonempty open subset.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module Topology

variable {K : Type*} [Field K]

/-- Every member of a permuted matrix chart represents a genuine line. -/
theorem lineChartMemberLine_finrank (p : Equiv.Perm (Fin 4))
    (B : Matrix (Fin 2) (Fin 2) K) : finrank K (lineChartMemberLine p B) = 2 := by
  rw [lineChartMemberLine, LinearEquiv.finrank_map_eq, graphLineFour_finrank]

/-- A common coordinate permutation preserves skewness of actual chart lines. -/
theorem lineChartMemberLine_disjoint_iff (p : Equiv.Perm (Fin 4))
    (B D : Matrix (Fin 2) (Fin 2) K) :
    Disjoint (lineChartMemberLine p B) (lineChartMemberLine p D) ↔
      Disjoint (graphLineFour B) (graphLineFour D) := by
  constructor
  · intro h
    apply Submodule.disjoint_def.mpr
    intro x hB hD
    have hz := Submodule.disjoint_def.mp h ((lineCoordinatePermutation p).symm x)
      ⟨x, hB, rfl⟩ ⟨x, hD, rfl⟩
    exact (map_eq_zero_iff (lineCoordinatePermutation (F := K) p).symm
      (lineCoordinatePermutation (F := K) p).symm.injective).mp hz
  · intro h
    exact Submodule.disjoint_map (lineCoordinatePermutation (F := K) p).symm.injective h

/-- Skewness is open on every actual coordinate-permuted chart subfamily. -/
theorem lineChartMemberLine_subfamily_skew_isOpen
    (S : Set (Matrix (Fin 2) (Fin 2) K)) (p : Equiv.Perm (Fin 4)) (B : S) :
    letI := graphLineChartTopology K
    IsOpen {D : S | Disjoint (lineChartMemberLine p B.val) (lineChartMemberLine p D.val)} := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  simpa only [lineChartMemberLine_disjoint_iff] using
    graphLineChart_subfamily_skew_isOpen S B

variable [IsAlgClosed K] [CharZero K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

/-- Each actual covering line component supplies three pairwise skew
members in every nonempty open subset of its actual matrix parameters. -/
theorem covering_line_component_skew_triple_in_open
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2) (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    letI := graphLineChartTopology K
    ∀ (O : Set (lineComponentPoints Q)), IsOpen O → O.Nonempty →
      ∃ a ∈ O, ∃ b ∈ O, ∃ c ∈ O,
        Disjoint (lineChartMemberLine p a.val) (lineChartMemberLine p b.val) ∧
        Disjoint (lineChartMemberLine p a.val) (lineChartMemberLine p c.val) ∧
        Disjoint (lineChartMemberLine p b.val) (lineChartMemberLine p c.val) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : PreirreducibleSpace (lineComponentPoints Q) :=
    Subtype.preirreducibleSpace (lineComponentPoints_isIrreducible Q).isPreirreducible
  intro O hO hOne
  exact noncoplanar_nonconcurrent_irreducible_family_skew_triple
    (fun B : lineComponentPoints Q => lineChartMemberLine p B.val)
    (fun B => lineChartMemberLine_finrank p B.val)
    (fun B => lineChartMemberLine_subfamily_skew_isOpen _ p B)
    (covering_line_component_not_coplanar Q H hind p hk)
    (covering_line_component_not_concurrent Q H hd hH hN hrank I hGauss p heq hk) O hO hOne

/-- Three actual pairwise skew contained lines are obtained from the
actual covering component, with no plane, vertex or irreducibility
obstruction left to assume. -/
theorem covering_line_component_skew_triple
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2) (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    ∃ B ∈ lineComponentPoints Q, ∃ D ∈ lineComponentPoints Q, ∃ T ∈ lineComponentPoints Q,
      Disjoint (lineChartMemberLine p B) (lineChartMemberLine p D) ∧
      Disjoint (lineChartMemberLine p B) (lineChartMemberLine p T) ∧
      Disjoint (lineChartMemberLine p D) (lineChartMemberLine p T) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : Nonempty (lineComponentPoints Q) := (lineComponentPoints_isIrreducible Q).nonempty.to_subtype
  obtain ⟨a, _, b, _, c, _, hab, hac, hbc⟩ :=
    covering_line_component_skew_triple_in_open Q H hd hH hN hrank hind I hGauss p heq hk
      Set.univ isOpen_univ Set.univ_nonempty
  exact ⟨a.val, a.property, b.val, b.property, c.val, c.property, hab, hac, hbc⟩

variable {E : Type*} [Field E] [Algebra K E]

omit [Q.IsPrime] in
/-- An actual generic image line supplies an original-field covering
curve component together with three actual skew members of that component. -/
theorem generic_image_line_exists_covering_component_with_skew_triple
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) :
    ∃ Q ∈ (graphLineEquationIdeal (rename s.1.symm I.equation)).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal ∧
      RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H ∧
      Algebra.trdeg K (FractionRing (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)) = 1 ∧
      ∃ B ∈ lineComponentPoints Q, ∃ D ∈ lineComponentPoints Q, ∃ T ∈ lineComponentPoints Q,
        Disjoint (lineChartMemberLine s.1 B) (lineChartMemberLine s.1 D) ∧
        Disjoint (lineChartMemberLine s.1 B) (lineChartMemberLine s.1 T) ∧
        Disjoint (lineChartMemberLine s.1 D) (lineChartMemberLine s.1 T) := by
  obtain ⟨Q, hQ, hparameter, hk, _, hdim⟩ :=
    generic_image_line_exists_one_dimensional_covering_component H hd hH hrank hind I s hpoint
  let : Q.IsPrime := hQ.isPrime
  exact ⟨Q, hQ, hparameter, hk, hdim,
    covering_line_component_skew_triple Q H hd hH hN hrank hind I hGauss s.1 hQ.le hk⟩

end DimensionFourDependence
