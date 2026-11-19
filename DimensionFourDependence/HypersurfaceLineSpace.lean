import DimensionFourDependence.LineChartNoetherian
import DimensionFourDependence.LinePairIncidenceMatrix

/-! # The Zariski parameter space of the actual lines on a hypersurface -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module TopologicalSpace
open scoped Topology

universe u
variable {K : Type u} [Field K]

/-- The actual projective lines contained in the hypersurface, with
each two-dimensional subspace represented once. -/
def HypersurfaceLineSpace (R : MvPolynomial (Fin 4) K) :=
  {L : Submodule K (Fin 4 → K) // finrank K L = 2 ∧ ∀ x ∈ L, aeval x R = 0}

/-- A chart on the actual parameter space, using the closed matrix chart
of the original equation in the specified pivot coordinates. -/
def hypersurfaceLineSpaceChart (R : MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (B : hypersurfaceLineChart (rename p.symm R)) : HypersurfaceLineSpace R :=
  ⟨hypersurfaceAtlasLine R ⟨p, B⟩,
    hypersurfaceAtlasLine_finrank R ⟨p, B⟩, hypersurfaceAtlasLine_contained R ⟨p, B⟩⟩

theorem hypersurfaceLineSpaceChart_injective (R : MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4)) :
    Function.Injective (hypersurfaceLineSpaceChart R p) := by
  intro B C h
  apply Subtype.val_injective
  exact lineChartMemberLine_injective p (congrArg Subtype.val h)

theorem hypersurfaceLineSpaceChart_cover [Infinite K] (R : MvPolynomial (Fin 4) K)
    (L : HypersurfaceLineSpace R) : ∃ p B, hypersurfaceLineSpaceChart R p B = L := by
  obtain ⟨⟨p, B⟩, h⟩ := hypersurfaceLineAtlas_covers_all_lines R L.val L.property.1 L.property.2
  exact ⟨p, B, Subtype.ext h⟩

/-- The Zariski topology on the line space, glued from its finite matrix atlas. -/
@[instance_reducible] def hypersurfaceLineSpaceTopology (R : MvPolynomial (Fin 4) K) : TopologicalSpace (HypersurfaceLineSpace R) :=
  ⨆ p : Equiv.Perm (Fin 4), ((graphLineChartTopology K).induced Subtype.val).coinduced (hypersurfaceLineSpaceChart R p)

theorem hypersurfaceLineSpace_isOpen_iff (R : MvPolynomial (Fin 4) K) (U : Set (HypersurfaceLineSpace R)) :
    IsOpen[hypersurfaceLineSpaceTopology R] U ↔ ∀ p : Equiv.Perm (Fin 4),
      IsOpen[(graphLineChartTopology K).induced Subtype.val] (hypersurfaceLineSpaceChart R p ⁻¹' U) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem hypersurfaceLineSpace_noetherian [Infinite K] (R : MvPolynomial (Fin 4) K) :
    letI := hypersurfaceLineSpaceTopology R
    NoetherianSpace (HypersurfaceLineSpace R) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : TopologicalSpace (HypersurfaceLineSpace R) := hypersurfaceLineSpaceTopology R
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  have hS : S = ⋃ p : Equiv.Perm (Fin 4), (hypersurfaceLineSpaceChart R p) ''
      (hypersurfaceLineSpaceChart R p ⁻¹' S) := by
    ext L
    constructor
    · intro hL
      obtain ⟨p, B, rfl⟩ := hypersurfaceLineSpaceChart_cover R L
      exact Set.mem_iUnion.mpr ⟨p, B, hL, rfl⟩
    · intro hL
      obtain ⟨p, B, hB, rfl⟩ := Set.mem_iUnion.mp hL
      exact hB
  rw [hS]
  apply isCompact_iUnion
  intro p
  let : NoetherianSpace (hypersurfaceLineChart (rename p.symm R)) := hypersurfaceLineChart_noetherian _
  apply (NoetherianSpace.isCompact _).image
  apply continuous_def.mpr
  intro U hU
  exact (hypersurfaceLineSpace_isOpen_iff R U).mp hU p

/-- Skewness with each fixed actual line is open throughout the whole
line parameter space, including all changes of coordinate chart. -/
theorem hypersurfaceLineSpace_skew_isOpen [Infinite K] (R : MvPolynomial (Fin 4) K)
    (L : HypersurfaceLineSpace R) :
    IsOpen[hypersurfaceLineSpaceTopology R] {L' | Disjoint L.val L'.val} := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  obtain ⟨p, B, rfl⟩ := hypersurfaceLineSpaceChart_cover R L
  apply (hypersurfaceLineSpace_isOpen_iff R _).mpr
  intro q
  let P : MvPolynomial LineMatrixIndex K := linePairSpecializeLeft B.val (linePairIncidencePolynomial p q)
  have h := (lineChart_principal_isOpen P).preimage
    (continuous_subtype_val (p := fun C => C ∈ hypersurfaceLineChart (rename q.symm R)))
  convert h using 1
  ext C
  change Disjoint (lineChartMemberLine p B.val) (lineChartMemberLine q C.val) ↔ lineChartPolynomialValue C.val P ≠ 0
  dsimp only [P]
  rw [linePairIncidenceMatrix_disjoint_iff_det, linePairSpecializeLeft_eval, linePairIncidencePolynomial_eval (K := K)]

/-- The original Zariski topology on a product of two matrix charts. -/
@[instance_reducible] def linePairMatrixZariskiTopology (K : Type u) [Field K] :
    TopologicalSpace (Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) :=
  TopologicalSpace.generateFrom {U | ∃ P : MvPolynomial LinePairIndex K,
    U = {z | aeval (linePairCoordinates z.1 z.2) P ≠ 0}}

/-- The global pair topology for the algebraic product of the line spaces,
with all eight coordinates on every pair chart. -/
@[instance_reducible] def hypersurfaceLinePairTopology (R S : MvPolynomial (Fin 4) K) :
    TopologicalSpace (HypersurfaceLineSpace R × HypersurfaceLineSpace S) :=
  ⨆ (p : Equiv.Perm (Fin 4)) (q : Equiv.Perm (Fin 4)),
    ((linePairMatrixZariskiTopology K).induced
      (fun (z : hypersurfaceLineChart (rename p.symm R) × hypersurfaceLineChart (rename q.symm S)) =>
        (z.1.val, z.2.val))).coinduced
      (fun z => (hypersurfaceLineSpaceChart R p z.1, hypersurfaceLineSpaceChart S q z.2))

/-- The skew pairs form an open subset in the actual algebraic product
of line parameter spaces. Its complement is the closed incidence relation. -/
theorem hypersurfaceLinePair_skew_isOpen (R S : MvPolynomial (Fin 4) K) :
    IsOpen[hypersurfaceLinePairTopology R S] {z | Disjoint z.1.val z.2.val} := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]
  intro p q
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) := linePairMatrixZariskiTopology K
  let f : hypersurfaceLineChart (rename p.symm R) × hypersurfaceLineChart (rename q.symm S) →
      Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K := fun z => (z.1.val, z.2.val)
  let : TopologicalSpace (hypersurfaceLineChart (rename p.symm R) × hypersurfaceLineChart (rename q.symm S)) :=
    (linePairMatrixZariskiTopology K).induced f
  have h : IsOpen {z : Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K |
      aeval (linePairCoordinates z.1 z.2) (linePairIncidencePolynomial (K := K) p q) ≠ 0} :=
    isOpen_generateFrom_of_mem ⟨linePairIncidencePolynomial p q, rfl⟩
  convert h.preimage (continuous_induced_dom (f := f)) using 1
  ext z
  change Disjoint (lineChartMemberLine p z.1.val) (lineChartMemberLine q z.2.val) ↔
    aeval (linePairCoordinates z.1.val z.2.val) (linePairIncidencePolynomial (K := K) p q) ≠ 0
  rw [linePairIncidenceMatrix_disjoint_iff_det, linePairIncidencePolynomial_eval (K := K)]

end DimensionFourDependence
