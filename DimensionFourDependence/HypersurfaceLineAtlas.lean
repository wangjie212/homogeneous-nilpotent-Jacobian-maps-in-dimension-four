import DimensionFourDependence.GraphLineEquations
import DimensionFourDependence.LineChartCoverage

/-! # A finite chart atlas for all lines on the hypersurface

Coordinate permutations of the explicit closed matrix charts parametrize
every two-dimensional line contained in a given equation over an infinite
field. The atlas may represent the same line in multiple charts. Gluing,
covering irreducible components and incidence dimensions are not asserted here.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F]

/-- Renaming the equation compensates for a coordinate permutation of its point. -/
theorem line_coordinate_rename_aeval (p : Equiv.Perm (Fin 4))
    (x : Fin 4 → F) (R : MvPolynomial (Fin 4) F) :
    aeval (lineCoordinatePermutation p x) (rename p.symm R) = aeval x R := by
  rw [aeval_rename]
  have he : (lineCoordinatePermutation p x) ∘ p.symm = x := by
    funext i
    simp [lineCoordinatePermutation]
  rw [he]

/-- Every line on the hypersurface occurs in one of the closed polynomial charts. -/
theorem hypersurface_line_exists_chart [Infinite F]
    (R : MvPolynomial (Fin 4) F) (L : Submodule F (Fin 4 → F))
    (hL : finrank F L = 2) (hR : ∀ x ∈ L, aeval x R = 0) :
    ∃ (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) F),
      L.map (lineCoordinatePermutation p).toLinearMap = graphLineFour B ∧
      B ∈ hypersurfaceLineChart (rename p.symm R) := by
  obtain ⟨p, B, hmap⟩ := projective_line_exists_graph_chart L hL
  refine ⟨p, B, hmap, (hypersurfaceLineChart_mem_iff_line_contained _ _).mpr ?_⟩
  intro y hy
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (line_coordinate_rename_aeval p x R).trans (hR x hx)

/-- The atlas of the hypersurface's lines, retaining its finite coordinate-chart index. -/
def hypersurfaceLineAtlas (R : MvPolynomial (Fin 4) F) : Type _ :=
  (p : Equiv.Perm (Fin 4)) × {B : Matrix (Fin 2) (Fin 2) F //
    B ∈ hypersurfaceLineChart (rename p.symm R)}

/-- The actual four-coordinate line represented by a chart point. -/
def hypersurfaceAtlasLine (R : MvPolynomial (Fin 4) F) (s : hypersurfaceLineAtlas R) :
    Submodule F (Fin 4 → F) :=
  (graphLineFour s.2.val).map (lineCoordinatePermutation (F := F) s.1).symm.toLinearMap

/-- Every point in the atlas represents a genuine projective line. -/
theorem hypersurfaceAtlasLine_finrank (R : MvPolynomial (Fin 4) F) (s : hypersurfaceLineAtlas R) :
    finrank F (hypersurfaceAtlasLine R s) = 2 := by
  rw [hypersurfaceAtlasLine, LinearEquiv.finrank_map_eq, graphLineFour_finrank]

/-- Every represented line is contained in the original hypersurface equation. -/
theorem hypersurfaceAtlasLine_contained (R : MvPolynomial (Fin 4) F) (s : hypersurfaceLineAtlas R) :
    ∀ x ∈ hypersurfaceAtlasLine R s, aeval x R = 0 := by
  rintro x ⟨y, hy, rfl⟩
  have he := hypersurfaceLineChart_line_contained (rename s.1.symm R) s.2.val s.2.property y hy
  rw [aeval_rename] at he
  exact he

/-- The chart atlas covers every line on the hypersurface in its original coordinates. -/
theorem hypersurfaceLineAtlas_covers_all_lines [Infinite F]
    (R : MvPolynomial (Fin 4) F) (L : Submodule F (Fin 4 → F))
    (hL : finrank F L = 2) (hR : ∀ x ∈ L, aeval x R = 0) :
    ∃ s : hypersurfaceLineAtlas R, hypersurfaceAtlasLine R s = L := by
  obtain ⟨p, B, hmap, hB⟩ := hypersurface_line_exists_chart R L hL hR
  refine ⟨⟨p, ⟨B, hB⟩⟩, ?_⟩
  have he := congrArg (fun Q : Submodule F (Fin 4 → F) =>
    Q.map (lineCoordinatePermutation (F := F) p).symm.toLinearMap) hmap
  have hc : (lineCoordinatePermutation (F := F) p).symm.toLinearMap.comp
      (lineCoordinatePermutation (F := F) p).toLinearMap = LinearMap.id := by
    ext x i
    simp [lineCoordinatePermutation]
  rw [← Submodule.map_comp, hc, Submodule.map_id] at he
  exact he.symm

end DimensionFourDependence
