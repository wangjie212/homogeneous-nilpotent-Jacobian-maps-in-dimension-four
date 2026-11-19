import DimensionFourDependence.LineChartEmbedding
import DimensionFourDependence.GenericOutputPoint

/-! # The actual function field of a universal line incidence

The quotient parameter coordinates and two free line coordinates give
the generic matrix and point. Over the field of the actual output point,
the matrix entries alone generate the universal incidence function field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

local notation "ParamRing" => (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)
local notation "IncRing" => MvPolynomial (Fin 2) ParamRing
local notation "F" => FractionRing IncRing

/-- The actual generic matrix over the component's universal incidence field. -/
noncomputable def componentLineGenericMatrix : Matrix (Fin 2) (Fin 2) F :=
  fun i j => algebraMap ParamRing F (Ideal.Quotient.mk Q (X (i, j)))

/-- The actual output of the universal incidence at its generic point. -/
noncomputable def componentLineGenericPoint (p : Equiv.Perm (Fin 4)) : Fin 4 → F :=
  fun i => algebraMap IncRing F (componentGraphLineCoordinate Q (p.symm i))

omit [Q.IsPrime] in
/-- Evaluation at the generic point is the incidence homomorphism followed
by the actual injective map to its fraction field. -/
theorem componentLineGenericPoint_aeval (p : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) K) :
    aeval (componentLineGenericPoint Q p) P =
      algebraMap IncRing F (componentLineIncidenceHom p Q P) := by
  exact (comp_aeval_apply (fun i => componentGraphLineCoordinate Q (p.symm i))
    (IsScalarTower.toAlgHom K IncRing F) P).symm

/-- The actual generic point lies on the line represented by the actual generic matrix. -/
theorem componentLineGenericPoint_mem (p : Equiv.Perm (Fin 4)) :
    componentLineGenericPoint Q p ∈ lineChartMemberLine p (componentLineGenericMatrix Q) := by
  let u : Fin 2 → F := fun j => algebraMap IncRing F (X j)
  let z : Fin 4 → F := fun i => algebraMap IncRing F (componentGraphLineCoordinate Q i)
  have hmapC (a : ParamRing) :
      algebraMap IncRing F (MvPolynomial.C a) = algebraMap ParamRing F a := by
    exact (IsScalarTower.algebraMap_apply ParamRing IncRing F a).symm
  have hz : z = ![u 0, u 1, (componentLineGenericMatrix Q *ᵥ u) 0,
      (componentLineGenericMatrix Q *ᵥ u) 1] := by
    funext i
    fin_cases i <;> simp [z, u, componentGraphLineCoordinate, componentLineGenericMatrix,
      Matrix.mulVec, dotProduct, hmapC]
  exact ⟨z, (mem_graphLineFour _ _).mpr ⟨u, hz⟩, rfl⟩

/-- The generic matrix satisfies the original coefficient equations of
every chart component on which those equations vanish. -/
theorem componentLineGenericMatrix_equations (R : MvPolynomial (Fin 4) K)
    (hQ : graphLineEquationIdeal R ≤ Q) :
    ∀ P ∈ graphLineEquationPolynomials R,
      extendedLineChartSpecialization (componentLineGenericMatrix Q) P = 0 := by
  intro P hP
  have hm : Ideal.Quotient.mk Q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hQ (Ideal.subset_span hP))
  let f : MvPolynomial (Fin 2 × Fin 2) K →ₐ[K] F :=
    (IsScalarTower.toAlgHom K ParamRing F).comp (Ideal.Quotient.mkₐ K Q)
  have he : extendedLineChartSpecialization (componentLineGenericMatrix Q) = f := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [extendedLineChartSpecialization, componentLineGenericMatrix, f]
  rw [he]
  change algebraMap ParamRing F (Ideal.Quotient.mk Q P) = 0
  rw [hm, map_zero]

/-- Once the actual output point is in the coefficient field, the generic
matrix entries generate the whole universal incidence function field. -/
theorem componentLineIncidence_field_generated_by_matrix (p : Equiv.Perm (Fin 4)) :
    IntermediateField.adjoin (fullOutputField (K := K) (componentLineGenericPoint Q p))
      (Set.range (fun ij : Fin 2 × Fin 2 => componentLineGenericMatrix Q ij.1 ij.2)) = ⊤ := by
  let M := fullOutputField (K := K) (componentLineGenericPoint Q p)
  let S := IntermediateField.adjoin M
    (Set.range (fun ij : Fin 2 × Fin 2 => componentLineGenericMatrix Q ij.1 ij.2))
  have hB (ij : Fin 2 × Fin 2) : componentLineGenericMatrix Q ij.1 ij.2 ∈ S :=
    IntermediateField.subset_adjoin M _ ⟨ij, rfl⟩
  have hO (i : Fin 4) : componentLineGenericPoint Q p i ∈ S :=
    S.algebraMap_mem ⟨_, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hu (j : Fin 2) : algebraMap IncRing F (X j) ∈ S := by
    fin_cases j
    · simpa [componentLineGenericPoint, componentGraphLineCoordinate] using hO (p 0)
    · simpa [componentLineGenericPoint, componentGraphLineCoordinate] using hO (p 1)
  have hcoeff (a : ParamRing) : algebraMap ParamRing F a ∈ S := by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction P using MvPolynomial.induction_on with
    | C a =>
      change algebraMap ParamRing F (algebraMap K ParamRing a) ∈ S
      rw [← IsScalarTower.algebraMap_apply K ParamRing F]
      exact (S.restrictScalars K).algebraMap_mem a
    | add P P' hP hP' => simp only [map_add]; exact S.add_mem hP hP'
    | mul_X P ij hP => simp only [map_mul]; exact S.mul_mem hP (hB ij)
  have hpoly (P : IncRing) : algebraMap IncRing F P ∈ S := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      change algebraMap IncRing F (algebraMap ParamRing IncRing a) ∈ S
      rw [← IsScalarTower.algebraMap_apply ParamRing IncRing F]
      exact hcoeff a
    | add P P' hP hP' => rw [map_add]; exact S.add_mem hP hP'
    | mul_X P j hP => rw [map_mul]; exact S.mul_mem hP (hu j)
  apply top_unique
  intro f _
  obtain ⟨P, P', _, rfl⟩ := IsFractionRing.div_surjective (A := IncRing) f
  exact S.div_mem (hpoly P) (hpoly P')

end DimensionFourDependence
