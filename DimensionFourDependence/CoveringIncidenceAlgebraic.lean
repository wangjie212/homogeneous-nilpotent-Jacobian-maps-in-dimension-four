import DimensionFourDependence.UniversalIncidenceFunctionField
import DimensionFourDependence.GenericImageLineFiberFiniteness

/-! # Algebraicity of a covering line incidence over the actual image field

The covering component has exactly the original image relations. Its
generic point is therefore a smooth generic point of the actual image.
All embeddings fixing that point send its generic matrix into a checked
finite fiber. Since the matrix generates the incidence field over the
output field, the field extension is algebraic.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

local notation "IncRing" => MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)
local notation "IncField" => FractionRing IncRing

omit [Q.IsPrime] in
/-- Exactness of the universal incidence kernel gives exactly the actual
image relations at its fraction-field generic point. -/
theorem componentLineGenericPoint_relations
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (P : MvPolynomial (Fin 4) K) :
    aeval (componentLineGenericPoint Q p) P = 0 ↔ aeval H P = 0 := by
  rw [componentLineGenericPoint_aeval]
  rw [map_eq_zero_iff _ (IsFractionRing.injective IncRing IncField)]
  change P ∈ RingHom.ker (componentLineIncidenceHom p Q) ↔ P ∈ imageRelationIdeal H
  rw [hk]

variable [CharZero K]

/-- A covering component's actual universal incidence function field is
algebraic over the field of its actual output coordinates. -/
theorem covering_component_incidence_isAlgebraic
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    Algebra.IsAlgebraic
      (fullOutputField (K := K) (componentLineGenericPoint Q p)) IncField := by
  let M := fullOutputField (K := K) (componentLineGenericPoint Q p)
  let O : Fin 4 → AlgebraicClosure IncField :=
    fun i => algebraMap IncField (AlgebraicClosure IncField) (componentLineGenericPoint Q p i)
  have hrel (P : MvPolynomial (Fin 4) K) : aeval O P = 0 ↔ aeval H P = 0 := by
    have he := comp_aeval_apply (componentLineGenericPoint Q p)
      (IsScalarTower.toAlgHom K IncField (AlgebraicClosure IncField)) P
    change algebraMap IncField (AlgebraicClosure IncField)
      (aeval (componentLineGenericPoint Q p) P) = aeval O P at he
    rw [← he, map_eq_zero_iff _ (algebraMap IncField (AlgebraicClosure IncField)).injective]
    exact componentLineGenericPoint_relations Q H p hk P
  have hf := I.finite_original_chart_fiber_of_relations H hd hH hrank hind O hrel p
  apply isAlgebraic_of_finite_matrix_embedding_values
    (componentLineGenericMatrix Q) (componentLineIncidence_field_generated_by_matrix Q p) _ hf
  intro σ
  have hs := original_line_chart_fiber_algHom (σ.restrictScalars K) p I.equation
    (componentLineGenericMatrix Q) (componentLineGenericPoint Q p)
    (componentLineGenericMatrix_equations Q _ heq) (componentLineGenericPoint_mem Q p)
  have hfix : (fun i => σ (componentLineGenericPoint Q p i)) = O := by
    funext i
    let a : M := ⟨componentLineGenericPoint Q p i,
      IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    change σ (algebraMap M IncField a) =
      algebraMap IncField (AlgebraicClosure IncField) (algebraMap M IncField a)
    rw [σ.commutes, ← IsScalarTower.algebraMap_apply M IncField (AlgebraicClosure IncField)]
    rfl
  refine ⟨hs.1, ?_⟩
  have hpoint : (fun i => σ (componentLineGenericPoint Q p i)) ∈
      lineChartMemberLine p (fun i j => σ (componentLineGenericMatrix Q i j)) := hs.2
  rw [hfix] at hpoint
  exact hpoint

end DimensionFourDependence
