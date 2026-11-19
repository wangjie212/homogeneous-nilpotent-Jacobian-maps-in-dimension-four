import DimensionFourDependence.ActualWeightedGaussRootForms
import DimensionFourDependence.ActualBoundaryGraphDirection

/-! # The actual boundary constructs the finite root and form data (4.4)

The original finite Gauss-algebraic boundary witness supplies a valuation
boundary and zero acceleration. Its first-three-coordinate projection is
nonzero, the actual quadratic equation gives its graph ruling equation,
and the original-to-closed parameter comparison supplies coefficient
algebraicity. The weighted calculation therefore constructs all root
and linear-form data in the same actual boundary coefficient extension.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y))

/-- Actual valuation boundary and finite original-coordinate linear
forms realizing (4.4) in its actual algebraic coefficient extension.
The root's rational expression and the original denominator are retained. -/
noncomputable def ActualGaussBoundaryRootFormsExist (d : ℕ) : Prop :=
  ∃ (V : ValuationSubring S₀) (hV : ∀ a : L, (a : S₀) ∈ V),
    letI : Algebra (L) V := valuationConstantAlgebra V hV
    letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
    let κ := IsLocalRing.ResidueField V
    letI : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
    letI : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∃ (i : Fin 4) (scale : S₀) (z : Option (Fin 4) → V),
      (z none : S₀) = scale ∧ (∀ j, (z (some j) : S₀) = scale * (x) j) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 ∧
      ∃ hκalg : Algebra.IsAlgebraic (L) κ,
      letI : Algebra.IsAlgebraic (L) κ := hκalg
      ∃ hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0,
        projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
          projectiveClosureSet («L» := L) (x) ∧
        (fun j : Fin 3 => IsLocalRing.residue V (z (some (p j.castSucc)))) ≠ 0 ∧
        let g := IsScalarTower.toAlgHom K (L) κ
        let f := g.comp (f₀)
        let y := fun j => g (coefficientCoordinate (K := K) (Y) j)
        let v := fun j : Fin 3 => IsLocalRing.residue V (z (some (p j.castSucc)))
        ∃ C : IntermediateField f.fieldRange κ, Module.Finite f.fieldRange C ∧
          ∃ (n m s : Fin 3 → C) (ρ : κ), n ≠ 0 ∧ m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
            ((fun j => (n j : κ)) ⬝ᵥ y) = g (n₀) ∧
            ((fun j => (n j : κ)) ⬝ᵥ y) * g c = ((fun j => (m j : κ)) ⬝ᵥ y) * ρ ∧
            ρ ^ d = (fun j => (s j : κ)) ⬝ᵥ y ∧ (fun j => (s j : κ)) ⬝ᵥ v = 0 ∧
            coordinateEuler v (extendedCoefficientPartial (Y) hY κ) ρ = 0 ∧
            ρ = (((fun j => (n j : κ)) ⬝ᵥ y) * g c) / ((fun j => (m j : κ)) ⬝ᵥ y) ∧
            (∀ j, n j = algebraMap f.fieldRange C
              (f.equivFieldRange (rationalParameterDerivative K (rationalParameterDerivative K ((A₀) j)))))

include hh hrank

/-- The actual original invariant coefficients construct the complete
finite root/form boundary data in (4.4). No branch, coordinate algebraicity,
ruling membership, zero acceleration or factorization is assumed. -/
theorem actual_gauss_boundary_root_forms_exist
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hc0 : c ≠ 0) (q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q) :
    ActualGaussBoundaryRootFormsExist H I p hY h c hh e d := by
  obtain ⟨V, hV, hrest⟩ := actual_finite_gauss_boundary_direction_exists H hrank I p hY h c hh e
    hd hH hN hind hGauss q k hc hq hk
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, halg, haccel, _⟩ := hrest
  let : Algebra.IsAlgebraic (L) κ := hκalg
  have hb : (fun j => IsLocalRing.residue V (z (some j))) ≠ 0 := by
    intro he
    have hi := congrFun he i
    change IsLocalRing.residue V (z (some i)) = 0 at hi
    exact one_ne_zero (hr1.symm.trans hi)
  let v : Fin 3 → κ := fun j => IsLocalRing.residue V (z (some (p j.castSucc)))
  have hv0 : v ≠ 0 := actual_full_fiber_boundary_first_three_direction_ne_zero H p hY h c hc κ
    (fun j => IsLocalRing.residue V (z j)) hres hb hboundary hr0
  have halg' : ∀ j, IsAlgebraic
      (((IsScalarTower.toAlgHom K (L) κ).comp (f₀)).fieldRange) (v j) := by
    intro j
    exact actual_boundary_original_gauss_algebraic_implies_closed_parameter_algebraic H hrank I p hY h hh e κ
      _ (halg (p j.castSucc))
  let z₃ : Option (Fin 3) → V := fun j => j.elim (z none) (fun j => z (some (p j.castSucc)))
  have hv : (fun j => algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) j)))) ⬝ᵥ v = 0 :=
    actual_closed_gauss_quadratic_boundary_mem_ruling H I p hY h hh e hGauss hd hH c q hq
      (IsScalarTower.toAlgHom (L) V κ) (show Function.Injective (algebraMap V S₀) from Subtype.val_injective)
      scale z₃ hz0 (fun j => hz (p j.castSucc)) hr0
  refine ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, hv0, ?_⟩
  exact actual_gauss_invariant_product_finite_three_root_forms H I p hY h hh e hGauss hd hH κ
    c hc hc0 v hv0 hv halg' haccel

end DimensionFourDependence
