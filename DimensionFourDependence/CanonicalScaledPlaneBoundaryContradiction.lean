import DimensionFourDependence.SpecifiedGraphOutputValues
import DimensionFourDependence.SpecifiedGraphCoefficientExtension
import DimensionFourDependence.CanonicalGraphRootFactor
import DimensionFourDependence.ActualSpecifiedSimpleRootBoundary

/-! # The original canonical scaled-plane root contradicts an actual fixed-vertex boundary -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    {B Z : Type u} [Field B] [Field Z] [Algebra B Z]

local notation "hd₀" => (lt_trans Nat.zero_lt_one hd)
local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => (fun i => algebraMap C₀ E (e ((A) i)))
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)
local notation "n꜀" => closedGaussCanonicalRootNumerator H I p hY h hh e E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A) (y₀)

local instance canonicalScaledPlaneBoundaryContradictionDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance canonicalScaledPlaneBoundaryContradictionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance canonicalScaledPlaneBoundaryContradictionExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The parameter maps compose through the entire original closed
Gauss inclusion before any new coefficient algebra is installed. -/
theorem original_graph_parameter_map_composition_retained
    [Algebra K B] (g : (L) →ₐ[K] B) :
    (g.comp (a)).comp e.toAlgHom = g.comp (f₀) := by
  apply AlgHom.ext
  intro t
  change g ((a) (e t)) = g ((f₀) t)
  apply congrArg g
  apply Subtype.ext
  exact (original_closed_gauss_graph_inclusion_source_value H I p hY h hh (e t)).trans
    (closedGaussCoefficientParameterHom_source_value H I p hY h hh e t).symm

include hrank hN hvertex

/-- With the original canonical numerator and original plane root,
the same specified source, graph and tensor realization cannot have
the fixed vertex on the original fiber boundary. The scalar root,
factor equation, coefficient algebraicity and longitudinal dual vector
are all constructed from the specified original data. -/
theorem canonical_scaled_plane_root_has_no_actual_fixed_vertex_boundary_of_compatible_algebras
    (s : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0)
    (hn : aeval (w) ((O) (n꜀)) ≠ 0) (u : E) (hu : u ≠ 0)
    (r : F₀) (hr : r ≠ 0)
    (hscaled : r = algebraMap E F₀ u * aeval (xₐ) (L₀))
    (hpower : r ^ d = aeval (xₐ) ((O) s))
    [aKB : Algebra K B] [aLB : Algebra (L) B]
    [@IsScalarTower K (L) B (inferInstance : SMul K (L)) aLB.toSMul aKB.toSMul]
    [Algebra.IsAlgebraic (L) B]
    (f : S₀ →+* Z) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z ((algebraMap (L) B) l) = f (l : S₀))
    (hσ : ∀ c : C₀, (algebraMap (L) B) ((a) c) = σ (algebraMap C₀ E c))
    (hsource : ∀ t : S₀, φ (algebraMap T₀ F₀ (t ⊗ₜ[C₀] (1 : E))) = f t)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (hcoords : ∀ i, φ ((xₐ) i) = f (rationalCoordinate (K := K) i))
    (z : Option (Fin 4) → B) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L)
      (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (hzfirst : ∀ i : Fin 3, z (some i.castSucc) = 0)
    (hzlast : z (some (Fin.last 3)) = 1) : False := by
  let gK : (L) →ₐ[K] B := IsScalarTower.toAlgHom K (L) B
  let gC : C₀ →ₐ[K] B := gK.comp (a)
  have hσC (c : C₀) : σ (algebraMap C₀ E c) = gC c := (hσ c).symm
  have hparam : gC.comp e.toAlgHom = gK.comp (f₀) :=
    original_graph_parameter_map_composition_retained H I p hY h hh e gK
  have hgraph (c : Fin 4 → E) :
      graphRestrictedCovector p (fun i => (gK.comp (f₀)) ((A) i)) (σ ∘ c) =
        σ ∘ graphRestrictedCovector p (Aₑ) c := by
    rw [← graphRestrictedCovector_field_map]
    congr 1
    funext i
    exact (DFunLike.congr_fun hparam ((A) i)).symm.trans (hσC (e ((A) i))).symm
  obtain ⟨c, q, k, hc, hq, hk⟩ :=
    specified_original_chart_exists_exact_invariant_coefficients H hrank p hY hN h hh
  let rho : B := σ u * σ (algebraMap C₀ E (a₀)) * (algebraMap (L) B) c
  have hrhoValue : φ r = algebraMap B Z rho := by
    rw [hscaled, map_mul, hcoeff,
      specified_tensor_normal_value_eq_original_first_invariant H I p hY h hh E hH (hd₀)
        hind hGauss e f (algebraMap (L) B) σ φ hg hσ hcoeff hcoords c hc]
    simp only [rho, map_mul, mul_assoc]
  have hrho : rho ≠ 0 := by
    intro hzero
    have he : φ r = φ 0 := hrhoValue.trans
      ((congrArg (algebraMap B Z) hzero).trans
        ((algebraMap B Z).map_zero'.trans φ.map_zero'.symm))
    exact hr (specified_original_affine_tensor_realization_injective H I E φ he)
  have hfactor := canonical_scaled_plane_root_constructs_original_graph_factor
    H I p hY h hh e E gC σ hσC u hu (fun i => (algebraMap (L) B) ((y₀) i)) rho ((algebraMap (L) B) c)
    (show rho = σ u * gC (a₀) * (algebraMap (L) B) c from by rw [← hσC])
  rw [hparam] at hfactor
  change parametricRulingDenominator (gK.comp (f₀)) (A) (fun i => gK ((y₀) i)) * gK c = _ at hfactor
  rw [parametricRulingDenominator_map] at hfactor
  have hroot := specified_tensor_root_power_eq_original_graph_pairing
    H I p hY h hh E (hd₀) hH e f (algebraMap (L) B) σ φ hg hσ hsource hcoeff s r hpower rho hrhoValue
  have hpair := fixed_vertex_canonical_scaled_plane_forms_independent_on_actual_ruling
    H I p hY h hh e E hH (hd₀) hind hGauss hvertex s hs hn u hu
  obtain ⟨hm, hsalg, b, _v, _hb, _hv, hbgraph, _hvgraph, hmb, hsb, _hmv, _hsv, _hLI⟩ :=
    actual_chosen_graph_dual_pair_retained_by_specified_coefficients
      H I p hY h hh e E hH (hd₀) hind hGauss gC σ hσC (u⁻¹ • (n꜀)) s hpair
  rw [hparam] at hm hsalg hbgraph
  have hb : (fun i => (gK.comp (f₀)) (rationalParameterDerivative K ((A) i))) ⬝ᵥ
      (fun i => σ (b (p i.castSucc))) = 0 := hbgraph
  have hs0 := actual_fixed_vertex_boundary_forces_specified_root_fourth_coefficient_zero
    H hrank I p hY h hh e B hd hH hN hind hGauss c q k hc hq hk
    (σ ∘ graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀))) (σ ∘ s)
    (fun i => σ (b (p i.castSucc))) hm
    (by rw [hgraph]; exact hsalg) hb hmb (by rw [hgraph]; exact hsb)
    rho hrho hfactor (by rw [hgraph]; exact hroot) z hz hpoint hz0 hzfirst hzlast
  exact hs ((RingHom.injective (R := E) (S := B) σ) (hs0.trans (map_zero σ).symm))


/-- The raw compatible graph embedding installs the original scalar
 tower and applies the contradiction with abstract compatible algebras. -/
theorem canonical_scaled_plane_root_has_no_actual_fixed_vertex_boundary
    (s : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0)
    (hn : aeval (w) ((O) (n꜀)) ≠ 0) (u : E) (hu : u ≠ 0)
    (r : F₀) (hr : r ≠ 0)
    (hscaled : r = algebraMap E F₀ u * aeval (xₐ) (L₀))
    (hpower : r ^ d = aeval (xₐ) ((O) s))
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c))
    (hsource : ∀ t : S₀, φ (algebraMap T₀ F₀ (t ⊗ₜ[C₀] (1 : E))) = f t)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (hcoords : ∀ i, φ ((xₐ) i) = f (rationalCoordinate (K := K) i)) :
    letI : Algebra (L) B := g.toAlgebra
    Algebra.IsAlgebraic (L) B →
    ∀ (z : Option (Fin 4) → B) (hz : z ≠ 0),
      projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L)
        (rationalCoordinate (K := K) (n := 4)) →
      z none = 0 → (∀ i : Fin 3, z (some i.castSucc) = 0) →
      z (some (Fin.last 3)) = 1 → False := by
  let aLB : Algebra (L) B := g.toAlgebra
  letI : Algebra (L) B := aLB
  letI : SMul (L) B := aLB.toSMul
  intro halg z hz hpoint hz0 hzfirst hzlast
  letI : Algebra.IsAlgebraic (L) B := halg
  letI : Algebra K B := ((algebraMap (L) B).comp (algebraMap K (L))).toAlgebra
  letI : IsScalarTower K (L) B := IsScalarTower.of_algebraMap_eq' rfl
  exact canonical_scaled_plane_root_has_no_actual_fixed_vertex_boundary_of_compatible_algebras
    H hrank I p hY h hh E hd hH hN hind hGauss hvertex e s hs hn u hu r hr hscaled hpower
    f σ φ hg hσ hsource hcoeff hcoords z hz hpoint hz0 hzfirst hzlast

end DimensionFourDependence
