import DimensionFourDependence.NormalDivisorStalkDvr
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField

/-! # A proper birational map lifts normal codimension-one points -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 120000

theorem dominant_map_generic_point {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at h

/-- Pullback on function fields is the actual stalk map at the generic point. -/
noncomputable def dominantFunctionFieldHom {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (Inseparable.of_eq (dominant_map_generic_point f).symm)).hom ≫ f.stalkMap (genericPoint X)).hom

theorem dominantFunctionFieldHom_stalk {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (a : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldHom f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  have hx : genericPoint X ⤳ x := genericPoint_specializes x
  have h := LocallyRingedSpace.stalkSpecializes_stalkMap_apply f.toLRSHom (genericPoint X) x hx a
  let h₁ : f (genericPoint X) ⤳ genericPoint Y := specializes_of_eq (dominant_map_generic_point f)
  let h₂ : genericPoint Y ⤳ f x := genericPoint_specializes (f x)
  have hcomp : Y.presheaf.stalkSpecializes h₂ ≫ Y.presheaf.stalkSpecializes h₁ =
      Y.presheaf.stalkSpecializes (hx.map f.continuous) := Y.presheaf.stalkSpecializes_comp h₁ h₂
  have ha := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hcomp) a
  exact (congrArg (fun s => f.stalkMap (genericPoint X) s) ha).trans h

private theorem local_ring_map_onto_of_valuation_fraction_field
    {A B F : Type u} [CommRing A] [CommRing B] [IsDomain A] [ValuationRing A] [IsLocalRing B]
    [Field F] [Algebra A F] [IsFractionRing A F] (f : A →+* B) [IsLocalHom f]
    (g : B →+* F) (hg : Function.Injective g) (hgf : ∀ a, g (f a) = algebraMap A F a) :
    Function.Surjective f := by
  intro b
  rcases ValuationRing.isInteger_or_isInteger A (g b) with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, hg ((hgf a).trans ha)⟩
  · by_cases hb : b = 0
    · exact ⟨0, (map_zero f).trans hb.symm⟩
    have hgb : g b ≠ 0 := fun h => hb (hg (h.trans (map_zero g).symm))
    have hab : f a * b = 1 := by
      apply hg
      rw [map_mul, hgf, ha, inv_mul_cancel₀ hgb, map_one]
    have hu : IsUnit a := isUnit_of_map_unit f a (IsUnit.of_mul_eq_one _ hab)
    obtain ⟨u, rfl⟩ := hu
    refine ⟨↑u⁻¹, hg ?_⟩
    rw [hgf]
    have h : algebraMap A F (u : A) * g b = 1 := by
      rw [ha, inv_mul_cancel₀ hgb]
    have hi : algebraMap A F (↑u⁻¹ : A) * algebraMap A F (u : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc
      algebraMap A F (↑u⁻¹ : A) = algebraMap A F (↑u⁻¹ : A) * 1 := (mul_one _).symm
      _ = g b := by rw [← h, ← mul_assoc, hi, one_mul]

/-- A dominant proper morphism inducing an isomorphism on function
fields has an isomorphic stalk above every normal codimension-one point. -/
theorem proper_birational_lifts_normal_divisor
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] (hf : Function.Surjective (dominantFunctionFieldHom f))
    (p : Y) (hp : Order.coheight p = 1) [IsIntegrallyClosed (Y.presheaf.stalk p)] :
    ∃ x : X, f x = p ∧ Order.coheight x = 1 ∧ Function.Bijective (f.stalkMap x).hom := by
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have htop := f.denseRange.closure_range
  rw [hclosed.closure_eq] at htop
  have hpRange : p ∈ Set.range f := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := hpRange
  have hxY : Order.coheight (f x) = 1 := by rw [hx]; exact hp
  let : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  let : IsDiscreteValuationRing (Y.presheaf.stalk (f x)) := normal_codimension_one_scheme_stalk_isDVR _ hxY
  let e := RingEquiv.ofBijective (dominantFunctionFieldHom f) ⟨(dominantFunctionFieldHom f).injective, hf⟩
  let g := e.symm.toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hg : Function.Injective g := e.symm.injective.comp (IsFractionRing.injective _ _)
  have hgf (a : Y.presheaf.stalk (f x)) : g ((f.stalkMap x).hom a) =
      algebraMap (Y.presheaf.stalk (f x)) Y.functionField a := by
    apply e.injective
    exact (e.apply_symm_apply _).trans (dominantFunctionFieldHom_stalk f x a).symm
  have hbij : Function.Bijective (f.stalkMap x).hom := ⟨fun a b hab =>
    (IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField)
      ((hgf a).symm.trans ((congrArg g hab).trans (hgf b))),
    local_ring_map_onto_of_valuation_fraction_field (f.stalkMap x).hom g hg hgf⟩
  have hd := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective (f.stalkMap x).hom hbij)
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hxY] at hd
  refine ⟨x, hx, ?_, hbij⟩
  exact_mod_cast hd.symm

end DimensionFourDependence
