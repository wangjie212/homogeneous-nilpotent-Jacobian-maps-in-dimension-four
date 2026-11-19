import DimensionFourDependence.HomogeneousGenericFiberAction
import DimensionFourDependence.FixedLastGeometricFiberValue
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # The free root-of-unity action and component count of Corollary 5.3 -/

namespace DimensionFourDependence

open MvPolynomial

universe u v
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 120000

/-- A finite free action partitions its finite set into copies of its
acting group, one for each actual orbit. -/
theorem free_finite_action_group_card_dvd
    {G : Type u} {X : Type v} [Group G] [MulAction G X] [Finite G] [Finite X]
    (h : ∀ (g : G) (x : X), g • x = x → g = 1) : Nat.card G ∣ Nat.card X := by
  let Ω := MulAction.orbitRel.Quotient G X
  have e (x : X) : G ≃ MulAction.orbit G x :=
    Equiv.ofBijective (fun g => ⟨g • x, ⟨g, rfl⟩⟩) ⟨fun g k he => by
      have hgk : g • x = k • x := congrArg Subtype.val he
      have heq : (g⁻¹ * k) • x = x := by rw [mul_smul, ← hgk, ← mul_smul, inv_mul_cancel, one_smul]
      have hc := h (g⁻¹ * k) x heq
      calc
        g = g * 1 := (mul_one _).symm
        _ = g * (g⁻¹ * k) := congrArg (fun w : G => g * w) hc.symm
        _ = k := by rw [← mul_assoc, mul_inv_cancel, one_mul],
      fun y => by obtain ⟨g, hg⟩ := y.property; exact ⟨g, Subtype.val_injective hg⟩⟩
  let f : X ≃ Ω × G := (MulAction.selfEquivSigmaOrbits G X).trans
    ((Equiv.sigmaCongrRight fun i : Ω => (e i.out).symm).trans (Equiv.sigmaEquivProd Ω G))
  have hcard := Nat.card_congr f
  rw [Nat.card_prod] at hcard
  exact ⟨Nat.card Ω, hcard.trans (Nat.mul_comm _ _)⟩

variable {K E : Type u} [Field K] [CharZero K] [Field E] [IsAlgClosed E]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing R₄
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- In the original coordinates with zero final output, scalar
multiplication acts freely on every actual geometric generic component.
Their finite number is therefore divisible by the homogeneous degree. -/
theorem homogeneous_rank_three_zero_last_output_free_scalar_action
    (H : Fin 4 → R₄) [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hr : polyRank (jac H) = 3) (hz : H (Fin.last 3) = 0) :
    let I := extendCoefficientIdeal E (fiberVanishingIdeal (L := polynomialOutputField H) x)
    ∃ action : MulAction (rootsOfUnity d E) I.minimalPrimes,
      letI := action
      (∀ (u : rootsOfUnity d E) (P : I.minimalPrimes),
        (u • P).val = P.val.comap (polynomialScalarEquiv (u : Eˣ)).toRingHom) ∧
      (∀ (u : rootsOfUnity d E) (P : I.minimalPrimes), u • P = P → u = 1) ∧
      d ∣ Nat.card I.minimalPrimes := by
  let I := extendCoefficientIdeal E (fiberVanishingIdeal (L := polynomialOutputField H) x)
  let G : Fin 4 → F := fun i => algebraMap R₄ F (H i)
  have hJ : rationalJacobian G = (jac H).map (algebraMap R₄ F) := rationalJacobian_polynomial H
  have hrG : (rationalJacobian G).rank = 3 := hJ.symm ▸ hr
  have hNG : IsNilpotent (rationalJacobian G) := hJ.symm ▸ hN.map (algebraMap R₄ F).mapMatrix
  have hG₀ : G (Fin.last 3) = 0 := by simp only [G, hz, map_zero]
  obtain ⟨W⟩ := nilpotent_rank_three_zero_last_output_constructs_fiber_equations G hNG hrG hG₀
  let action := homogeneousGenericFiberAction (E := E) H hH
  let : MulAction (rootsOfUnity d E) I.minimalPrimes := action
  have hAction (u : rootsOfUnity d E) (P : I.minimalPrimes) :
      (u • P).val = P.val.comap (polynomialScalarEquiv (u : Eˣ)).toRingHom := rfl
  have hfree (u : rootsOfUnity d E) (P : I.minimalPrimes) (hp : u • P = P) : u = 1 := by
    have hFix := congrArg (fun q : I.minimalPrimes => q.val) hp
    rw [hAction] at hFix
    let : P.val.IsPrime := P.property.isPrime
    obtain ⟨a, ha, hP⟩ := fixed_last_geometric_component_has_nonzero_last_value G W hrG E P.val P.property
    apply Subtype.val_injective
    exact scalar_stabilizer_trivial_of_nonzero_coordinate_value P.val (Fin.last 3) a ha hP (u : Eˣ) hFix
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let : NeZero (d : E) := ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)⟩
  let : Finite I.minimalPrimes := I.finite_minimalPrimes_of_isNoetherianRing
  have hcard := free_finite_action_group_card_dvd hfree
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity E d] at hcard
  exact ⟨action, hAction, hfree, hcard⟩

end DimensionFourDependence
