import DimensionFourDependence.ProjectiveConeFractionConstants
import DimensionFourDependence.NormalizationRing

/-! # Homogeneous rational roots and their linear combinations lift to the actual cone normalization -/

namespace DimensionFourDependence

open MvPolynomial

variable {E F : Type*} [Field E] [Field F] [Algebra E F] (x : Fin 3 → F)

local notation "A₀" => projectiveConeCoordinateAlgebra (E := E) x
local notation "φ₀" => projectiveConeFractionEmbedding (E := E) x

/-- The actual fraction embedding preserves the whole original
cone algebra, not merely its chosen homogeneous coordinates. -/
theorem projectiveConeFractionEmbedding_algebraMap (a : A₀) :
    φ₀ (algebraMap A₀ (FractionRing A₀) a) = algebraMap (Polynomial F) (RatFunc F) (a : Polynomial F) := by
  change IsFractionRing.lift (projectiveConeRadialHom_injective (E := E) x) _ = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- A homogeneous original cone polynomial retains its original
coefficient value and its exact radial degree under the actual embedding. -/
theorem projectiveConeFractionEmbedding_homogeneous_value
    (P : MvPolynomial (Option (Fin 3)) E) {d : ℕ} (hP : P.IsHomogeneous d) :
    φ₀ (algebraMap A₀ (FractionRing A₀) ((projectiveConeMap (L := E) x).rangeRestrict P)) =
      RatFunc.C (aeval (fun i : Option (Fin 3) => i.elim 1 x) P) * RatFunc.X ^ d := by
  calc
    _ = algebraMap (Polynomial F) (RatFunc F) (projectiveConeMap (L := E) x P) :=
      projectiveConeFractionEmbedding_algebraMap x _
    _ = algebraMap (Polynomial F) (RatFunc F)
        (Polynomial.monomial d (aeval (fun i : Option (Fin 3) => i.elim 1 x) P)) :=
      congrArg (algebraMap (Polynomial F) (RatFunc F)) (projectiveConeMap_of_isHomogeneous x hP)
    _ = _ := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      rfl

variable (hgen : IntermediateField.adjoin E (Set.range x) = ⊤)

/-- Homogenize an actual original point-field element with the
same original radial coordinate in the actual cone fraction field. -/
noncomputable def projectiveConeRadialLift (u : F) : FractionRing A₀ :=
  projectiveConeFractionConstantHom x hgen u *
    algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x none)

theorem projectiveConeRadialLift_value (u : F) :
    φ₀ (projectiveConeRadialLift x hgen u) = RatFunc.C u * RatFunc.X := by
  calc
    _ = φ₀ (projectiveConeFractionConstantHom x hgen u) *
        φ₀ (algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x none)) := map_mul (φ₀) _ _
    _ = RatFunc.C u * (RatFunc.C (1 : F) * RatFunc.X) :=
      congrArg₂ (· * ·) (projectiveConeFractionConstantHom_value x hgen u)
        (projectiveConeFractionEmbedding_coordinate x none)
    _ = _ := by rw [map_one, one_mul]

/-- The original rational root power equation homogenizes to an
actual equation over the whole original cone coordinate algebra. -/
theorem projectiveConeRadialLift_root_power
    (P : MvPolynomial (Option (Fin 3)) E) {d : ℕ} (hP : P.IsHomogeneous d)
    (r : F) (hroot : r ^ d = aeval (fun i : Option (Fin 3) => i.elim 1 x) P) :
    projectiveConeRadialLift x hgen r ^ d =
      algebraMap A₀ (FractionRing A₀) ((projectiveConeMap (L := E) x).rangeRestrict P) := by
  apply (φ₀).injective
  calc
    _ = (RatFunc.C r * RatFunc.X) ^ d :=
      (map_pow (φ₀) _ d).trans (congrArg (· ^ d) (projectiveConeRadialLift_value x hgen r))
    _ = RatFunc.C (r ^ d) * RatFunc.X ^ d := by rw [mul_pow, map_pow]
    _ = RatFunc.C (aeval (fun i : Option (Fin 3) => i.elim 1 x) P) * RatFunc.X ^ d :=
      congrArg (fun u : F => RatFunc.C u * RatFunc.X ^ d) hroot
    _ = _ := (projectiveConeFractionEmbedding_homogeneous_value x P hP).symm

/-- The actual homogenized rational root is regular in the actual
cone normalization, by its original positive-degree power equation. -/
theorem projectiveConeRadialLift_root_mem_normalization
    (P : MvPolynomial (Option (Fin 3)) E) {d : ℕ} (hP : P.IsHomogeneous d) (hd : 0 < d)
    (r : F) (hroot : r ^ d = aeval (fun i : Option (Fin 3) => i.elim 1 x) P) :
    projectiveConeRadialLift x hgen r ∈ normalizationRing A₀ :=
  rational_root_mem_normalization A₀ _ hd _ (projectiveConeRadialLift_root_power x hgen P hP r hroot)

/-- Degree-one original source polynomials lift into the original
cone algebra itself, with no normality assumption. -/
theorem projectiveConeRadialLift_linear_value
    (Q : MvPolynomial (Option (Fin 3)) E) (hQ : Q.IsHomogeneous 1) :
    projectiveConeRadialLift x hgen (aeval (fun i : Option (Fin 3) => i.elim 1 x) Q) =
      algebraMap A₀ (FractionRing A₀) ((projectiveConeMap (L := E) x).rangeRestrict Q) := by
  simpa only [pow_one] using projectiveConeRadialLift_root_power x hgen Q hQ
    (aeval (fun i : Option (Fin 3) => i.elim 1 x) Q) (by rw [pow_one])

/-- The paper's linear combination of a linear source form and a
homogeneous rational root is an actual regular element of the cone
normalization. Integrality over the entire cone is derived. -/
theorem projectiveConeRadialLift_root_combination_mem_normalization
    (Q : MvPolynomial (Option (Fin 3)) E) (hQ : Q.IsHomogeneous 1)
    (P : MvPolynomial (Option (Fin 3)) E) {d : ℕ} (hP : P.IsHomogeneous d) (hd : 0 < d)
    (r : F) (hroot : r ^ d = aeval (fun i : Option (Fin 3) => i.elim 1 x) P) (α β : E) :
    projectiveConeRadialLift x hgen
      (algebraMap E F α * aeval (fun i : Option (Fin 3) => i.elim 1 x) Q + algebraMap E F β * r) ∈
        normalizationRing A₀ := by
  have hr := projectiveConeRadialLift_root_mem_normalization x hgen P hP hd r hroot
  have hlinear : projectiveConeRadialLift x hgen (aeval (fun i : Option (Fin 3) => i.elim 1 x) Q) ∈
      normalizationRing A₀ := by
    rw [projectiveConeRadialLift_linear_value x hgen Q hQ]
    exact (normalizationRing A₀).algebraMap_mem _
  have hc (c : E) : algebraMap E (FractionRing A₀) c ∈ normalizationRing A₀ := by
    change IsIntegral A₀ (algebraMap E (FractionRing A₀) c)
    rw [IsScalarTower.algebraMap_apply E A₀ (FractionRing A₀)]
    exact isIntegral_algebraMap
  have he : projectiveConeRadialLift x hgen
      (algebraMap E F α * aeval (fun i : Option (Fin 3) => i.elim 1 x) Q + algebraMap E F β * r) =
        algebraMap E (FractionRing A₀) α *
          projectiveConeRadialLift x hgen (aeval (fun i : Option (Fin 3) => i.elim 1 x) Q) +
        algebraMap E (FractionRing A₀) β * projectiveConeRadialLift x hgen r := by
    dsimp only [projectiveConeRadialLift]
    rw [map_add, map_mul, map_mul,
      (projectiveConeFractionConstantHom x hgen).commutes,
      (projectiveConeFractionConstantHom x hgen).commutes]
    ring
  exact he ▸ add_mem (mul_mem (hc α) hlinear) (mul_mem (hc β) hr)

end DimensionFourDependence
