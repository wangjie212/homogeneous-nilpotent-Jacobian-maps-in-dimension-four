import DimensionFourDependence.ExtendedNormalizationHyperplaneSections

/-! # Actual original-frame unit transitions and global section gluing on the pencil -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e

local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- The coefficient transition Xj/Xi on the original overlap, with
the original overlap order retained. -/
noncomputable def extendedClosedGaussHyperplaneCoefficientTransition (i j : Fin 4) :
    Γ(N, U i ⊓ U j) :=
  (N).presheaf.map (eqToHom (inf_comm (U i) (U j))).op
    (extendedClosedGaussNormalizationHyperplaneTransition H I E hH e j i)

/-- The actual regular coefficient transition has exactly its
original rational coordinate-ratio value. -/
theorem extendedClosedGaussHyperplaneCoefficientTransition_value (i j : Fin 4)
    (p : (U i ⊓ U j : (N).Opens)) :
    schemeRationalSectionFunction N (U i ⊓ U j)
        (extendedClosedGaussHyperplaneCoefficientTransition H I E hH e i j) p = w j / w i := by
  unfold extendedClosedGaussHyperplaneCoefficientTransition
  rw [schemeRationalSectionFunction_res]
  exact extendedClosedGaussNormalizationHyperplaneTransition_value H I E hH e j i _

/-- Both original regular frame changes are inverse in the actual
regular overlap ring, not merely in a supplied coefficient field. -/
theorem extendedClosedGaussHyperplaneTransition_mul_coefficientTransition (i j : Fin 4) :
    extendedClosedGaussNormalizationHyperplaneTransition H I E hH e i j *
        extendedClosedGaussHyperplaneCoefficientTransition H I E hH e i j = 1 := by
  apply schemeRationalSectionFunction_injective_all N (U i ⊓ U j)
  funext p
  simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply]
  rw [extendedClosedGaussNormalizationHyperplaneTransition_value,
    extendedClosedGaussHyperplaneCoefficientTransition_value]
  field_simp [extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e i,
    extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e j]

/-- Each actual original frame change is a regular unit on its
actual tensor-normalization overlap. -/
theorem extendedClosedGaussNormalizationHyperplaneTransition_isUnit (i j : Fin 4) :
    IsUnit (extendedClosedGaussNormalizationHyperplaneTransition H I E hH e i j) :=
  isUnit_iff_exists_inv.mpr
    ⟨extendedClosedGaussHyperplaneCoefficientTransition H I E hH e i j,
      extendedClosedGaussHyperplaneTransition_mul_coefficientTransition H I E hH e i j⟩

/-- Regular coefficients extracted from an actual global section of
the actual pencil sheaf obey the actual original-frame gluing equation. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficient_overlap
    (s : Γ(M, ⊤)) (i j : Fin 4) :
    (N).presheaf.map (Opens.infLELeft (U i) (U j)).op
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s i) =
      extendedClosedGaussHyperplaneCoefficientTransition H I E hH e i j *
        (N).presheaf.map (Opens.infLERight (U i) (U j)).op
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s j) :=
  rationalFrameGlobalCoefficient_overlap N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s i j
    (extendedClosedGaussHyperplaneCoefficientTransition H I E hH e i j)
    (extendedClosedGaussHyperplaneCoefficientTransition_value H I E hH e i j)

end DimensionFourDependence
