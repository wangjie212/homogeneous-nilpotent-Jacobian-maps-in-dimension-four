import DimensionFourDependence.Defs

/-! # A degree-preserving monic projection equation from the hypersurface

When the fiber variable has the full original total degree, its leading
coefficient is a nonzero constant. Affine specialization of the projection
coordinates and constant normalization therefore construct a monic
equation of that same degree, with every coefficient-degree inequality
needed on the infinity chart.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {F k σ : Type*} [Field F] [Field k] [Algebra F k]

/-- Affine specialization into a one-variable polynomial ring does not
increase the original multivariate total degree. -/
theorem polynomial_natDegree_aeval_le_totalDegree
    (s : σ → Polynomial k) (hs : ∀ i, (s i).natDegree ≤ 1)
    (f : MvPolynomial σ F) : (aeval s f).natDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [aeval_monomial]
  have hprod : (d.prod (fun i n => s i ^ n)).natDegree ≤ d.sum (fun _ n => n) := by
    apply (Polynomial.natDegree_prod_le d.support (fun i => s i ^ d i)).trans
    apply Finset.sum_le_sum
    intro i _
    exact Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (d i) (hs i))
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.algebraMap_apply, Polynomial.natDegree_C, zero_add] using
      hprod.trans (le_totalDegree hd))

variable {L : Type*} [CommRing L] [Algebra F L] [Algebra (Polynomial k) L]
  [IsScalarTower F (Polynomial k) L]

/-- An original hypersurface equation with full degree in the fiber
variable constructs a monic equation of the same total degree after
affine projection specialization. The root and all infinity coefficient
degree bounds are constructed from the original equation. -/
theorem exists_monic_hypersurface_projection_equation
    (s : σ → Polynomial k) (hs : ∀ i, (s i).natDegree ≤ 1)
    (f : MvPolynomial (Option σ) F) (hf : f ≠ 0)
    (hfull : f.degreeOf none = f.totalDegree)
    (v : L) (hroot : aeval
      (fun i => i.elim v (fun j => algebraMap (Polynomial k) L (s j))) f = 0) :
    ∃ P : Polynomial (Polynomial k), P.Monic ∧ P.natDegree = f.totalDegree ∧
      (∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree) ∧
      Polynomial.aeval v P = 0 := by
  let f' := optionEquivLeft F σ f
  have hf' : f' ≠ 0 := by
    intro h
    exact hf ((optionEquivLeft F σ).injective (by simpa only [map_zero] using h))
  have hfdegree : f'.natDegree = f.totalDegree :=
    (natDegree_optionEquivLeft F f).trans hfull
  have hconstant : f'.leadingCoeff.totalDegree = 0 := by
    have h := totalDegree_coeff_optionEquivLeft_add_le F σ f f.totalDegree le_rfl
    change (f'.coeff f.totalDegree).totalDegree + f.totalDegree ≤ f.totalDegree at h
    rw [← hfdegree, Polynomial.coeff_natDegree] at h
    omega
  let c : F := f'.leadingCoeff.coeff 0
  have hlead : f'.leadingCoeff = C c := totalDegree_eq_zero_iff_eq_C.mp hconstant
  have hc : c ≠ 0 := by
    intro hzero
    apply (Polynomial.leadingCoeff_ne_zero.mpr hf')
    rw [hlead, hzero, map_zero]
  let c' : k := algebraMap F k c
  have hc' : c' ≠ 0 := by
    simpa only [c', map_zero] using (algebraMap F k).injective.ne hc
  let φ : MvPolynomial σ F →+* Polynomial k := (aeval s).toRingHom
  let raw : Polynomial (Polynomial k) := f'.map φ
  have hmaplead : φ f'.leadingCoeff = Polynomial.C c' := by
    rw [hlead]
    change aeval s (C c) = Polynomial.C c'
    rw [aeval_C, Polynomial.algebraMap_apply]
  have hmaplead0 : φ f'.leadingCoeff ≠ 0 := by
    rw [hmaplead]
    exact Polynomial.C_ne_zero.mpr hc'
  have hrawlead : raw.leadingCoeff = Polynomial.C c' :=
    (Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ hmaplead0).trans hmaplead
  have hrawdegree : raw.natDegree = f.totalDegree :=
    (Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hmaplead0).trans hfdegree
  let d : Polynomial k := Polynomial.C c'⁻¹
  let P := raw * Polynomial.C d
  have hP : P.Monic := by
    apply Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [hrawlead]
    change Polynomial.C c' * Polynomial.C c'⁻¹ = 1
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc', map_one]
  have hPdegree : P.natDegree = f.totalDegree := by
    rw [Polynomial.natDegree_mul (left_ne_zero_of_mul hP.ne_zero)
      (right_ne_zero_of_mul hP.ne_zero), Polynomial.natDegree_C, add_zero, hrawdegree]
  have hPcoeff : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree := by
    intro i hi
    have hicoeff : (raw.coeff i).natDegree ≤ (f'.coeff i).totalDegree := by
      rw [show raw = f'.map φ from rfl, Polynomial.coeff_map]
      change (aeval s (f'.coeff i)).natDegree ≤ _
      exact polynomial_natDegree_aeval_le_totalDegree s hs _
    have hioriginal := totalDegree_coeff_optionEquivLeft_add_le F σ f i (hi.trans_eq hPdegree)
    have hiraw : (raw.coeff i).natDegree + i ≤ f.totalDegree :=
      (Nat.add_le_add_right hicoeff i).trans hioriginal
    have hip : (P.coeff i).natDegree ≤ (raw.coeff i).natDegree := by
      rw [Polynomial.coeff_mul_C]
      exact Polynomial.natDegree_mul_C_le _ _
    exact ((Nat.add_le_add_right hip i).trans hiraw).trans_eq hPdegree.symm
  have hrawroot : Polynomial.aeval v raw = 0 := by
    let ψ : Polynomial (MvPolynomial σ F) →ₐ[F] L :=
      ((Polynomial.aeval v).restrictScalars F).comp (Polynomial.mapAlgHom (aeval s))
    have hψ : ψ.comp (optionEquivLeft F σ).toAlgHom = aeval
        (fun i => i.elim v (fun j => algebraMap (Polynomial k) L (s j))) := by
      apply MvPolynomial.algHom_ext
      intro i
      cases i <;> simp [ψ]
    exact (AlgHom.congr_fun hψ f).trans hroot
  refine ⟨P, hP, hPdegree, hPcoeff, ?_⟩
  change Polynomial.aeval v (raw * Polynomial.C d) = 0
  rw [map_mul, hrawroot, zero_mul]

end DimensionFourDependence
