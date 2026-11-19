import DimensionFourDependence.SimpleFieldDegreeBound

/-! # A hypersurface equation gives a projection polynomial of bounded degree

Separate the fiber variable from the independent projection coordinates.
Specialization into the projection field retains a nonzero equation and
does not increase its degree. Its root and generating property then
construct the actual finite field degree bound.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {k K L σ : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- The given hypersurface equation, read as a univariate equation
over the actual projection coordinate field. -/
noncomputable def projectionDefiningPolynomial
    (s : σ → K) (f : MvPolynomial (Option σ) k) : Polynomial K :=
  Polynomial.map (MvPolynomial.aeval s).toRingHom (optionEquivLeft k σ f)

/-- Independent projection coordinates prevent a nonzero original
hypersurface equation from disappearing under coefficient specialization. -/
theorem projectionDefiningPolynomial_ne_zero
    (s : σ → K) (hs : AlgebraicIndependent k s)
    (f : MvPolynomial (Option σ) k) (hf : f ≠ 0) :
    projectionDefiningPolynomial s f ≠ 0 := by
  intro h
  have hmap := Polynomial.map_injective (MvPolynomial.aeval s).toRingHom
    (algebraicIndependent_iff_injective_aeval.mp hs)
  have hzero : optionEquivLeft k σ f = 0 :=
    hmap (by simpa only [projectionDefiningPolynomial, Polynomial.map_zero] using h)
  exact hf ((optionEquivLeft k σ).injective (by simpa only [map_zero] using hzero))

/-- The projection polynomial degree is bounded by the total degree
of the actual original hypersurface equation. -/
theorem projectionDefiningPolynomial_natDegree_le
    (s : σ → K) (f : MvPolynomial (Option σ) k) :
    (projectionDefiningPolynomial s f).natDegree ≤ f.totalDegree := by
  have hdegree : (projectionDefiningPolynomial s f).natDegree ≤
      (optionEquivLeft k σ f).natDegree := Polynomial.natDegree_map_le
  rw [MvPolynomial.natDegree_optionEquivLeft] at hdegree
  exact hdegree.trans (MvPolynomial.degreeOf_le_totalDegree f none)

/-- Evaluating the projection polynomial at the original fiber
coordinate is exactly evaluation of the original hypersurface equation. -/
theorem projectionDefiningPolynomial_aeval
    (s : σ → K) (x : L) (f : MvPolynomial (Option σ) k) :
    Polynomial.aeval x (projectionDefiningPolynomial s f) =
      MvPolynomial.aeval (fun i => i.elim x (fun j => algebraMap K L (s j))) f := by
  let φ : Polynomial (MvPolynomial σ k) →ₐ[k] L :=
    ((Polynomial.aeval x).restrictScalars k).comp (Polynomial.mapAlgHom (MvPolynomial.aeval s))
  have hφ : φ.comp (optionEquivLeft k σ).toAlgHom =
      MvPolynomial.aeval (fun i => i.elim x (fun j => algebraMap K L (s j))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [φ]
  exact AlgHom.congr_fun hφ f

/-- The original nonzero hypersurface equation constructs finiteness
of a generating projection fiber and bounds its actual field degree. -/
theorem projection_hypersurface_field_degree_le
    (s : σ → K) (hs : AlgebraicIndependent k s)
    (x : L) (hgen : IntermediateField.adjoin K {x} = ⊤)
    (f : MvPolynomial (Option σ) k) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval (fun i => i.elim x (fun j => algebraMap K L (s j))) f = 0) :
    Module.Finite K L ∧ Module.finrank K L ≤ f.totalDegree := by
  have hp := projectionDefiningPolynomial_ne_zero s hs f hf
  have hr : Polynomial.aeval x (projectionDefiningPolynomial s f) = 0 := by
    rw [projectionDefiningPolynomial_aeval, hroot]
  obtain ⟨hfinite, hdegree⟩ := generating_root_finite_and_degree_le x hgen _ hp hr
  exact ⟨hfinite, hdegree.trans (projectionDefiningPolynomial_natDegree_le s f)⟩

end DimensionFourDependence
