import DimensionFourDependence.CompleteIntersectionPair

/-! # Hilbert functions of homogeneous relation ideals

The Hilbert function is the dimension of the degree-`d` polynomial space
modulo its relations in the ideal. Its monotonicity will transfer an
intersection bound to the actual fiber component.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L σ : Type*} [Field L]

/-- A homogeneous polynomial space in finitely many variables is finite-dimensional. -/
@[instance]
theorem homogeneousPiece_finite [Finite σ] (d : ℕ) :
    Module.Finite L (homogeneousSubmodule σ L d) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ L d)

/-- Counting degree-`d` monomials gives the dimension of a homogeneous piece. -/
theorem homogeneousPiece_finrank (d : ℕ) :
    finrank L (homogeneousSubmodule σ L d) = (Nat.card σ + d - 1).choose d := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  change finrank L (restrictSupport L {m : σ →₀ ℕ | m.degree = d}) = _
  rw [finrank_eq_nat_card_basis (basisRestrictSupport L {m : σ →₀ ℕ | m.degree = d})]
  change Nat.card {m : σ →₀ ℕ // m.sum (fun _ => id) = d} = _
  rw [← Nat.card_congr (Sym.equivNatSum σ d), Sym.natCard_sym_eq_choose]

/-- Homogeneous relations of degree `d` in an ideal. -/
noncomputable def homogeneousRelationSpace (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    Submodule L (homogeneousSubmodule σ L d) :=
  (I.restrictScalars L).comap (homogeneousSubmodule σ L d).subtype

/-- The degree-`d` part of the quotient's Hilbert function. This definition
also makes sense before homogeneity of the ideal has been established. -/
noncomputable def projectiveHilbertFunction (I : Ideal (MvPolynomial σ L)) (d : ℕ) : ℕ :=
  finrank L ((homogeneousSubmodule σ L d) ⧸ homogeneousRelationSpace I d)

theorem projectiveHilbertFunction_add_relation_finrank [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    projectiveHilbertFunction I d + finrank L (homogeneousRelationSpace I d) =
      finrank L (homogeneousSubmodule σ L d) :=
  Submodule.finrank_quotient_add_finrank _

/-- Adding relations can only decrease the Hilbert function. -/
theorem projectiveHilbertFunction_antitone [Finite σ]
    {I J : Ideal (MvPolynomial σ L)} (hIJ : I ≤ J) (d : ℕ) :
    projectiveHilbertFunction J d ≤ projectiveHilbertFunction I d := by
  have hrel : homogeneousRelationSpace I d ≤ homogeneousRelationSpace J d := fun _ hp => hIJ hp
  have hdim := Submodule.finrank_mono hrel
  have hi := projectiveHilbertFunction_add_relation_finrank I d
  have hj := projectiveHilbertFunction_add_relation_finrank J d
  omega

theorem projectiveHilbertFunction_le_monomial_count [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (d : ℕ) :
    projectiveHilbertFunction I d ≤ (Nat.card σ + d - 1).choose d := by
  have h := projectiveHilbertFunction_add_relation_finrank I d
  rw [homogeneousPiece_finrank] at h
  omega

/-- In four homogeneous coordinates the unrestricted piece has size `choose(d+3,3)`. -/
theorem homogeneousPiece_four_finrank (d : ℕ) :
    finrank L (homogeneousSubmodule (Option (Fin 3)) L d) = (d + 3).choose 3 := by
  rw [homogeneousPiece_finrank]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  have he : 3 + 1 + d - 1 = d + 3 := by omega
  rw [he, ← Nat.choose_symm (by omega : d ≤ d + 3)]
  congr 1
  omega

end DimensionFourDependence
