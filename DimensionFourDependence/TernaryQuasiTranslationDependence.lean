import DimensionFourDependence.HomogeneousQuasiTranslationSpan
import DimensionFourDependence.PrimeQuotientCodimensionOne
import DimensionFourDependence.OutputCoordinateFieldEquiv
import DimensionFourDependence.SmallerSourceDependenceTransport

/-! # The homogeneous ternary zero-acceleration branch over original constants -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 3) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 3) K)

/-- The actual image relation quotient has the actual Jacobian
rank as its transcendence degree in three source variables. -/
theorem ternary_image_relation_quotient_trdeg_eq_jacobian_rank (H : Fin 3 → R₀) :
    Algebra.trdeg K (R₀ ⧸ fiberVanishingIdeal (L := K) (fun i => algebraMap R₀ F₀ (H i))) =
      polyRank (jac H) := by
  let Y : Fin 3 → F₀ := fun i => algebraMap R₀ F₀ (H i)
  have hfield : Algebra.trdeg K (fullOutputField (K := K) Y) = polyRank (jac H) := by
    have he := rationalJacobian_rank_eq_output_trdeg Y
    rw [rationalJacobian_polynomial H] at he
    exact he
  calc
    _ = Algebra.trdeg K (FractionRing (R₀ ⧸ fiberVanishingIdeal (L := K) Y)) :=
      (fractionRing_trdeg_eq_base (k := K) (A := R₀ ⧸ fiberVanishingIdeal (L := K) Y)).symm
    _ = Algebra.trdeg K (fullOutputField (K := K) Y) := (outputCoordinateFunctionFieldEquiv (K := K) Y).trdeg_eq
    _ = _ := hfield

/-- A primitive positive homogeneous ternary quasi-translation
cannot exist. Its actual image relation prime would be a principal
height-one prime containing every primitive component. -/
theorem primitive_positive_homogeneous_ternary_zero_acceleration_impossible
    (u : Fin 3 → R₀) {e : ℕ} (he : 0 < e) (hu : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) : False := by
  have hrge := two_le_polyRank_jac_of_isPrimitiveVec u he hu hhom hprim
  have hleft : u ᵥ* (jac u)ᵀ = 0 := by simpa only [Matrix.vecMul_transpose] using hacc
  have hrlt := polyRank_lt_of_vecMul_eq_zero (jac u)ᵀ u hu hleft
  have hrank : polyRank (jac u) = 2 := by
    simp only [polyRank, Matrix.transpose_map, Matrix.rank_transpose] at hrlt
    change polyRank (jac u) < 3 at hrlt
    omega
  let I := fiberVanishingIdeal (L := K) (fun i => algebraMap R₀ F₀ (u i))
  have hdim : Algebra.trdeg K (R₀ ⧸ I) = 2 :=
    (ternary_image_relation_quotient_trdeg_eq_jacobian_rank u).trans (congrArg (fun n : ℕ => (n : Cardinal)) hrank)
  have hheight : I.height = 1 := prime_height_eq_one_of_quotient_trdeg_two (by simp) I hdim
  obtain ⟨δ, hI⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
  have hmem (i : Fin 3) : u i ∈ I := by
    change aeval (fun j => algebraMap R₀ F₀ (u j)) (u i) = 0
    rw [← aeval_polynomial_to_fraction,
      homogeneous_quasi_translation_vanishes_on_its_own_image u he hhom hacc, map_zero]
  have hunit : IsUnit δ := hprim δ (fun i => Ideal.mem_span_singleton.mp (by simpa only [hI] using hmem i))
  exact (inferInstance : I.IsPrime).ne_top (hI.trans (Ideal.span_singleton_eq_top.mpr hunit))

/-- Every homogeneous ternary quasi-translation of positive degree
has dependent components over its original characteristic-zero field.
The primitive factor and all image-prime arguments are constructed. -/
theorem positive_homogeneous_ternary_zero_acceleration_componentsDependent
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hacc : jac H *ᵥ H = 0) : ComponentsDependent H := by
  by_contra hind
  have hLI := linearIndependent_of_componentsIndependent H hind
  have hH0 : H ≠ 0 := by intro hz; exact hLI.ne_zero 0 (congrFun hz 0)
  obtain ⟨g, u, c, _hc, hg, _hgh, huh, hprim, hHu⟩ := exists_primitive_factorization d H hH hH0
  have hindU : ¬ComponentsDependent u := by
    intro hdep
    apply hind
    rw [hHu]
    exact componentsDependent_common_factor u g hdep
  have hLIU := linearIndependent_of_componentsIndependent u hindU
  have hu : u ≠ 0 := by intro hz; exact hLIU.ne_zero 0 (congrFun hz 0)
  have hacc' : jac (fun i => g * u i) *ᵥ (fun i => g * u i) = 0 := hHu ▸ hacc
  have hred := (zero_acceleration_common_factor_constructs_invariant_factor_and_reduced_direction g hg u hu hacc').2
  have he : 0 < d - c := by
    by_contra hn
    have he0 : d - c = 0 := by omega
    have hconst (i) : u i = C ((u i).coeff 0) := eq_C_of_isHomogeneous_zero (he0 ▸ huh i)
    have hscalar : LinearIndependent K (fun i : Fin 3 => (u i).coeff 0) := by
      apply LinearIndependent.of_comp (Algebra.linearMap K R₀)
      convert hLIU using 1
      funext i
      exact (hconst i).symm
    have hbound := hscalar.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_self] at hbound
    omega
  exact primitive_positive_homogeneous_ternary_zero_acceleration_impossible u he hu huh hprim hred

/-- The entire squared-Jacobian Euler-zero branch of ternary
homogeneous nilpotent dependence, without any nilpotence assumption. -/
theorem positive_homogeneous_ternary_squared_jacobian_euler_zero_componentsDependent
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hzero : jac H ^ 2 *ᵥ coordVec = 0) : ComponentsDependent H := by
  have he := hzero
  rw [pow_two, ← Matrix.mulVec_mulVec, euler_identity H hH, Matrix.mulVec_smul] at he
  have hacc : jac H *ᵥ H = 0 := (smul_eq_zero.mp he).resolve_left (by exact_mod_cast hd.ne')
  exact positive_homogeneous_ternary_zero_acceleration_componentsDependent H hd hH hacc

/-- A remaining independent original ternary map has a nonzero
second Jacobian orbit on its source Euler vector. -/
theorem independent_positive_homogeneous_ternary_second_jacobian_orbit_ne_zero
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H) :
    jac H ^ 2 *ᵥ coordVec ≠ 0 :=
  fun hz => hind (positive_homogeneous_ternary_squared_jacobian_euler_zero_componentsDependent H hd hH hz)

end DimensionFourDependence
