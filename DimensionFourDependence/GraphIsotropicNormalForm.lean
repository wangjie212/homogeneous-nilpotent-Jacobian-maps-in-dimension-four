import DimensionFourDependence.CoefficientIsotropicBasis

/-! # Constructing full-source isotropic coordinates and the quadratic normal form

The graph hyperplane lifts an isotropic basis in three coordinates to
the original four source coordinates. Its translation has only the last
chart coordinate nonzero. The weighted radial pairing then gives (3.3).
-/

namespace DimensionFourDependence

open Matrix

variable {E G : Type*} [Field E] [Field G] [Algebra E G]

/-- The affine graph equation determines the fourth coordinate of a
three-coordinate radial/isotropic decomposition, in the original chart. -/
theorem graph_coordinate_decomposition_lift
    (p : Equiv.Perm (Fin 4)) (x : Fin 4 → G) (Y : Fin 4 → E)
    (g Z W : Fin 3 → E) (c : E) (τ s t : G)
    (hY : Y (p 3) = ∑ i : Fin 3, g i * Y (p i.castSucc))
    (hgraph : x (p 3) = (∑ i : Fin 3, algebraMap E G (g i) * x (p i.castSucc)) + algebraMap E G c)
    (hx : ∀ i : Fin 3, x (p i.castSucc) = τ * algebraMap E G (Y (p i.castSucc)) +
      s * algebraMap E G (Z i) + t * algebraMap E G (W i)) :
    let Z' : Fin 4 → E := (Fin.snoc Z (∑ i, g i * Z i)) ∘ p.symm
    let W' : Fin 4 → E := (Fin.snoc W (∑ i, g i * W i)) ∘ p.symm
    ∀ j, x j = τ * algebraMap E G (Y j) + s * algebraMap E G (Z' j) +
      t * algebraMap E G (W' j) + algebraMap E G ((Pi.single (p 3) c : Fin 4 → E) j) := by
  dsimp only
  intro j
  obtain ⟨k, rfl⟩ := p.surjective j
  simp only [Function.comp_apply, p.symm_apply_apply]
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [Fin.snoc_last, Fin.snoc_last]
    change x (p 3) = τ * algebraMap E G (Y (p 3)) +
      s * algebraMap E G (∑ i, g i * Z i) + t * algebraMap E G (∑ i, g i * W i) +
      algebraMap E G ((Pi.single (p 3) c : Fin 4 → E) (p 3))
    rw [Pi.single_eq_same, hgraph, hY]
    simp_rw [hx]
    simp only [map_sum, map_mul, Finset.mul_sum]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    have hi : p i.castSucc ≠ p 3 := by
      apply p.injective.ne
      exact Fin.castSucc_ne_last i
    rw [Pi.single_eq_of_ne hi, map_zero, add_zero]
    exact hx i

variable [CharZero E] [IsAlgClosed E]

omit [IsAlgClosed E] in
/-- A radial isotropic pair and the graph and quadratic equations
construct the full-source normal form, without a matrix rank assumption
after extension of the original coefficient field. -/
theorem graph_isotropic_quadratic_normal_form_of_directions
    (p : Equiv.Perm (Fin 4)) (x : Fin 4 → G) (Y : Fin 4 → E)
    (g a : Fin 3 → E) (T : Matrix (Fin 3) (Fin 3) E)
    (hT : ∀ i j, T i j = T j i)
    (Z₀ W₀ : Fin 3 → E) (hZ : matrixBilinearPairing T Z₀ Z₀ = 0)
    (hW : matrixBilinearPairing T W₀ W₀ = 0) (hκ : matrixBilinearPairing T Z₀ W₀ ≠ 0)
    (hY0 : (fun i : Fin 3 => Y (p i.castSucc)) ≠ 0)
    (hTY : ∀ j : Fin 3, (∑ i : Fin 3, Y (p i.castSucc) * T i j) = 0)
    (θ c q : E)
    (hY : Y (p 3) = ∑ i : Fin 3, g i * Y (p i.castSucc))
    (hgraph : x (p 3) = (∑ i : Fin 3, algebraMap E G (g i) * x (p i.castSucc)) + algebraMap E G c)
    (hweight : (∑ i : Fin 3, a i * Y (p i.castSucc)) = θ * c)
    (hq : algebraMap E G q = quadraticExpression (fun i => algebraMap E G (a i))
      (T.map (algebraMap E G)) (fun i : Fin 3 => x (p i.castSucc))) :
    ∃ (Z W : Fin 4 → E) (τ s t : G),
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => Z (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => W (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) ≠ 0 ∧
      LinearIndependent E ![(fun i : Fin 3 => Y (p i.castSucc)),
        (fun i : Fin 3 => Z (p i.castSucc)), (fun i : Fin 3 => W (p i.castSucc))] ∧
      (∀ j, x j = τ * algebraMap E G (Y j) + s * algebraMap E G (Z j) +
        t * algebraMap E G (W j) + algebraMap E G ((Pi.single (p 3) c : Fin 4 → E) j)) ∧
      algebraMap E G q = algebraMap E G θ * algebraMap E G c * τ +
        algebraMap E G (∑ i : Fin 3, a i * Z (p i.castSucc)) * s +
        algebraMap E G (∑ i : Fin 3, a i * W (p i.castSucc)) * t +
        algebraMap E G (matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc))
          (fun i : Fin 3 => W (p i.castSucc))) * s * t := by
  let : CharZero G := charZero_of_injective_algebraMap (algebraMap E G).injective
  have hRad : T *ᵥ (fun i : Fin 3 => Y (p i.castSucc)) = 0 := by
    funext j
    change (∑ i : Fin 3, T j i * Y (p i.castSucc)) = 0
    calc
      _ = ∑ i : Fin 3, Y (p i.castSucc) * T i j :=
        Finset.sum_congr rfl (fun i _ => by rw [hT j i, mul_comm])
      _ = 0 := hTY j
  have hYpair (v : Fin 3 → E) : matrixBilinearPairing T (fun i : Fin 3 => Y (p i.castSucc)) v = 0 := by
    rw [matrixBilinearPairing_symmetric T hT, matrixBilinearPairing_eq_dot_mulVec, hRad, dotProduct_zero]
  have hli := radical_isotropic_triple_independent T hT (fun i : Fin 3 => Y (p i.castSucc))
    Z₀ W₀ hY0 hYpair hZ hW hκ
  obtain ⟨τ, s, t, hx⟩ := radial_isotropic_coordinates_over T hT
    (fun i : Fin 3 => Y (p i.castSucc)) Z₀ W₀ hY0 hTY hZ hW hκ (fun i : Fin 3 => x (p i.castSucc))
  let Z : Fin 4 → E := (Fin.snoc Z₀ (∑ i, g i * Z₀ i)) ∘ p.symm
  let W : Fin 4 → E := (Fin.snoc W₀ (∑ i, g i * W₀ i)) ∘ p.symm
  have hZchart : (fun i : Fin 3 => Z (p i.castSucc)) = Z₀ := by
    funext i
    simp only [Z, Function.comp_apply, p.symm_apply_apply, Fin.snoc_castSucc]
  have hWchart : (fun i : Fin 3 => W (p i.castSucc)) = W₀ := by
    funext i
    simp only [W, Function.comp_apply, p.symm_apply_apply, Fin.snoc_castSucc]
  refine ⟨Z, W, τ, s, t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hZchart] using hZ
  · simpa only [hWchart] using hW
  · simpa only [hZchart, hWchart] using hκ
  · simpa only [hZchart, hWchart] using hli
  · exact graph_coordinate_decomposition_lift p x Y g Z₀ W₀ c τ s t hY hgraph hx
  · have hcoords : (fun i : Fin 3 => x (p i.castSucc)) =
        fun i : Fin 3 => τ * algebraMap E G (Y (p i.castSucc)) +
          s * algebraMap E G (Z₀ i) + t * algebraMap E G (W₀ i) := funext hx
    have he := quadraticExpression_radial_isotropic_base_change (A := G)
      a T hT (fun i : Fin 3 => Y (p i.castSucc)) hTY
      (fun i => algebraMap E G (Z₀ i)) (fun i => algebraMap E G (W₀ i))
      (by rw [matrixBilinearPairing_map, hZ, map_zero])
      (by rw [matrixBilinearPairing_map, hW, map_zero]) θ c τ s t hweight
    rw [← hcoords, matrixBilinearPairing_map] at he
    have heq := hq.trans he
    simpa only [Z, W, Function.comp_apply, p.symm_apply_apply, Fin.snoc_castSucc,
      ← map_mul, ← map_sum] using heq

/-- From a rank-two radial Hessian, the graph equation and the actual
quadratic equation, construct both full-source isotropic directions,
their parameters, the nonzero mixed coefficient and equation (3.3). -/
theorem exists_graph_isotropic_quadratic_normal_form
    (p : Equiv.Perm (Fin 4)) (x : Fin 4 → G) (Y : Fin 4 → E)
    (g a : Fin 3 → E) (T : Matrix (Fin 3) (Fin 3) E)
    (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (hY0 : (fun i : Fin 3 => Y (p i.castSucc)) ≠ 0)
    (hTY : ∀ j : Fin 3, (∑ i : Fin 3, Y (p i.castSucc) * T i j) = 0)
    (θ c q : E)
    (hY : Y (p 3) = ∑ i : Fin 3, g i * Y (p i.castSucc))
    (hgraph : x (p 3) = (∑ i : Fin 3, algebraMap E G (g i) * x (p i.castSucc)) + algebraMap E G c)
    (hweight : (∑ i : Fin 3, a i * Y (p i.castSucc)) = θ * c)
    (hq : algebraMap E G q = quadraticExpression (fun i => algebraMap E G (a i))
      (T.map (algebraMap E G)) (fun i : Fin 3 => x (p i.castSucc))) :
    ∃ (Z W : Fin 4 → E) (τ s t : G),
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => Z (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => W (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) = 0 ∧
      matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc)) (fun i : Fin 3 => W (p i.castSucc)) ≠ 0 ∧
      LinearIndependent E ![(fun i : Fin 3 => Y (p i.castSucc)),
        (fun i : Fin 3 => Z (p i.castSucc)), (fun i : Fin 3 => W (p i.castSucc))] ∧
      (∀ j, x j = τ * algebraMap E G (Y j) + s * algebraMap E G (Z j) +
        t * algebraMap E G (W j) + algebraMap E G ((Pi.single (p 3) c : Fin 4 → E) j)) ∧
      algebraMap E G q = algebraMap E G θ * algebraMap E G c * τ +
        algebraMap E G (∑ i : Fin 3, a i * Z (p i.castSucc)) * s +
        algebraMap E G (∑ i : Fin 3, a i * W (p i.castSucc)) * t +
        algebraMap E G (matrixBilinearPairing T (fun i : Fin 3 => Z (p i.castSucc))
          (fun i : Fin 3 => W (p i.castSucc))) * s * t := by
  let : CharZero G := charZero_of_injective_algebraMap (algebraMap E G).injective
  have hRad : T *ᵥ (fun i : Fin 3 => Y (p i.castSucc)) = 0 := by
    funext j
    change (∑ i : Fin 3, T j i * Y (p i.castSucc)) = 0
    calc
      _ = ∑ i : Fin 3, Y (p i.castSucc) * T i j :=
        Finset.sum_congr rfl (fun i _ => by rw [hT j i, mul_comm])
      _ = 0 := hTY j
  obtain ⟨Z₀, W₀, hZ, hW, hκ, hli, _⟩ := rank_two_exists_radial_isotropic_basis T hT hrank
    (fun i : Fin 3 => Y (p i.castSucc)) hY0 hRad
  exact graph_isotropic_quadratic_normal_form_of_directions p x Y g a T hT
    Z₀ W₀ hZ hW hκ hY0 hTY θ c q hY hgraph hweight hq

end DimensionFourDependence
