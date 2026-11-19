import DimensionFourDependence.RadialDirectionNormalization

/-! # Constructing both normalized directions of equation (3.4)

Both directions can share the prescribed zero coordinate, while their
unit coordinates may differ. Their nonzero mixed pairing and independence
modulo the radial direction survive this normalization.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F] {n : ℕ}

/-- Construct simultaneous zero-coordinate normalizations for an
isotropic pair satisfying both equations (3.4). -/
theorem exists_normalized_isotropic_pair
    (T : Matrix (Fin n) (Fin n) F) (C : Fin n → Fin n → Fin n → F)
    (hT : ∀ i j, T i j = T j i)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (Y Z W : Fin n → F) (a : Fin n) (hYa : Y a ≠ 0)
    (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hCY : ∀ v w, tensorTrilinearPairing C Y v w = -matrixBilinearPairing T v w)
    (hZ : matrixBilinearPairing T Z Z = 0) (hW : matrixBilinearPairing T W W = 0)
    (hκ : matrixBilinearPairing T Z W ≠ 0)
    (hCZ : tensorTrilinearPairing C Z Z Z = 0) (hCW : tensorTrilinearPairing C W W W = 0) :
    ∃ (U V : Fin n → F) (b d : Fin n), U a = 0 ∧ U b = 1 ∧ b ≠ a ∧
      V a = 0 ∧ V d = 1 ∧ d ≠ a ∧
      matrixBilinearPairing T U U = 0 ∧ matrixBilinearPairing T V V = 0 ∧
      tensorTrilinearPairing C U U U = 0 ∧ tensorTrilinearPairing C V V V = 0 ∧
      matrixBilinearPairing T U V ≠ 0 ∧ LinearIndependent F ![Y, U, V] := by
  have hY0 : Y ≠ 0 := fun hz => hYa (congrFun hz a)
  have hli := radical_isotropic_triple_independent T hT Y Z W hY0 hY hZ hW hκ
  have hYZ : LinearIndependent F ![Y, Z] := by
    have he : (fun i : Fin 2 => ![Y, Z, W] i.castSucc) = ![Y, Z] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hli.comp Fin.castSucc (Fin.castSucc_injective 2)
  have hYW : LinearIndependent F ![Y, W] := by
    let j : Fin 2 → Fin 3 := ![0, 2]
    have hj : Function.Injective j := by decide
    have he : (fun i : Fin 2 => ![Y, Z, W] (j i)) = ![Y, W] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hli.comp j hj
  obtain ⟨U, b, r, s, hs, hU, hUa, hUb, hba⟩ := exists_normalized_radial_direction Y Z hYZ a hYa
  obtain ⟨V, d, r', s', hs', hV, hVa, hVd, hda⟩ := exists_normalized_radial_direction Y W hYW a hYa
  obtain ⟨hQU, hCU⟩ := radial_normalization_preserves_isotropy T C hT h12 h23 Y Z U hY hCY hZ hCZ r s hU
  obtain ⟨hQV, hCV⟩ := radial_normalization_preserves_isotropy T C hT h12 h23 Y W V hY hCY hW hCW r' s' hV
  have hUV : matrixBilinearPairing T U V ≠ 0 := by
    rw [radial_normalization_mixed_pairing T hT Y Z W U V hY r s r' s' hU hV]
    exact mul_ne_zero (mul_ne_zero hs hs') hκ
  exact ⟨U, V, b, d, hUa, hUb, hba, hVa, hVd, hda, hQU, hQV, hCU, hCV, hUV,
    radical_isotropic_triple_independent T hT Y U V hY0 hY hQU hQV hUV⟩

end DimensionFourDependence
