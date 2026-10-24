import BrownianSharp.QueryRecovery

/-!
# Exact fair Parseval identity for the complete query

Adding an independent dummy coordinate preserves uniform means. Tensor
orthogonality therefore gives the energy identity in the original cube,
including the scalar and every admitted strictly coarser coefficient.
-/

open scoped BigOperators

namespace HaarQuarter

theorem uniform_mean_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (e : ι ≃ κ) (F : κ → ℝ) :
    mean (uniformLaw ι) (fun x => F (e x)) = mean (uniformLaw κ) F := by
  unfold mean uniformLaw
  rw [← Finset.mul_sum, ← Finset.mul_sum, Fintype.card_congr e]
  congr 1
  exact e.sum_comp F

theorem uniform_mean_product_snd {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (F : κ → ℝ) :
    mean (uniformLaw (ι × κ)) (fun p => F p.2) = mean (uniformLaw κ) F := by
  classical
  have hι : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hκ : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold mean uniformLaw
  rw [← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  field_simp

def fullCubeEquiv (D N : ℕ) : SignCube (D + 1) N ≃ ((Fin N → Bool) × SignCube D N) where
  toFun z := (z.first, unpackFullCube z)
  invFun p := ⟨p.1, Fin.cons p.2.first p.2.transverse⟩
  left_inv z := by
    cases z with
    | mk first transverse =>
      dsimp [unpackFullCube]
      congr 1
      exact Fin.cons_self_tail transverse
  right_inv p := by
    rcases p with ⟨b, first, transverse⟩
    simp [unpackFullCube]

theorem fair_mean_unpackFullCube {D N : ℕ} (F : SignCube D N → ℝ) :
    mean (fairCubeLaw (D + 1) N) (fun z => F (unpackFullCube z)) =
      mean (fairCubeLaw D N) F := by
  calc
    _ = mean (uniformLaw ((Fin N → Bool) × SignCube D N)) (fun p => F p.2) :=
      uniform_mean_equiv (fullCubeEquiv D N) (fun p => F p.2)
    _ = _ := uniform_mean_product_snd F

noncomputable def queryEnergy {D N : ℕ} (β : CoefficientField D N)
    (x : SignCube D N) : ℝ :=
  ∑ l, ∑ v, if IsQueryProfile l v then (β l v x) ^ 2 else 0

theorem queryEnergy_nonneg {D N : ℕ} (β : CoefficientField D N) (x : SignCube D N) :
    0 ≤ queryEnergy β x := by
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro v hv
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

theorem fair_fullTensor_energy {D N : ℕ} (β : CoefficientField D N) :
    (∑ v, mean (fairCubeLaw (D + 1) N) (fun z => (fullTensorField β v z) ^ 2)) =
      mean (fairCubeLaw D N) (queryEnergy β) := by
  classical
  rw [sum_fullProfiles]
  unfold queryEnergy
  rw [mean_sum]
  simp_rw [mean_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hq : IsQueryProfile l v
  · simp only [fullTensorField, Fin.cons_zero, Fin.tail_cons, ite_eq_left hq]
    exact fair_mean_unpackFullCube (fun x => (β l v x) ^ 2)
  · simp [fullTensorField, hq, mean_const]

theorem fair_query_mean {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (c₀ : ℝ) :
    mean (fairCubeLaw D N) (rowPolynomial c₀ (queryLevel β)) = c₀ := by
  have h := fair_tensorPolynomial_mean (Nat.succ_pos D) c₀ (fullTensorField β)
    (fullTensorField_legal β hβ)
  change mean (fairCubeLaw (D + 1) N) (fun z => tensorPolynomial c₀ (fullTensorField β) z) = c₀ at h
  simp_rw [fullTensor_signal] at h
  rw [fair_mean_unpackFullCube (rowPolynomial c₀ (queryLevel β))] at h
  exact h

theorem fair_query_parseval {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (c₀ : ℝ) :
    mean (fairCubeLaw D N) (fun x => (rowPolynomial c₀ (queryLevel β) x) ^ 2) =
      c₀ ^ 2 + mean (fairCubeLaw D N) (queryEnergy β) := by
  have h := fair_tensor_parseval (Nat.succ_pos D) c₀ (fullTensorField β)
    (fullTensorField_legal β hβ)
  simp_rw [fullTensor_signal] at h
  rw [fair_mean_unpackFullCube (fun x => (rowPolynomial c₀ (queryLevel β) x) ^ 2),
    fair_fullTensor_energy β] at h
  exact h

theorem query_scalar_bound {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (c₀ : ℝ)
    (hbound : ∀ x, |rowPolynomial c₀ (queryLevel β) x| ≤ 1) : |c₀| ≤ 1 := by
  rw [← fair_query_mean β hβ c₀]
  exact abs_mean_le_one _ _ hbound

theorem fair_query_energy_bound {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (c₀ : ℝ)
    (hbound : ∀ x, |rowPolynomial c₀ (queryLevel β) x| ≤ 1) :
    mean (fairCubeLaw D N) (queryEnergy β) ≤ 1 := by
  have hm : mean (fairCubeLaw D N) (fun x => (rowPolynomial c₀ (queryLevel β) x) ^ 2) ≤ 1 := by
    calc
      _ ≤ mean (fairCubeLaw D N) (fun _ => 1) := by
        apply mean_mono
        intro x
        have hb := hbound x
        nlinarith [sq_abs (rowPolynomial c₀ (queryLevel β) x),
          abs_nonneg (rowPolynomial c₀ (queryLevel β) x)]
      _ = 1 := mean_const _ _
  rw [fair_query_parseval β hβ c₀] at hm
  nlinarith [sq_nonneg c₀]

theorem queryLevel_bound {D N : ℕ} (β : CoefficientField D N)
    (hβ : ∀ l v, IsQueryProfile l v → ∀ x, |β l v x| ≤ 1)
    (l : Fin N) (x : SignCube D N) : |queryLevel β l x| ≤ (N : ℝ) ^ D := by
  classical
  unfold queryLevel
  calc
    _ ≤ ∑ v, |if IsQueryProfile l v then β l v x * profileWord x v else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : BoundedProfile D N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases hq : IsQueryProfile l v
      · simpa [hq, abs_mul, profileWord_abs] using hβ l v hq x
      · simp [hq]
    _ = _ := by simp

end HaarQuarter
