import BrownianSharp.NativeVarianceMean

/-! A deterministic positive-density subset of midpoint rows on which the
actual native Brownian variance is bounded below. -/

open scoped BigOperators

namespace BrownianSharp

/-- The mean lower bound for one actual native Brownian row. -/
noncomputable def nativeVarianceMeanLowerBound (d n : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ (n + 4 * d)) * Nat.choose (n + d - 1) (d - 1)

/-- Grid points whose native Brownian row variance is at least half the
proved mean lower bound. -/
noncomputable def NativeGoodGrid (d n : ℕ) :=
  {q : MidpointGridIndex d n //
    nativeVarianceMeanLowerBound d n / 2 ≤ nativeLayerRowVariance q}

noncomputable instance nativeGoodGridFintype (d n : ℕ) :
    Fintype (NativeGoodGrid d n) := by
  classical
  letI : Finite (NativeGoodGrid d n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

theorem nativeVarianceMeanLowerBound_pos {d n : ℕ} (hd : 0 < d) :
    0 < nativeVarianceMeanLowerBound d n := by
  unfold nativeVarianceMeanLowerBound
  have hc : 0 < Nat.choose (n + d - 1) (d - 1) := by
    apply Nat.choose_pos
    omega
  positivity

private theorem nativeGoodGrid_card_eq_filter {d n : ℕ} :
    Fintype.card (NativeGoodGrid d n) =
      (Finset.univ.filter (fun q : MidpointGridIndex d n =>
        nativeVarianceMeanLowerBound d n / 2 ≤ nativeLayerRowVariance q)).card := by
  classical
  let s : Finset (MidpointGridIndex d n) := Finset.univ.filter fun q =>
    nativeVarianceMeanLowerBound d n / 2 ≤ nativeLayerRowVariance q
  let e : NativeGoodGrid d n ≃ {q // q ∈ s} := {
    toFun := fun q => ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩⟩
    invFun := fun q => ⟨q.1, (Finset.mem_filter.mp q.2).2⟩
    left_inv q := by apply Subtype.ext; rfl
    right_inv q := by apply Subtype.ext; rfl
  }
  calc
    Fintype.card (NativeGoodGrid d n) = Fintype.card {q // q ∈ s} :=
      Fintype.card_congr e
    _ = s.card := Fintype.card_coe s
    _ = _ := rfl

/-- At least `1/(2·4^d)` of the midpoint grid belongs to the deterministic
good set. -/
theorem nativeGoodGrid_fraction_lower {d n : ℕ} (hd : 0 < d) :
    1 / (2 * (4 : ℝ) ^ d) ≤
      (Fintype.card (NativeGoodGrid d n) : ℝ) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let m := nativeVarianceMeanLowerBound d n
  have hm : 0 < m := by simpa [m] using nativeVarianceMeanLowerBound_pos hd
  have hmean : m ≤
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simpa [m, nativeVarianceMeanLowerBound] using
      (nativeLayerRowVariance_mean_lower (d := d) (n := n) hd)
  have hfrac := nativeLayerRowVariance_good_fraction hd m hm hmean
  have hcardEq : Fintype.card (NativeGoodGrid d n) =
      (Finset.univ.filter (fun q : MidpointGridIndex d n =>
        m / 2 ≤ nativeLayerRowVariance q)).card := by
    simpa [m] using nativeGoodGrid_card_eq_filter (d := d) (n := n)
  rw [← hcardEq] at hfrac
  have hchoose : 0 < Nat.choose (n + d - 1) (d - 1) := by
    apply Nat.choose_pos
    omega
  have hratio : m /
      (2 * ((1 / (2 : ℝ) ^ (n + 2 * d)) *
        Nat.choose (n + d - 1) (d - 1))) = 1 / (2 * (4 : ℝ) ^ d) := by
    dsimp [m, nativeVarianceMeanLowerBound]
    have hc : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast hchoose)
    have hp : (2 : ℝ) ^ (n + 4 * d) =
        (2 : ℝ) ^ (n + 2 * d) * (4 : ℝ) ^ d := by
      rw [show n + 4 * d = (n + 2 * d) + 2 * d by omega, pow_add]
      rw [show (4 : ℝ) ^ d = (2 : ℝ) ^ (2 * d) by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]]
    rw [hp]
    field_simp
    <;> ring
  rw [hratio] at hfrac
  simpa using hfrac

/-- The good subset is nonempty. -/
theorem nativeGoodGrid_nonempty {d n : ℕ} (hd : 0 < d) :
    Nonempty (NativeGoodGrid d n) := by
  classical
  have hgrid : 0 < (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simp [MidpointGridIndex, Fintype.card_pi]
  have hfrac := nativeGoodGrid_fraction_lower (d := d) (n := n) hd
  have hcard : 0 < (Fintype.card (NativeGoodGrid d n) : ℝ) := by
    have hpositive : 0 < 1 / (2 * (4 : ℝ) ^ d) := by positivity
    have hratio : 0 <
        (Fintype.card (NativeGoodGrid d n) : ℝ) /
          (Fintype.card (MidpointGridIndex d n) : ℝ) :=
      lt_of_lt_of_le hpositive hfrac
    have hnonneg : 0 ≤ (Fintype.card (NativeGoodGrid d n) : ℝ) := by positivity
    by_contra hnot
    have hz : (Fintype.card (NativeGoodGrid d n) : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    rw [hz] at hratio
    simp at hratio
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hcard)

/-- Every member of the good set satisfies its advertised variance floor. -/
theorem nativeGoodGrid_variance_floor {d n : ℕ} (q : NativeGoodGrid d n) :
    nativeVarianceMeanLowerBound d n / 2 ≤ nativeLayerRowVariance q.1 :=
  q.2

end BrownianSharp
