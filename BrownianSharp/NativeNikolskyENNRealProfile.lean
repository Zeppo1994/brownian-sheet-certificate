import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Convert the two-sided dyadic Nikolsky profile between real and ENNReal
coordinates. This isolates the conversion needed by the fixed-shape endpoint. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp

/-- ENNReal version of the coordinatewise two-sided geometric shape weight. -/
def nativeNikolskyENNRealShapeWeight {d : ℕ} (t : Fin d → ℕ)
    (qlow qhigh : ENNReal) (s : Fin d → ℕ) : ENNReal :=
  ∏ i : Fin d, if t i ≤ s i then qlow ^ (s i - t i)
    else qhigh ^ (t i - s i)

/-- Real version of the coordinatewise two-sided geometric shape weight. -/
def nativeNikolskyRealShapeWeight {d : ℕ} (t : Fin d → ℕ)
    (qlow qhigh : ℝ) (s : Fin d → ℕ) : ℝ :=
  ∏ i : Fin d, if t i ≤ s i then qlow ^ (s i - t i)
    else qhigh ^ (t i - s i)

theorem nativeNikolskyShapeWeight_eq_ofReal_real
    {d : ℕ} (t : Fin d → ℕ) (qlow qhigh : ℝ)
    (hqlow : 0 ≤ qlow) (hqhigh : 0 ≤ qhigh) (s : Fin d → ℕ) :
    nativeNikolskyENNRealShapeWeight t (ENNReal.ofReal qlow) (ENNReal.ofReal qhigh) s =
      ENNReal.ofReal (nativeNikolskyRealShapeWeight t qlow qhigh s) := by
  unfold nativeNikolskyENNRealShapeWeight nativeNikolskyRealShapeWeight
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i hi
    split_ifs
    · rw [ENNReal.ofReal_pow hqlow]
    · rw [ENNReal.ofReal_pow hqhigh]
  · intro i hi
    split_ifs <;> positivity

/-- The real low and high dyadic profile bases are strictly inside `(0,1)`
under the exact Nikolsky parameter inequalities. -/
theorem real_dyadic_profile_bases_lt_one {r K : ℝ}
    (hr : 0 < r) (hKr : r < K) :
    (2 : ℝ) ^ (-r) < 1 ∧ (2 : ℝ) ^ (-(K-r)) < 1 := by
  constructor
  · rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (inv_lt_one₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) r)).2
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hr
  · have hKr' : 0 < K-r := by linarith
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (inv_lt_one₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (K-r))).2
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hKr'

theorem ennreal_dyadic_profile_bases_lt_one {r K : ℝ}
    (hr : 0 < r) (hKr : r < K) :
    ENNReal.ofReal ((2 : ℝ) ^ (-r)) < 1 ∧
      ENNReal.ofReal ((2 : ℝ) ^ (-(K-r))) < 1 := by
  rcases real_dyadic_profile_bases_lt_one hr hKr with ⟨hlow, hhigh⟩
  exact ⟨ENNReal.ofReal_lt_one.mpr hlow, ENNReal.ofReal_lt_one.mpr hhigh⟩

end BrownianSharp
