import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! The actual high/low coefficient split used for the real-interpolation
step, including the quantitative ℓ₂ and ℓ∞ endpoint bounds. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperSequenceSplit

def highPart {ι : Type*} (a : ι → ℝ≥0∞) (τ : ℝ≥0∞) (i : ι) : ℝ≥0∞ :=
  if τ < a i then a i else 0

def lowPart {ι : Type*} (a : ι → ℝ≥0∞) (τ : ℝ≥0∞) (i : ι) : ℝ≥0∞ :=
  if τ < a i then 0 else a i

theorem lowPart_le {ι : Type*} (a : ι → ℝ≥0∞) (τ : ℝ≥0∞) (i : ι) :
    lowPart a τ i ≤ τ := by
  unfold lowPart
  split_ifs with h
  · exact bot_le
  · exact le_of_not_gt h

theorem highPart_square_sum_le {ι : Type*} (a : ι → ℝ≥0∞)
    (θ : ℝ) (hθ : 2 ≤ θ) (τ : ℝ≥0∞) (hτ : 0 < τ) (hτtop : τ ≠ ∞)
    (hsum : ∑' i, (a i) ^ θ ≤ 1) :
    ∑' i, highPart a τ i ^ (2 : ℕ) ≤ τ ^ (2 - θ) := by
  have hθ0 : 0 < θ := by linarith
  have hfinite (i : ι) : a i ≠ ∞ := by
    have hterm : (a i) ^ θ < ∞ :=
      ((ENNReal.le_tsum i).trans hsum).trans_lt (by simp)
    exact ((ENNReal.rpow_lt_top_iff_of_pos hθ0).mp hterm).ne
  have hpoint (i : ι) :
      highPart a τ i ^ (2 : ℕ) ≤ τ ^ (2 - θ) * (a i) ^ θ := by
    unfold highPart
    split_ifs with hi
    · have hai : a i ≠ 0 := ne_of_gt (hτ.trans hi)
      have hneg : (a i) ^ (2 - θ) ≤ τ ^ (2 - θ) := by
        rw [show (2 : ℝ) - θ = -(θ - 2) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hi.le (by linarith))
      have hid : a i ^ (2 : ℕ) = (a i) ^ (2 - θ) * (a i) ^ θ := by
        rw [← ENNReal.rpow_add _ _ hai (hfinite i)]
        simp
      rw [hid]
      exact mul_le_mul hneg le_rfl (by positivity) (by positivity)
    · simp
  calc
    ∑' i, highPart a τ i ^ (2 : ℕ) ≤ ∑' i, τ ^ (2 - θ) * (a i) ^ θ :=
      ENNReal.tsum_le_tsum hpoint
    _ = τ ^ (2 - θ) * ∑' i, (a i) ^ θ := ENNReal.tsum_mul_left
    _ ≤ τ ^ (2 - θ) * 1 := mul_le_mul le_rfl hsum (by positivity) (by positivity)
    _ = τ ^ (2 - θ) := mul_one _

theorem term_le_one_of_power_sum_le_one {ι : Type*} (a : ι → ℝ≥0∞)
    (θ : ℝ) (hθ : 0 < θ) (hsum : ∑' i, (a i) ^ θ ≤ 1) (i : ι) :
    a i ≤ 1 := by
  have hterm := (ENNReal.le_tsum (f := fun i => (a i) ^ θ) i).trans hsum
  apply (ENNReal.rpow_le_rpow_iff hθ).mp
  simpa using hterm

def balancedThreshold (E₀ E₁ θ : ℝ) : ℝ := (E₀ / E₁) ^ (2 / θ)

theorem balancedThreshold_pos (E₀ E₁ θ : ℝ) (h₀ : 0 < E₀) (h₁ : 0 < E₁) :
    0 < balancedThreshold E₀ E₁ θ := Real.rpow_pos_of_pos (div_pos h₀ h₁) _

theorem balanced_endpoint_cost (E₀ E₁ θ : ℝ)
    (h₀ : 0 < E₀) (h₁ : 0 < E₁) (hθ : θ ≠ 0) :
    E₀ * balancedThreshold E₀ E₁ θ ^ (1 - θ / 2) +
      E₁ * balancedThreshold E₀ E₁ θ =
      2 * E₀ ^ (2 / θ) * E₁ ^ (1 - 2 / θ) := by
  let τ := balancedThreshold E₀ E₁ θ
  have hτ : 0 < τ := balancedThreshold_pos E₀ E₁ θ h₀ h₁
  have hlog : Real.log τ = (2 / θ) * (Real.log E₀ - Real.log E₁) := by
    dsimp [τ, balancedThreshold]
    rw [Real.log_rpow (div_pos h₀ h₁), Real.log_div h₀.ne' h₁.ne']
  have hfirst : E₀ * τ ^ (1 - θ / 2) =
      E₀ ^ (2 / θ) * E₁ ^ (1 - 2 / θ) := by
    rw [Real.rpow_def_of_pos hτ, Real.rpow_def_of_pos h₀,
      Real.rpow_def_of_pos h₁, ← Real.exp_log h₀, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hlog, Real.log_exp]
    field_simp
    ring
  have hsecond : E₁ * τ = E₀ ^ (2 / θ) * E₁ ^ (1 - 2 / θ) := by
    nth_rw 1 [← Real.exp_log h₁, ← Real.exp_log hτ]
    rw [Real.rpow_def_of_pos h₀, Real.rpow_def_of_pos h₁,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hlog]
    ring
  change E₀ * τ ^ (1 - θ / 2) + E₁ * τ = _
  rw [hfirst, hsecond]
  ring

end BrownianSharp.AlignmentPaperSequenceSplit

