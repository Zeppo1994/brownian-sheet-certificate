import BrownianSharp.TorusFoundations
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic

/-!
A concrete smooth dyadic resolution for the literal norms in the extended
manuscript. Existing v10 Fourier coefficients, torus Haar measure and entropy
numbers are reused. These smooth blocks are kept distinct from v10's hard
frequency blocks; no unproved norm equivalence is used as an identification.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace BrownianSharp.SmoothResolution
open BrownianSharp.Torus

/-- Smooth even cutoff, one on [-1,1] and zero outside (-2,2). -/
def cutoff (ξ : ℝ) : ℝ := 1 - Real.smoothTransition ((ξ ^ 2 - 1) / 3)

theorem cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff := by
  unfold cutoff
  fun_prop

theorem cutoff_eq_one {ξ : ℝ} (hξ : |ξ| ≤ 1) : cutoff ξ = 1 := by
  have hs : ξ ^ 2 ≤ 1 := by nlinarith [abs_le.mp hξ |>.1, abs_le.mp hξ |>.2]
  simp [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith : (ξ ^ 2 - 1) / 3 ≤ 0)]

theorem cutoff_eq_zero {ξ : ℝ} (hξ : 2 ≤ |ξ|) : cutoff ξ = 0 := by
  have hs : 4 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
  simp [cutoff, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ (ξ ^ 2 - 1) / 3)]

theorem cutoff_even (ξ : ℝ) : cutoff (-ξ) = cutoff ξ := by simp [cutoff]

theorem cutoff_bounds (ξ : ℝ) : 0 ≤ cutoff ξ ∧ cutoff ξ ≤ 1 := by
  constructor <;> dsimp [cutoff] <;>
    linarith [Real.smoothTransition.nonneg ((ξ ^ 2 - 1) / 3),
      Real.smoothTransition.le_one ((ξ ^ 2 - 1) / 3)]

/-- Telescoping smooth scalar dyadic multipliers, including the low block. -/
def scalarBlock (s : ℕ) (ξ : ℝ) : ℝ :=
  if s = 0 then cutoff ξ else
    cutoff (ξ / (2 : ℝ) ^ s) - cutoff (ξ / (2 : ℝ) ^ (s - 1))

theorem scalarBlock_smooth (s : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarBlock s) := by
  unfold scalarBlock cutoff
  split_ifs <;> fun_prop

/-- The scalar dyadic resolution telescopes exactly at every finite cutoff. -/
theorem scalarBlock_sum (N : ℕ) (ξ : ℝ) :
    (∑ s ∈ Finset.range (N + 1), scalarBlock s ξ) = cutoff (ξ / (2 : ℝ) ^ N) := by
  induction N with
  | zero => simp [scalarBlock]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [scalarBlock, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    ring

/-- For each frequency, sufficiently large finite dyadic sums equal one. -/
theorem scalarBlock_sum_eventually_one (ξ : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, (∑ s ∈ Finset.range (N + 1), scalarBlock s ξ) = 1 := by
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hpow.eventually_ge_atTop |ξ|] with N hN
  rw [scalarBlock_sum]
  apply cutoff_eq_one
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N)]
  exact (div_le_one (by positivity : (0 : ℝ) < 2 ^ N)).2 hN

/-- A finite frequency box containing the support of the tensor multiplier. -/
def frequencyBox {d : ℕ} (s : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-((2 : ℤ) ^ (s i + 1))) ((2 : ℤ) ^ (s i + 1))

/-- Tensor smooth multiplier on actual integer torus frequencies. -/
def tensorMultiplier {d : ℕ} (s : Fin d → ℕ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, scalarBlock (s i) (k i)

/-- Smooth Fourier block of the actual input function. -/
def block {d : ℕ} (s : Fin d → ℕ) (f : RealPeriodic d) :
    C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial (frequencyBox s)
    (fun k => (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k)

/-- Weighted block size in the normalized torus Lp norm. -/
def weightedBlockNorm {d : ℕ} (p : ENNReal) (r : ℝ)
    (s : Fin d → ℕ) (f : RealPeriodic d) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) *
    eLpNorm (fun x => block s f x) p (volume : Measure (UnitAddTorus (Fin d)))

/-- The manuscript's smooth-resolution Besov unit ball. -/
def BesovUnitBall {d : ℕ} (p : ENNReal) (r : ℝ) (θ : ENNReal)
    (f : RealPeriodic d) : Prop :=
  if θ = ⊤ then ∀ s, weightedBlockNorm p r s f ≤ 1 else
    ∑' s, (weightedBlockNorm p r s f) ^ θ.toReal ≤ 1

/-- The manuscript's pointwise smooth dyadic square function, with extended
values retained so divergent series cannot become zero by conversion. -/
def squareFunctionSquared {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) : ENNReal :=
  ∑' s : Fin d → ℕ, ENNReal.ofReal
    ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) * ‖block s f x‖ ^ 2)

/-- The mixed Bessel-potential norm as the manuscript's square-function norm.
The p-th power integral is compared with one, avoiding any ∞→real coercion. -/
def SobolevUnitBall {d : ℕ} (p r : ℝ) (f : RealPeriodic d) : Prop :=
  (∫⁻ x, (squareFunctionSquared r f x) ^ (p / 2)
    ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1

def NikolskyUnitBall {d : ℕ} (p : ENNReal) (r : ℝ)
    (f : RealPeriodic d) : Prop := BesovUnitBall p r ⊤ f

end BrownianSharp.SmoothResolution
