import BrownianSharp.PredictableSigns
import BrownianSharp.SourceQuery
import BrownianSharp.QuarterScale

/-!
# Alignment from information and variance budgets

Source: unrestricted quarter-gain proof, Section 5, Proposition AL.
First escape and the one-axis Gibbs bound are proved dependencies. The
information and variance budgets are explicit hypotheses here; their physical
stopped-law and matrix/Fourier derivations remain separate obligations.
-/

open Filter
open scoped BigOperators Topology

namespace HaarQuarter

theorem mean_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : PositiveLaw ι) (F : κ → ι → ℝ) :
    mean P (fun x => ∑ j, F j x) = ∑ j, mean P (F j) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The good-event pressure estimate plus the rare bad-event bound. -/
theorem variance_bound_of_good_bad {ι : Type*} [Fintype ι]
    (P : PositiveLaw ι) (good : ι → Prop) [DecidablePred good] (variance energy : ι → ℝ)
    (a T pressure badMass : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (henergy : ∀ x, 0 ≤ energy x)
    (hgood : ∀ x, good x → variance x ≤ a * energy x)
    (hbad : ∀ x, ¬ good x → variance x ≤ T)
    (hpressure : mean P energy ≤ pressure)
    (hbadMass : mean P (fun x => if good x then 0 else 1) ≤ badMass) :
    mean P variance ≤ a * pressure + T * badMass := by
  classical
  have hpoint : ∀ x, variance x ≤ a * energy x + T * (if good x then 0 else 1) := by
    intro x
    by_cases hg : good x
    · simpa [hg] using hgood x hg
    · have h := hbad x hg
      have hnonneg := mul_nonneg ha (henergy x)
      simp only [ite_eq_right hg, mul_one]
      linarith
  calc
    _ ≤ mean P (fun x => a * energy x + T * (if good x then 0 else 1)) := mean_mono P hpoint
    _ = a * mean P energy + T * mean P (fun x => if good x then 0 else 1) := mean_linear P _ _ _ _
    _ ≤ a * pressure + T * badMass :=
      add_le_add (mul_le_mul_of_nonneg_left hpressure ha) (mul_le_mul_of_nonneg_left hbadMass hT)

theorem abs_mean_le_mean_abs {ι : Type*} [Fintype ι]
    (P : PositiveLaw ι) (F : ι → ℝ) : |mean P F| ≤ mean P (fun x => |F x|) := by
  unfold mean
  calc
    _ ≤ ∑ x, |P.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_pos (P.positive x)]

theorem abs_mean_le_one {ι : Type*} [Fintype ι]
    (P : PositiveLaw ι) (Q : ι → ℝ) (hQ : ∀ x, |Q x| ≤ 1) : |mean P Q| ≤ 1 := by
  calc
    _ ≤ mean P (fun x => |Q x|) := abs_mean_le_mean_abs P Q
    _ ≤ mean P (fun _ => 1) := mean_mono P hQ
    _ = 1 := mean_const P 1

noncomputable def sourceQueryError {D N : ℕ} {ι : Type*} [Fintype ι]
    (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (x : SignCube D N) : ℝ :=
  (∑ j, interaction (Ω j) (β j) (v j) (t j) x) -
    ∑ j, diagonalTerm (Ω j) (β j) (v j) (t j) x

/-- AL's mean estimate, with only its analytic budgets left as hypotheses. -/
theorem sourceQuery_mean_bound {D N : ℕ} {ι : Type*} [Fintype ι]
    (P : PositiveLaw (SignCube D N)) (l : ι → ℕ)
    (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (hgrade : ∀ j, grade (naturalProfile (t j)) ≤ grade (naturalProfile (v j)))
    (hΩ : ∀ j, LegalCoefficient (l j) (naturalProfile (v j)) (Ω j))
    (hβ : ∀ j, LegalCoefficient (l j) (naturalProfile (t j)) (β j))
    (K A : ℝ) (hK : relativeEntropy P (fairCubeLaw D N) ≤ K)
    (hA : ∀ h : Fin D,
      mean P (axisVariance (fun u => escapedCoefficientAt Ω β v t h u)) ≤ A) :
    |mean P (sourceQueryError Ω β v t)| ≤ (D : ℝ) * Real.sqrt (2 * K * A) := by
  have hKnonneg : 0 ≤ K := (relativeEntropy_nonneg P (fairCubeLaw D N)).trans hK
  have heq : sourceQueryError Ω β v t =
      (fun x => ∑ h, axisMartingale h (fun u => escapedCoefficientAt Ω β v t h u) x) := by
    funext x
    exact sourceQuery_firstEscape Ω β v t hgrade x
  rw [heq, mean_sum]
  calc
    _ ≤ ∑ h, |mean P (axisMartingale h (fun u => escapedCoefficientAt Ω β v t h u))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h : Fin D, Real.sqrt (2 * K * A) := by
      apply Finset.sum_le_sum
      intro h hh
      have hreads := fun u => escapedCoefficientAt_readsAxisPast l Ω β v t hΩ hβ h u
      have hvarnonneg : 0 ≤ mean P (axisVariance (fun u => escapedCoefficientAt Ω β v t h u)) :=
        Finset.sum_nonneg (fun x _ => mul_nonneg (le_of_lt (P.positive x))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      calc
        _ ≤ Real.sqrt (2 * relativeEntropy P (fairCubeLaw D N) *
            mean P (axisVariance (fun u => escapedCoefficientAt Ω β v t h u))) :=
          oneAxis_gibbs P h _ hreads
        _ ≤ Real.sqrt (2 * K * A) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num))
            (hA h) hvarnonneg (mul_nonneg (by norm_num) hKnonneg)
    _ = _ := by simp

theorem sqrt_budget_tendsto_zero (D : ℕ) (K A : ℕ → ℝ)
    (hproduct : Tendsto (fun N => K N * A N) atTop (𝓝 0)) :
    Tendsto (fun N => (D : ℝ) * Real.sqrt (2 * K N * A N)) atTop (𝓝 0) := by
  have htwice := hproduct.const_mul (2 : ℝ)
  simp only [mul_zero] at htwice
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp htwice
  simp only [Real.sqrt_zero] at hsqrt
  have h := hsqrt.const_mul (D : ℝ)
  simpa only [mul_zero, mul_assoc, Function.comp_apply] using h

theorem alignment_tendsto_zero_of_budgets (D : ℕ) (K A error : ℕ → ℝ)
    (hproduct : Tendsto (fun N => K N * A N) atTop (𝓝 0))
    (hbound : ∀ N, |error N| ≤ (D : ℝ) * Real.sqrt (2 * K N * A N)) :
    Tendsto error atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun N => abs_nonneg (error N)) hbound (sqrt_budget_tendsto_zero D K A hproduct)

theorem alignment_tendsto_zero_of_eventual_budgets (D : ℕ) (K A error : ℕ → ℝ)
    (hproduct : Tendsto (fun N => K N * A N) atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, |error N| ≤ (D : ℝ) * Real.sqrt (2 * K N * A N)) :
    Tendsto error atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg (error N)))
      hbound (sqrt_budget_tendsto_zero D K A hproduct)

end HaarQuarter
