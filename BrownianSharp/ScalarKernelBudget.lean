import BrownianSharp.ScalarSecondDifference
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.Floor.Semiring

/-! Bounds for the sampled second-difference weights of a smooth scalar profile. -/

open Set
open scoped BigOperators

namespace BrownianSharp
noncomputable section

theorem exists_iteratedDeriv_two_bound_of_compactSupport
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |iteratedDeriv 2 f y| ≤ M := by
  have hcomp : HasCompactSupport (iteratedDeriv 2 f) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hfc.deriv.deriv
  have hcont : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv' 2
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcomp
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro y
  exact (hB y).trans (le_max_left _ _)

theorem exists_radius_of_compactSupport {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < |y| → f y = 0 := by
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let R := max R₀ 0
  have hR : tsupport f ⊆ Metric.closedBall (0 : ℝ) R := by
    exact hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨R, le_max_right _ _, ?_⟩
  intro y hy
  by_contra hne
  have hmem : y ∈ tsupport f := subset_closure (by simpa [Function.mem_support] using hne)
  have hyR : ‖y‖ ≤ R := by
    have hb := hR hmem
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hb
  have habs : ‖y‖ = |y| := Real.norm_eq_abs y
  linarith

theorem exists_scalarProfile_cutoffIndex {R : ℝ} (hR : 0 ≤ R) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ J : ℕ, R * (N : ℝ) < (J : ℝ) ∧ (J : ℝ) ≤ (R + 2) * (N : ℝ) := by
  let J := Nat.ceil (R * (N : ℝ)) + 1
  have hRN : 0 ≤ R * (N : ℝ) := mul_nonneg hR (Nat.cast_nonneg _)
  have hceilLo : R * (N : ℝ) ≤ (Nat.ceil (R * (N : ℝ)) : ℝ) := by
    exact_mod_cast Nat.le_ceil (R * (N : ℝ))
  have hceilHi : (Nat.ceil (R * (N : ℝ)) : ℝ) < R * (N : ℝ) + 1 :=
    Nat.ceil_lt_add_one hRN
  refine ⟨J, ?_, ?_⟩
  · dsimp [J]
    exact lt_of_le_of_lt hceilLo (by exact_mod_cast Nat.lt_succ_self (Nat.ceil (R * (N : ℝ))))
  · dsimp [J]
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have := add_lt_add_right hceilHi (1 : ℝ)
    norm_cast at this
    push_cast
    nlinarith

def scalarProfileSample (f : ℝ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  f ((k : ℝ) / (N : ℝ))

def scalarProfileSecondWeight (f : ℝ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) *
    (scalarProfileSample f N j - 2 * scalarProfileSample f N (j + 1) +
      scalarProfileSample f N (j + 2))

theorem sum_abs_scalarProfileSecondWeight_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (N J : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range J, |scalarProfileSecondWeight f N j|) ≤
      2 * M * (((J : ℝ) / (N : ℝ)) ^ 2) := by
  let K : ℝ := 2 * M * ((N : ℝ)⁻¹) ^ 2
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hK : 0 ≤ K := by positivity
  have hdiff (j : ℕ) :
      |scalarProfileSample f N j - 2 * scalarProfileSample f N (j + 1) +
        scalarProfileSample f N (j + 2)| ≤ 2 * M * ((N : ℝ)⁻¹) ^ 2 := by
    have hh := abs_centeredSecondDifference_le_of_iteratedDeriv_two hf hDeriv
      (((j + 1 : ℕ) : ℝ) / (N : ℝ)) ((N : ℝ)⁻¹)
    convert hh using 1 <;> simp [scalarProfileSample] <;> field_simp <;> ring
  calc
    _ ≤ ∑ j ∈ Finset.range J, K * (J : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjNat : j + 1 ≤ J := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hjReal : ((j + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjNat
      change |((j + 1 : ℕ) : ℝ) *
        (scalarProfileSample f N j - 2 * scalarProfileSample f N (j + 1) +
          scalarProfileSample f N (j + 2))| ≤ _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        ((j + 1 : ℕ) : ℝ) *
              |scalarProfileSample f N j - 2 * scalarProfileSample f N (j + 1) +
                scalarProfileSample f N (j + 2)| ≤
            ((j + 1 : ℕ) : ℝ) * K := mul_le_mul_of_nonneg_left (by simpa [K] using hdiff j)
              (Nat.cast_nonneg _)
        _ ≤ (J : ℝ) * K := mul_le_mul_of_nonneg_right hjReal hK
        _ = K * (J : ℝ) := by ring
    _ = 2 * M * (((J : ℝ) / (N : ℝ)) ^ 2) := by
      simp [K, Finset.sum_const, nsmul_eq_mul]
      field_simp

theorem sum_abs_scalarProfileSecondWeight_le_radius
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M R : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (hR : 0 ≤ R) (N J : ℕ) (hN : 0 < N)
    (hJ : (J : ℝ) ≤ (R + 3) * (N : ℝ)) :
    (∑ j ∈ Finset.range J, |scalarProfileSecondWeight f N j|) ≤
      2 * M * (R + 3) ^ 2 := by
  have hbase := sum_abs_scalarProfileSecondWeight_le hf hM hDeriv N J hN
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hratio : (J : ℝ) / (N : ℝ) ≤ R + 3 :=
    (div_le_iff₀ hNpos).2 (by nlinarith)
  have hratio0 : 0 ≤ (J : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hsquare : ((J : ℝ) / (N : ℝ)) ^ 2 ≤ (R + 3) ^ 2 := by nlinarith
  exact hbase.trans (by nlinarith [mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 2 * M)])

theorem scalarProfileSample_eq_zero_of_outside
    {f : ℝ → ℝ} {R : ℝ} (hSupport : ∀ y, R < |y| → f y = 0)
    (N : ℕ) (hN : 0 < N) {k : ℕ} (hRk : R * (N : ℝ) < (k : ℝ)) :
    scalarProfileSample f N k = 0 := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have harg : R < |(k : ℝ) / (N : ℝ)| := by
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNpos.le)]
    exact (lt_div_iff₀ hNpos).2 hRk
  simp [scalarProfileSample, hSupport _ harg]

theorem scalarProfileSample_tail_zero
    {f : ℝ → ℝ} {R : ℝ} (hSupport : ∀ y, R < |y| → f y = 0)
    (N J : ℕ) (hN : 0 < N) (hRNJ : R * (N : ℝ) < (J : ℝ)) :
    scalarProfileSample f N J = 0 ∧ scalarProfileSample f N (J + 1) = 0 := by
  constructor
  · exact scalarProfileSample_eq_zero_of_outside hSupport N hN hRNJ
  · apply scalarProfileSample_eq_zero_of_outside hSupport N hN
    exact lt_trans hRNJ (by exact_mod_cast Nat.lt_succ_self J)

end
end BrownianSharp
