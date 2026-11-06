import BrownianSharp.Carl
import BrownianSharp.CameronMartinNativeConfinement
import BrownianSharp.CameronMartin
import BrownianSharp.ExtendedStatements
import BrownianSharp.KolmogorovWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Deterministic entropy-to-width extraction for the Cameron--Martin ball

This module combines the actual Cameron--Martin entropy lower bound with the
finite-cover Carl upper bound proved in `BrownianSharp.Carl`.  Its only
additional analytic input is the stated sharp width upper estimate; it does
not assume an entropy-to-width implication.
-/

open Set HaarQuarter BrownianSharp
open scoped ENNReal NNReal
open InnerProductSpace
open scoped RealInnerProductSpace

namespace BrownianSharp.CarlRateExtraction

noncomputable section

private theorem KdUnitCube_norm_le_one (d : ℕ) :
    ∀ f ∈ CameronMartin.KdUnitCube d, ‖f‖ ≤ 1 := by
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩
  rw [ContinuousMap.norm_eq_iSup_norm]
  apply ciSup_le
  intro x
  change ‖⟪CameronMartin.unitCubeZeroExtend g,
      (brownianCubeSpanEmbedding d (CameronMartin.featureVector x))⟫‖ ≤ 1
  calc
    _ ≤ ‖CameronMartin.unitCubeZeroExtend g‖ *
        ‖brownianCubeSpanEmbedding d (CameronMartin.featureVector x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ 1 := by
      rw [CameronMartin.unitCubeZeroExtend_norm]
      have hfv := CameronMartin.featureVector_norm_le_one x
      have heq := (brownianCubeSpanEmbedding d).norm_map (CameronMartin.featureVector x)
      rw [heq]
      nlinarith [norm_nonneg g]

private theorem KdUnitCube_width_zero_le_one (d : ℕ) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (CameronMartin.KdUnitCube d) 0 ≤ ENNReal.ofReal 1 := by
  rw [HaarQuarter.TheoremD.Width.kolmogorovWidth_zero_eq_bot]
  unfold HaarQuarter.TheoremD.Width.approximationError
  apply iSup_le
  intro x
  have hxnorm : ‖(x : C(BrownianCubeAnchor d, ℝ))‖ ≤ 1 :=
    KdUnitCube_norm_le_one d x.1 x.2
  have hdist : dist (x : C(BrownianCubeAnchor d, ℝ)) 0 ≤ 1 := by
    simpa [dist_eq_norm] using hxnorm
  calc
    Metric.infEDist (x : C(BrownianCubeAnchor d, ℝ))
        ((⊥ : Submodule ℝ C(BrownianCubeAnchor d, ℝ)) : Set _) ≤
        edist (x : C(BrownianCubeAnchor d, ℝ)) 0 :=
      Metric.infEDist_le_edist_of_mem (by simp)
    _ = ENNReal.ofReal (dist (x : C(BrownianCubeAnchor d, ℝ)) 0) := edist_dist _ _
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hdist

private theorem cmIndexRate_log_mono {d : ℕ} {m N : ℕ}
    (hd : 2 ≤ d) (hm : 2 ≤ m) (hmN : m ≤ N) :
    (Real.log (m : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤
      (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
  have hmR : 1 < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hNR : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hmN)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ha : 0 ≤ (d : ℝ) - 1 / 2 := by linarith
  exact Real.rpow_le_rpow hNR hlog ha

private theorem four_pow_eq_two_pow_sq (j : ℕ) :
    (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
  calc
    (4 : ℝ) ^ j = ((2 : ℝ) ^ 2) ^ j := by norm_num
    _ = (2 : ℝ) ^ (2 * j) := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (j * 2) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul]

private theorem dyadic_rate_scale_le {d r m N j : ℕ}
    (hd : 2 ≤ d) (hr : 2 ≤ r) (hrm : r ≤ m) (hm : 2 ≤ m) (hmN : m ≤ N)
    (hindex : r + 1 = 2 ^ j) :
    (4 : ℝ) ^ j * cmIndexRate d r ≤
      4 * (m : ℝ) * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
  have hrR : 0 < (r : ℝ) := by positivity
  have hrOne : 1 ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hQnonneg : 0 ≤ (Real.log (r : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
    have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
    have hdR : 0 ≤ (d : ℝ) - 1 / 2 := by
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    exact Real.rpow_nonneg hlog _
  have hrN : r ≤ N := le_trans hrm hmN
  have hlogcmp := cmIndexRate_log_mono (m := r) (N := N) hd hr hrN
  have hpow4 : (4 : ℝ) ^ j = ((r : ℝ) + 1) ^ 2 := by
    have hpow := four_pow_eq_two_pow_sq j
    have hindexR : (r : ℝ) + 1 = (2 : ℝ) ^ j := by
      exact_mod_cast hindex
    rw [← hindexR] at hpow
    exact hpow
  have hrate : cmIndexRate d r =
      (1 / (r : ℝ)) * (Real.log (r : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
    unfold cmIndexRate logarithmicIndexRate
    rw [Real.rpow_neg hrR.le, Real.rpow_one]
    ring
  have hratio' : ((r : ℝ) + 1) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hratio : ((r : ℝ) + 1) ^ 2 / (r : ℝ) ≤ 4 * (r : ℝ) :=
    (div_le_iff₀ hrR).2 (by nlinarith [hratio'])
  rw [hpow4, hrate]
  calc
    ((r : ℝ) + 1) ^ 2 * (1 / (r : ℝ) *
        (Real.log (r : ℝ)) ^ ((d : ℝ) - 1 / 2)) ≤
      (4 * (r : ℝ)) * (Real.log (r : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
        have := mul_le_mul_of_nonneg_right hratio hQnonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    _ ≤ 4 * (m : ℝ) * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
      have hrmR : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm
      have hq := hlogcmp
      have hmnonneg : 0 ≤ (m : ℝ) := by positivity
      nlinarith [mul_nonneg hmnonneg hQnonneg]

/-- Scalar form of the finite Carl cover bound, with its NNReal radius
converted back to an extended real. -/
theorem entropy_le_of_dyadic_width_bound
    {d L : ℕ} (K : Set C(BrownianCubeAnchor d, ℝ))
    (B : ℝ) (hB : 0 < B)
    (hwidth : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) ≤
        ENNReal.ofReal (B / (4 : ℝ) ^ j.val)) :
    HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1) K ≤
      ENNReal.ofReal (4 * B / (4 : ℝ) ^ L) := by
  obtain ⟨P, hP⟩ := _root_.BrownianSharp.Carl.exists_entropy_cover_of_dyadic_width_bound
    K L B hB hwidth
  calc
    _ ≤ (NNReal.mk (4 * B / (4 : ℝ) ^ L) (by positivity) : ENNReal) := hP
    _ = ENNReal.ofReal (4 * B / (4 : ℝ) ^ L) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl

/-- A sharp width upper bound gives exactly the dyadic budget needed by Carl.
The first term handles the finitely many early widths, the second the scales
below `m`, and the last all scales above `m`. -/
theorem dyadic_width_budget_of_sharp_upper
    {d m₀ m L : ℕ} (hd : 2 ≤ d) (hm₀ : 2 ≤ m₀) (hm₀m : m₀ ≤ m)
    (hmN : m ≤ 2 ^ L) (hL : 1 ≤ L)
    (C : ℝ) (hC : 0 < C)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ≤
        ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ B : ℝ,
      B = (m₀ : ℝ) ^ 2 + 4 * C * (m : ℝ) *
        (Real.log (2 ^ L : ℝ)) ^ ((d : ℝ) - 1 / 2) +
        (2 ^ L : ℝ) ^ 2 *
          (HaarQuarter.TheoremD.Width.kolmogorovWidth
            (CameronMartin.KdUnitCube d) m).toReal ∧
      0 < B ∧
      ∀ j : Fin (L + 1),
        HaarQuarter.TheoremD.Width.kolmogorovWidth
            (CameronMartin.KdUnitCube d) (2 ^ j.val - 1) ≤
          ENNReal.ofReal (B / (4 : ℝ) ^ j.val) := by
  let K := CameronMartin.KdUnitCube d
  let N : ℝ := (2 ^ L : ℕ)
  let Q : ℝ := (Real.log N) ^ ((d : ℝ) - 1 / 2)
  have hm2 : 2 ≤ m := le_trans hm₀ hm₀m
  have hmN' : m ≤ 2 ^ L := hmN
  have hN2 : 2 ≤ 2 ^ L := le_trans hm2 hmN
  have hNreal : 0 < N := by dsimp [N]; positivity
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by dsimp [N]; exact_mod_cast (by omega : 1 ≤ 2 ^ L))
    have ha : 0 ≤ (d : ℝ) - 1 / 2 := by
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    exact Real.rpow_nonneg hlog _
  have hfinite : HaarQuarter.TheoremD.Width.kolmogorovWidth K m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper m hm₀m)
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth K m).toReal
  have hw : HaarQuarter.TheoremD.Width.kolmogorovWidth K m = ENNReal.ofReal w := by
    dsimp [w]
    exact (ENNReal.ofReal_toReal hfinite).symm
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact ENNReal.toReal_nonneg
  let B : ℝ := (m₀ : ℝ) ^ 2 + 4 * C * (m : ℝ) * Q + N ^ 2 * w
  have hbaseNonneg : 0 ≤ (m₀ : ℝ) ^ 2 + N ^ 2 * w := by positivity
  have hB : 0 < B := by
    dsimp [B]
    have hm₀R : 0 < (m₀ : ℝ) := by exact_mod_cast (by omega : 0 < m₀)
    have hw_nonneg : 0 ≤ w := by
      dsimp [w]
      exact ENNReal.toReal_nonneg
    positivity
  refine ⟨B, ?_, hB, ?_⟩
  · simp [B, Q, N, w, K]
  intro j
  let r : ℕ := 2 ^ j.val - 1
  have hrplus : r + 1 = 2 ^ j.val := by
    dsimp [r]
    have hpos : 0 < 2 ^ j.val := Nat.pow_pos (by decide)
    have hle : 1 ≤ 2 ^ j.val := by omega
    exact Nat.sub_add_cancel hle
  have hpow4 : (4 : ℝ) ^ j.val = ((r : ℝ) + 1) ^ 2 := by
    have h := four_pow_eq_two_pow_sq j.val
    have hcast : (r : ℝ) + 1 = (2 : ℝ) ^ j.val := by
      exact_mod_cast hrplus
    rw [← hcast] at h
    exact h
  by_cases hrsmall : r < m₀
  · have hr0 : r ≤ 2 ^ j.val - 1 := by rfl
    have hwidth0 : HaarQuarter.TheoremD.Width.kolmogorovWidth K r ≤
        HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 := by
      exact HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone K (Nat.zero_le r)
    have hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth K r ≤ ENNReal.ofReal 1 :=
      le_trans hwidth0 (KdUnitCube_width_zero_le_one d)
    have hrplusBound : (r + 1 : ℝ) ≤ (m₀ : ℝ) := by
      have hrm : r + 1 ≤ m₀ := by omega
      exact_mod_cast hrm
    have hbudget : 1 ≤ B / (4 : ℝ) ^ j.val := by
      apply (le_div_iff₀ (by positivity : 0 < (4 : ℝ) ^ j.val)).2
      dsimp [B]
      rw [hpow4]
      have hm₀Sq : ((m₀ : ℝ)) ^ 2 ≥ ((r : ℝ) + 1) ^ 2 := by nlinarith
      have hrest : 0 ≤ 4 * C * (m : ℝ) * Q + N ^ 2 * w := by positivity
      nlinarith
    exact le_trans hwidth (ENNReal.ofReal_le_ofReal hbudget)
  · have hrlarge : m₀ ≤ r := by omega
    by_cases hrle : r ≤ m
    · have hup := hupper r hrlarge
      have hr2 : 2 ≤ r := le_trans hm₀ hrlarge
      have hscale := dyadic_rate_scale_le hd hr2 hrle hm2 hmN hrplus
      have hbudget : C * cmIndexRate d r ≤ B / (4 : ℝ) ^ j.val := by
        apply (le_div_iff₀ (by positivity : 0 < (4 : ℝ) ^ j.val)).2
        have hscaled : C * cmIndexRate d r * (4 : ℝ) ^ j.val ≤
            4 * C * (m : ℝ) * Q := by
          calc
            _ = C * ((4 : ℝ) ^ j.val * cmIndexRate d r) := by ring
            _ ≤ C * (4 * (m : ℝ) * Q) :=
              mul_le_mul_of_nonneg_left hscale hC.le
            _ = 4 * C * (m : ℝ) * Q := by ring
        exact le_trans hscaled (by dsimp [B]; nlinarith [hbaseNonneg])
      exact le_trans hup (ENNReal.ofReal_le_ofReal hbudget)
    · have hmle : m ≤ r := by omega
      have hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth K r ≤
          HaarQuarter.TheoremD.Width.kolmogorovWidth K m :=
        HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone K hmle
      have hjL : j.val ≤ L := by omega
      have hpow2 : (2 : ℝ) ^ j.val ≤ N := by
        dsimp [N]
        exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hjL
      have hfactor : (4 : ℝ) ^ j.val ≤ N ^ 2 := by
        rw [four_pow_eq_two_pow_sq]
        have hpowPos : 0 ≤ (2 : ℝ) ^ j.val := by positivity
        nlinarith [sq_nonneg (N - (2 : ℝ) ^ j.val)]
      have hbudget : w ≤ B / (4 : ℝ) ^ j.val := by
        apply (le_div_iff₀ (by positivity : 0 < (4 : ℝ) ^ j.val)).2
        dsimp [B]
        have hw_nonneg : 0 ≤ w := by
          dsimp [w]
          exact ENNReal.toReal_nonneg
        have hprod := mul_le_mul_of_nonneg_right hfactor hw_nonneg
        have hlowBudget : 0 ≤ (m₀ : ℝ) ^ 2 + 4 * C * (m : ℝ) * Q := by positivity
        nlinarith [hprod, hlowBudget]
      exact le_trans (le_trans hwidth (le_of_eq hw)) (ENNReal.ofReal_le_ofReal hbudget)

end

end BrownianSharp.CarlRateExtraction
