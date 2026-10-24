import BrownianSharp.PeriodicEntropy
import BrownianSharp.TheoremDEntropyPacking
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Basic

/-!
# Covering-to-entropy rate inversion for Theorem 2

This is the deterministic rate bridge used after proving covering-number
bounds. It uses the copied v10 dyadic entropy number definition verbatim and
retains ambient-center (external) covering numbers. The hypotheses record the
cover-budget inequalities at the candidate radii; analytic estimates on the
covering function are separate inputs.
-/

open Set
open Filter
open Topology
open scoped ENNReal NNReal

namespace BrownianSharp

variable {X : Type*} [PseudoEMetricSpace X]

/-- The real-valued version of the candidate entropy radius. -/
noncomputable def powerLogRadiusReal (x A γ : ℝ) : ℝ :=
  A / x * (Real.log x) ^ γ

/-- The inverse-radius logarithm is asymptotic to `log x`. This is the
calibration that turns a covering estimate in `t` into the dyadic entropy
scale; it is proved here rather than postulated. -/
theorem log_inverse_powerLogRadius_ratio_tendsto
    {A γ : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      Real.log ((powerLogRadiusReal x A γ)⁻¹) / Real.log x) atTop (𝓝 1) := by
  have hconst : (fun _ : ℝ => Real.log A) =o[atTop] Real.log :=
    Real.isLittleO_const_log_atTop
  have hconst0 := hconst.tendsto_div_nhds_zero
  have hloglog : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] Real.log := by
    exact Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hloglog0 := hloglog.tendsto_div_nhds_zero
  have hratio : Tendsto (fun x : ℝ =>
      1 - Real.log A / Real.log x -
        γ * (Real.log (Real.log x) / Real.log x)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ => Real.log A / Real.log x) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hconst0
    have h2 : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
        atTop (𝓝 0) := hloglog0
    have h2' : Tendsto (fun x : ℝ => γ *
        (Real.log (Real.log x) / Real.log x)) atTop (𝓝 0) := by
      simpa using h2.const_mul γ
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1 |>.sub h2'
  have heq : ∀ᶠ x : ℝ in atTop,
      Real.log ((powerLogRadiusReal x A γ)⁻¹) / Real.log x =
        1 - Real.log A / Real.log x -
          γ * (Real.log (Real.log x) / Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hpowpos : 0 < (Real.log x) ^ γ := Real.rpow_pos_of_pos hlogpos γ
    have hradius : 0 < powerLogRadiusReal x A γ := by
      unfold powerLogRadiusReal
      positivity
    have hlogradius : Real.log (powerLogRadiusReal x A γ) =
        Real.log A - Real.log x + γ * Real.log (Real.log x) := by
      unfold powerLogRadiusReal
      rw [Real.log_mul (div_ne_zero hA.ne' hxpos.ne') hpowpos.ne',
        Real.log_div hA.ne' hxpos.ne', Real.log_rpow hlogpos]
    rw [Real.log_inv, hlogradius]
    field_simp [ne_of_gt hlogpos]
    ring
  have heq' : (fun x : ℝ =>
      1 - Real.log A / Real.log x -
        γ * (Real.log (Real.log x) / Real.log x)) =ᶠ[atTop]
      (fun x => Real.log ((powerLogRadiusReal x A γ)⁻¹) / Real.log x) :=
    heq.mono fun _ hx => hx.symm
  exact hratio.congr' heq'

/-- Every fixed positive power-log candidate radius tends to zero. -/
theorem powerLogRadiusReal_tendsto_zero
    {A γ : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => powerLogRadiusReal x A γ) atTop (𝓝 0) := by
  have hratio := log_inverse_powerLogRadius_ratio_tendsto (A := A) (γ := γ) hA
  have hhalf : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) ≤
        Real.log ((powerLogRadiusReal x A γ)⁻¹) / Real.log x := by
    have hh := hratio.eventually (Ioo_mem_nhds
      (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
    exact hh.mono fun _ hx => hx.1.le
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hhalfLog : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.log x) atTop atTop :=
    hlog.const_mul_atTop (by norm_num)
  have hinvlog : Tendsto (fun x : ℝ =>
      Real.log ((powerLogRadiusReal x A γ)⁻¹)) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hhalfLog
    filter_upwards [hhalf, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlogx : 0 < Real.log x := Real.log_pos hx1
    exact (le_div_iff₀ hlogx).mp hx
  have hneg : Tendsto (fun x : ℝ =>
      -Real.log ((powerLogRadiusReal x A γ)⁻¹)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hinvlog
  have hexp : Tendsto (fun x : ℝ =>
      Real.exp (-Real.log ((powerLogRadiusReal x A γ)⁻¹))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have heq : ∀ᶠ x : ℝ in atTop,
      Real.exp (-Real.log ((powerLogRadiusReal x A γ)⁻¹)) =
        powerLogRadiusReal x A γ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hpowpos : 0 < (Real.log x) ^ γ := Real.rpow_pos_of_pos hlogpos γ
    have hradius : 0 < powerLogRadiusReal x A γ := by
      unfold powerLogRadiusReal
      positivity
    rw [Real.log_inv, neg_neg, Real.exp_log hradius]
  exact hexp.congr' heq

/-- The standard power-log candidate radius `A k⁻¹ (log k)^γ`, represented as
an NNReal. The condition `2 ≤ k` ensures that the logarithmic power is
well-defined and positive for every real `γ`. -/
noncomputable def powerLogEntropyRadius (k : ℕ) (A γ : ℝ) (hk : 2 ≤ k)
    (hA : 0 ≤ A) : ℝ≥0 :=
  ⟨A * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ, by
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    positivity⟩

theorem externalCover_gt_of_log_toNat_gt
    (k : ℕ) (K : Set X) (ρ : ℝ≥0)
    (hfinite : Metric.externalCoveringNumber ρ K ≠ ⊤)
    (hlog : Real.log ((2 ^ (k - 1) : ℕ) : ℝ) <
      Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ)) :
    ((2 ^ (k - 1) : ℕ) : ℕ∞) < Metric.externalCoveringNumber ρ K := by
  have hbudget : 0 < ((2 ^ (k - 1) : ℕ) : ℝ) := by positivity
  have hcountPos : 0 < ((Metric.externalCoveringNumber ρ K).toNat : ℝ) := by
    by_contra h
    have hzero : (Metric.externalCoveringNumber ρ K).toNat = 0 := by
      have hnonneg : (0 : ℝ) ≤ (Metric.externalCoveringNumber ρ K).toNat := by positivity
      have hle : (Metric.externalCoveringNumber ρ K).toNat ≤ (0 : ℝ) := le_of_not_gt h
      have heq : ((Metric.externalCoveringNumber ρ K).toNat : ℝ) = 0 := le_antisymm hle hnonneg
      exact_mod_cast heq
    have hlogbudget : 0 ≤ ((k - 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    simp [hzero] at hlog
    exact (not_lt_of_ge hlogbudget) hlog
  have hnat : 2 ^ (k - 1) < (Metric.externalCoveringNumber ρ K).toNat := by
    exact_mod_cast (Real.log_lt_log_iff hbudget hcountPos).mp hlog
  rw [← ENat.natCast_toNat hfinite]
  exact_mod_cast hnat

theorem externalCover_le_of_log_toNat_le
    (k : ℕ) (K : Set X) (ρ : ℝ≥0)
    (hfinite : Metric.externalCoveringNumber ρ K ≠ ⊤)
    (hlog : Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ) ≤
      Real.log ((2 ^ (k - 1) : ℕ) : ℝ)) :
    Metric.externalCoveringNumber ρ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  have hcount : (Metric.externalCoveringNumber ρ K).toNat ≤ 2 ^ (k - 1) := by
    by_cases hzero : (Metric.externalCoveringNumber ρ K).toNat = 0
    · simp [hzero]
    · have hcountPos : 0 < ((Metric.externalCoveringNumber ρ K).toNat : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hbudget : 0 < ((2 ^ (k - 1) : ℕ) : ℝ) := by positivity
      have hreal := (Real.log_le_log_iff hcountPos hbudget).mp hlog
      exact_mod_cast hreal
  rw [← ENat.natCast_toNat hfinite]
  exact_mod_cast hcount

/-- Two-sided entropy-rate inversion from the covering budget at the two
candidate power-log radii. In particular, for Theorem 2 take
`γ = d - 1/2`; proving the two cover-budget hypotheses is the analytic content
of the covering estimate, while this theorem handles the exact v10 entropy
number and both directions of the rate comparison. -/
theorem entropyNumber_powerLog_bounds_of_covering
    (k : ℕ) (K : Set X) (c C γ : ℝ)
    (hk : 2 ≤ k) (hc : 0 < c) (hC : 0 < C)
    (hlower : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber (powerLogEntropyRadius k c γ hk hc.le) K)
    (hupper : Metric.externalCoveringNumber (powerLogEntropyRadius k C γ hk hC.le) K ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    ENNReal.ofReal (c * (k : ℝ) ^ (-1 : ℝ) *
      (Real.log (k : ℝ)) ^ γ) ≤ HaarQuarter.TheoremD.entropyNumber k K ∧
    HaarQuarter.TheoremD.entropyNumber k K ≤
      ENNReal.ofReal (C * (k : ℝ) ^ (-1 : ℝ) *
        (Real.log (k : ℝ)) ^ γ) := by
  have hlo : 0 ≤ c * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ := by
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    positivity
  have hup : 0 ≤ C * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ := by
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    positivity
  have hloRadius : (powerLogEntropyRadius k c γ hk hc.le : ℝ) =
      c * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ := rfl
  have hupRadius : (powerLogEntropyRadius k C γ hk hC.le : ℝ) =
      C * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ := rfl
  constructor
  · have h := periodicEntropyNumber_ge_of_covering_gt k K
      (powerLogEntropyRadius k c γ hk hc.le) hlower
    have heq : ENNReal.ofReal (c * (k : ℝ) ^ (-1 : ℝ) *
        (Real.log (k : ℝ)) ^ γ) =
        (powerLogEntropyRadius k c γ hk hc.le : ℝ≥0∞) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hlo]
      rfl
    rw [heq]
    exact h
  · have heq : ENNReal.ofReal (C * (k : ℝ) ^ (-1 : ℝ) *
        (Real.log (k : ℝ)) ^ γ) =
        (powerLogEntropyRadius k C γ hk hC.le : ℝ≥0∞) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hup]
      rfl
    rw [heq]
    apply sInf_le
    exact ⟨powerLogEntropyRadius k C γ hk hC.le, rfl, hupper⟩

/-- The literal exponent in the anchored mixed-Sobolev entropy estimate. -/
theorem theorem2EntropyRate_of_covering
    {d k : ℕ} (K : Set X) (c C : ℝ)
    (_hd : 2 ≤ d) (hk : 2 ≤ k) (hc : 0 < c) (hC : 0 < C)
    (hlower : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber
        (powerLogEntropyRadius k c ((d : ℝ) - 1 / 2) hk hc.le) K)
    (hupper : Metric.externalCoveringNumber
        (powerLogEntropyRadius k C ((d : ℝ) - 1 / 2) hk hC.le) K ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    ENNReal.ofReal (c * (k : ℝ) ^ (-1 : ℝ) *
      (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2)) ≤ HaarQuarter.TheoremD.entropyNumber k K ∧
    HaarQuarter.TheoremD.entropyNumber k K ≤ ENNReal.ofReal
      (C * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2)) := by
  exact entropyNumber_powerLog_bounds_of_covering k K c C ((d : ℝ) - 1 / 2)
    hk hc hC hlower hupper

private theorem powerLogEntropyRadius_eq_real (k : ℕ) (A γ : ℝ)
    (hk : 2 ≤ k) (hA : 0 ≤ A) :
    (powerLogEntropyRadius k A γ hk hA : ℝ) =
      powerLogRadiusReal (k : ℝ) A γ := by
  change A * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ =
    A / (k : ℝ) * (Real.log (k : ℝ)) ^ γ
  rw [Real.rpow_neg_one]
  ring

private theorem cover_profile_identity {x r b γ : ℝ} (hx : 2 ≤ x)
    (hr : 0 < r) (hb : 0 < b)
    (hQ : 0 < Real.log ((powerLogRadiusReal x r γ)⁻¹)) :
    b * (powerLogRadiusReal x r γ)⁻¹ *
        (Real.log ((powerLogRadiusReal x r γ)⁻¹)) ^ γ =
      (b / r) * x * (Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x) ^ γ := by
  have hxpos : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpow : 0 < (Real.log x) ^ γ := Real.rpow_pos_of_pos hL γ
  have hrad : 0 < powerLogRadiusReal x r γ := by
    unfold powerLogRadiusReal
    positivity
  have hratio : 0 ≤ Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x :=
    div_nonneg hQ.le hL.le
  have hfactor :
      (Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x) * Real.log x =
        Real.log ((powerLogRadiusReal x r γ)⁻¹) := by
    field_simp
  calc
    b * (powerLogRadiusReal x r γ)⁻¹ *
        (Real.log ((powerLogRadiusReal x r γ)⁻¹)) ^ γ =
      b * (powerLogRadiusReal x r γ)⁻¹ *
        ((Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x) *
          Real.log x) ^ γ := by rw [hfactor]
    _ = b * (powerLogRadiusReal x r γ)⁻¹ *
        (Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x) ^ γ *
          (Real.log x) ^ γ := by
          rw [Real.mul_rpow hratio hL.le]
          ring
    _ = (b / r) * x *
        (Real.log ((powerLogRadiusReal x r γ)⁻¹) / Real.log x) ^ γ := by
      unfold powerLogRadiusReal
      field_simp [ne_of_gt hr, ne_of_gt hxpos, ne_of_gt hLpow]

/-- A genuine small-radius covering profile yields the entropy rate without
postulating cover-budget inequalities at the selected entropy radii. The
calibrations `c/k (log k)^γ` and `C/k (log k)^γ` tend to zero, while their
inverse-radius logarithms are asymptotic to `log k`; this supplies the
cover-budget slack internally. -/
theorem entropyNumber_powerLog_bounds_of_profile
    (K : Set X) {a A γ t₀ c C : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (hA : 0 < A) (ht₀ : 0 < t₀)
    (hc : 0 < c) (hC : 0 < C)
    (hcoeffL : 2 * Real.log 2 ≤ a / c * (1 / 2 : ℝ) ^ γ)
    (hcoeffU : A / C * (2 : ℝ) ^ γ ≤ Real.log 2 / 2)
    (hprofile : ∀ (t : ℝ) (ht : 0 < t) (_htsmall : t ≤ t₀),
      let N := Metric.externalCoveringNumber (⟨t, ht.le⟩ : ℝ≥0) K
      N ≠ ⊤ ∧
      a * t⁻¹ * (Real.log (t⁻¹)) ^ γ ≤ Real.log (N.toNat : ℝ) ∧
      Real.log (N.toNat : ℝ) ≤ A * t⁻¹ * (Real.log (t⁻¹)) ^ γ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ) ≤
        HaarQuarter.TheoremD.entropyNumber k K ∧
      HaarQuarter.TheoremD.entropyNumber k K ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ) := by
  have hratC := log_inverse_powerLogRadius_ratio_tendsto (A := c) (γ := γ) hc
  have hratD := log_inverse_powerLogRadius_ratio_tendsto (A := C) (γ := γ) hC
  have hzeroC := powerLogRadiusReal_tendsto_zero (A := c) (γ := γ) hc
  have hzeroD := powerLogRadiusReal_tendsto_zero (A := C) (γ := γ) hC
  let natReal : ℕ → ℝ := fun k => (k : ℝ)
  have hnat : Tendsto natReal atTop atTop := tendsto_natCast_atTop_atTop
  have hratC' := hratC.comp hnat
  have hratD' := hratD.comp hnat
  have hzeroC' := hzeroC.comp hnat
  have hzeroD' := hzeroD.comp hnat
  have heC : ∀ᶠ k : ℕ in atTop,
      (1 / 2 : ℝ) ≤
        Real.log ((powerLogRadiusReal (k : ℝ) c γ)⁻¹) / Real.log (k : ℝ) := by
    have hh := hratC'.eventually (Ioo_mem_nhds
      (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
    exact hh.mono fun k hk => hk.1.le
  have heD : ∀ᶠ k : ℕ in atTop,
      ((1 / 2 : ℝ) ≤
        Real.log ((powerLogRadiusReal (k : ℝ) C γ)⁻¹) / Real.log (k : ℝ)) ∧
      (Real.log ((powerLogRadiusReal (k : ℝ) C γ)⁻¹) / Real.log (k : ℝ) ≤ 2) := by
    have hh := hratD'.eventually (Ioo_mem_nhds
      (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
    exact hh.mono fun k hk => ⟨hk.1.le, hk.2.le⟩
  have hzC : ∀ᶠ k : ℕ in atTop, powerLogRadiusReal (k : ℝ) c γ ≤ t₀ := by
    have hh := hzeroC'.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < t₀))
    exact hh.mono fun k hk => hk.le
  have hzD : ∀ᶠ k : ℕ in atTop, powerLogRadiusReal (k : ℝ) C γ ≤ t₀ := by
    have hh := hzeroD'.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < t₀))
    exact hh.mono fun k hk => hk.le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 heC
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 heD
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hzC
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 hzD
  let k₀ := max 2 (max N₁ (max N₂ (max N₃ N₄)))
  refine ⟨k₀, ?_⟩
  intro k hk
  have hk0 : max 2 (max N₁ (max N₂ (max N₃ N₄))) ≤ k := hk
  have hk2 : 2 ≤ k := by omega
  have hk₁ : N₁ ≤ k := by omega
  have hk₂ : N₂ ≤ k := by omega
  have hk₃ : N₃ ≤ k := by omega
  have hk₄ : N₄ ≤ k := by omega
  have hratioL := hN₁ k hk₁
  have hratioU := hN₂ k hk₂
  have hradiusL := hN₃ k hk₃
  have hradiusU := hN₄ k hk₄
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  let tL := powerLogRadiusReal (k : ℝ) c γ
  let tU := powerLogRadiusReal (k : ℝ) C γ
  have htL : 0 < tL := by
    dsimp [tL, powerLogRadiusReal]
    positivity
  have htU : 0 < tU := by
    dsimp [tU, powerLogRadiusReal]
    positivity
  have hQL : 0 < Real.log (tL⁻¹) := by
    have hratio := hratioL
    have hmul := (le_div_iff₀ hlogk).mp hratio
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 / 2 : ℝ) * Real.log (k : ℝ))
      (by simpa [tL] using hmul)
  have hQU : 0 < Real.log (tU⁻¹) := by
    have hratio := hratioU.1
    have hmul := (le_div_iff₀ hlogk).mp hratio
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 / 2 : ℝ) * Real.log (k : ℝ))
      (by simpa [tU] using hmul)
  have hprofL := hprofile tL htL (hradiusL.trans_eq (by rfl))
  have hprofU := hprofile tU htU (hradiusU.trans_eq (by rfl))
  rcases hprofL with ⟨hfiniteL, hcoverL, _⟩
  rcases hprofU with ⟨hfiniteU, _, hcoverU⟩
  have hidL := cover_profile_identity (x := (k : ℝ)) (r := c) (b := a)
    hkR hc ha hQL
  have hidU := cover_profile_identity (x := (k : ℝ)) (r := C) (b := A)
    hkR hC hA hQU
  have hRpowL : (1 / 2 : ℝ) ^ γ ≤ (Real.log (tL⁻¹) / Real.log (k : ℝ)) ^ γ :=
    Real.rpow_le_rpow (by norm_num) (by simpa [tL] using hratioL) hγ.le
  have hRpowU : (Real.log (tU⁻¹) / Real.log (k : ℝ)) ^ γ ≤ (2 : ℝ) ^ γ :=
    Real.rpow_le_rpow (by positivity) (by simpa [tU] using hratioU.2) hγ.le
  have hlogNlower :
      2 * Real.log 2 * (k : ℝ) ≤
        Real.log ((Metric.externalCoveringNumber
          (⟨tL, htL.le⟩ : ℝ≥0) K).toNat : ℝ) := by
    have htmp := hcoverL
    rw [hidL] at htmp
    have hkpos : 0 ≤ (k : ℝ) := by positivity
    have hcoefpos : 0 ≤ a / c := div_nonneg ha.le hc.le
    have hfirst : 2 * Real.log 2 * (k : ℝ) ≤
        (a / c) * (1 / 2 : ℝ) ^ γ * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeffL hkpos
    have hsecond : (a / c) * (1 / 2 : ℝ) ^ γ * (k : ℝ) ≤
        (a / c) * (k : ℝ) * (1 / 2 : ℝ) ^ γ := by
      rw [div_eq_mul_inv]
      exact le_of_eq (by ring)
    have hthird : (a / c) * (k : ℝ) * (1 / 2 : ℝ) ^ γ ≤
        (a / c) * (k : ℝ) *
          (Real.log (tL⁻¹) / Real.log (k : ℝ)) ^ γ := by
      exact mul_le_mul_of_nonneg_left hRpowL (mul_nonneg hcoefpos hkpos)
    exact le_trans hfirst (le_trans hsecond (le_trans hthird htmp))
  have hlogNupper :
      Real.log ((Metric.externalCoveringNumber
          (⟨tU, htU.le⟩ : ℝ≥0) K).toNat : ℝ) ≤
        (Real.log 2 / 2) * (k : ℝ) := by
    have htmp := hcoverU
    rw [hidU] at htmp
    have hkpos : 0 ≤ (k : ℝ) := by positivity
    have hcoefpos : 0 ≤ A / C := div_nonneg hA.le hC.le
    have hfirst : (A / C) * (k : ℝ) *
        (Real.log (tU⁻¹) / Real.log (k : ℝ)) ^ γ ≤
        (A / C) * (k : ℝ) * (2 : ℝ) ^ γ := by
      exact mul_le_mul_of_nonneg_left hRpowU (mul_nonneg hcoefpos hkpos)
    have hsecond : (A / C) * (k : ℝ) * (2 : ℝ) ^ γ ≤
        (Real.log 2 / 2) * (k : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hcoeffU hkpos
      nlinarith [h]
    exact le_trans htmp (le_trans hfirst hsecond)
  have hbudget : Real.log ((2 ^ (k - 1) : ℕ) : ℝ) =
      ((k : ℝ) - 1) * Real.log 2 := by
    have hcast : ((2 ^ (k - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k - 1) := by norm_cast
    rw [hcast, Real.log_pow]
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogGt : Real.log ((2 ^ (k - 1) : ℕ) : ℝ) <
      Real.log ((Metric.externalCoveringNumber
        (⟨tL, htL.le⟩ : ℝ≥0) K).toNat : ℝ) := by
    rw [hbudget]
    nlinarith [hlogNlower, hlog2, hkR]
  have hlogLe : Real.log ((Metric.externalCoveringNumber
        (⟨tU, htU.le⟩ : ℝ≥0) K).toNat : ℝ) ≤
      Real.log ((2 ^ (k - 1) : ℕ) : ℝ) := by
    rw [hbudget]
    nlinarith [hlogNupper, hlog2, hkR]
  have hρL : (powerLogEntropyRadius k c γ hk2 hc.le : ℝ≥0) =
      (⟨tL, htL.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    simpa [tL] using powerLogEntropyRadius_eq_real k c γ hk2 hc.le
  have hρU : (powerLogEntropyRadius k C γ hk2 hC.le : ℝ≥0) =
      (⟨tU, htU.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    simpa [tU] using powerLogEntropyRadius_eq_real k C γ hk2 hC.le
  have hfiniteL' : Metric.externalCoveringNumber
      (powerLogEntropyRadius k c γ hk2 hc.le) K ≠ ⊤ := by
    simpa [hρL] using hfiniteL
  have hfiniteU' : Metric.externalCoveringNumber
      (powerLogEntropyRadius k C γ hk2 hC.le) K ≠ ⊤ := by
    simpa [hρU] using hfiniteU
  have hlower := externalCover_gt_of_log_toNat_gt k K
    (powerLogEntropyRadius k c γ hk2 hc.le) hfiniteL' (by simpa [hρL] using hlogGt)
  have hupper := externalCover_le_of_log_toNat_le k K
    (powerLogEntropyRadius k C γ hk2 hC.le) hfiniteU' (by simpa [hρU] using hlogLe)
  exact entropyNumber_powerLog_bounds_of_covering k K c C γ hk2 hc hC hlower hupper

/-- Explicit constants satisfying the dyadic-budget slack. Thus the only
substantive hypothesis needed for the rate conclusion is the stated
small-radius covering profile. -/
theorem entropyNumber_powerLog_bounds_of_profile_explicit
    (K : Set X) {a A γ t₀ : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (hA : 0 < A) (ht₀ : 0 < t₀)
    (hprofile : ∀ (t : ℝ) (ht : 0 < t) (_htsmall : t ≤ t₀),
      let N := Metric.externalCoveringNumber (⟨t, ht.le⟩ : ℝ≥0) K
      N ≠ ⊤ ∧
      a * t⁻¹ * (Real.log (t⁻¹)) ^ γ ≤ Real.log (N.toNat : ℝ) ∧
      Real.log (N.toNat : ℝ) ≤ A * t⁻¹ * (Real.log (t⁻¹)) ^ γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ) ≤
        HaarQuarter.TheoremD.entropyNumber k K ∧
      HaarQuarter.TheoremD.entropyNumber k K ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-1 : ℝ) * (Real.log (k : ℝ)) ^ γ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c := a * (1 / 2 : ℝ) ^ γ / (4 * Real.log 2)
  let C := 4 * A * (2 : ℝ) ^ γ / Real.log 2
  have hpowL : 0 < (1 / 2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
  have hpowU : 0 < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hcoeffL : 2 * Real.log 2 ≤ a / c * (1 / 2 : ℝ) ^ γ := by
    have heq : a / c * (1 / 2 : ℝ) ^ γ = 4 * Real.log 2 := by
      dsimp [c]
      field_simp [ne_of_gt ha, ne_of_gt hpowL, ne_of_gt hlog2]
    rw [heq]
    linarith
  have hcoeffU : A / C * (2 : ℝ) ^ γ ≤ Real.log 2 / 2 := by
    have heq : A / C * (2 : ℝ) ^ γ = Real.log 2 / 4 := by
      dsimp [C]
      field_simp [ne_of_gt hA, ne_of_gt hpowU, ne_of_gt hlog2]
    rw [heq]
    linarith
  obtain ⟨k₀, hk⟩ := entropyNumber_powerLog_bounds_of_profile K
    hγ ha hA ht₀ hc hC hcoeffL hcoeffU hprofile
  exact ⟨c, C, hc, hC, k₀, hk⟩

end BrownianSharp
