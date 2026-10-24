import BrownianSharp.NativeCameronMartinWidthRate
import BrownianSharp.NativeCameronMartinEntropyUpper
import BrownianSharp.CameronMartinWidthCertified
import BrownianSharp.EntropyCoverInversion
import BrownianSharp.Theorem2Entropy
import Mathlib.Algebra.Order.Floor.Semifield

set_option maxHeartbeats 500000

open Filter
open Topology
open scoped ENNReal NNReal

namespace BrownianSharp

private theorem cover_cmRate_nonneg {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    0 ≤ cmIndexRate d k := by
  unfold cmIndexRate logarithmicIndexRate
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have ha : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  positivity

private theorem eventually_log_ceil_powerlog_le_two
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧
      Real.log ((⌈A * x * (Real.log x) ^ α⌉₊ : ℕ) : ℝ) ≤
        2 * Real.log x := by
  have hconst : Tendsto (fun x : ℝ => Real.log (2 * A) / Real.log x)
      atTop (𝓝 0) := by
    have h : (fun _ : ℝ => Real.log (2 * A)) =o[atTop] Real.log :=
      Real.isLittleO_const_log_atTop
    have ht := h.tendsto_div_nhds_zero
    simpa [div_eq_mul_inv] using ht
  have hloglog : Tendsto (fun x : ℝ =>
      Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact h.tendsto_div_nhds_zero
  have hconstEv : ∀ᶠ x : ℝ in atTop,
      Real.log (2 * A) / Real.log x < 1 / 2 := by
    exact hconst.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hloglogEv : ∀ᶠ x : ℝ in atTop,
      α * (Real.log (Real.log x) / Real.log x) < 1 / 2 := by
    have hmul : Tendsto (fun x : ℝ => α *
        (Real.log (Real.log x) / Real.log x)) atTop (𝓝 0) := by
      simpa using hloglog.const_mul α
    exact hmul.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_gt_atTop (Real.exp 1), eventually_gt_atTop (2 : ℝ),
    eventually_gt_atTop (1 / A), hconstEv, hloglogEv]
    with x hx hx2 hxA hconstx hloglogx
  have hx2' : 2 ≤ x := hx2.le
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by positivity) hx.le
  have hLpos : 0 < Real.log x := by linarith
  have hzpow : 0 < (Real.log x) ^ α := Real.rpow_pos_of_pos hLpos α
  let z : ℝ := A * x * (Real.log x) ^ α
  have hz : 1 ≤ z := by
    have hAx : 1 < A * x := by
      have h := (div_lt_iff₀ hA).1 hxA
      nlinarith
    have hLpownontriv : 1 ≤ (Real.log x) ^ α := Real.one_le_rpow hL hα.le
    dsimp [z]
    calc
      1 ≤ A * x := hAx.le
      _ ≤ A * x * (Real.log x) ^ α := by nlinarith
  have hceil : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ z)
  have hceil2 : (⌈z⌉₊ : ℝ) ≤ 2 * z := by nlinarith
  have hlogceil : Real.log (⌈z⌉₊ : ℝ) ≤ Real.log (2 * z) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogprod : Real.log (2 * z) = Real.log (2 * A) + Real.log x +
      α * Real.log (Real.log x) := by
    dsimp [z]
    rw [show 2 * (A * x * (Real.log x) ^ α) =
        (2 * A) * (x * (Real.log x) ^ α) by ring,
      Real.log_mul (by positivity : 2 * A ≠ 0)
        (by positivity : x * (Real.log x) ^ α ≠ 0),
      Real.log_mul (by positivity : x ≠ 0) (ne_of_gt hzpow),
      Real.log_rpow hLpos]
    ring
  have hconstlog : Real.log (2 * A) ≤ (1 / 2 : ℝ) * Real.log x :=
    (div_lt_iff₀ hLpos).1 hconstx |>.le
  have hloglogterm : α * Real.log (Real.log x) ≤
      (1 / 2 : ℝ) * Real.log x := by
    have hloglogx' : (α * Real.log (Real.log x)) / Real.log x < 1 / 2 := by
      simpa [div_eq_mul_inv, mul_assoc] using hloglogx
    have hmul := (div_lt_iff₀ hLpos).1 hloglogx'
    nlinarith
  refine ⟨hx2', ?_⟩
  have hlogbound : Real.log (⌈z⌉₊ : ℝ) ≤ 2 * Real.log x := by
    rw [hlogprod] at hlogceil
    nlinarith [hlogceil, hconstlog, hloglogterm]
  simpa [z] using hlogbound

private theorem eventually_floor_powerlog_lower
    {a α : ℝ} (ha : 0 < a) (hα : 1 ≤ α) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ (⌊a * x * (Real.log x) ^ α⌋₊ : ℕ) ∧
      x ≤ (⌊a * x * (Real.log x) ^ α⌋₊ : ℕ) ∧
      (a / 2) * x * (Real.log x) ^ α ≤
        (⌊a * x * (Real.log x) ^ α⌋₊ : ℝ) := by
  filter_upwards [eventually_gt_atTop (Real.exp (max 1 (2 / a))),
    eventually_gt_atTop (2 : ℝ)] with x hx hx2
  have hxa : 0 < x := by
    have : 0 < Real.exp (max 1 (2 / a)) := Real.exp_pos _
    linarith
  have hL : max 1 (2 / a) ≤ Real.log x := by
    rw [← Real.log_exp (max 1 (2 / a))]
    exact Real.log_le_log (by positivity) hx.le
  have hLpos : 0 < Real.log x :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_left (1 : ℝ) (2 / a)) hL)
  have hLone : 1 ≤ Real.log x := le_trans (le_max_left (1 : ℝ) (2 / a)) hL
  have hLpow : Real.log x ≤ (Real.log x) ^ α :=
    Real.self_le_rpow_of_one_le hLone hα
  have hLpowA : 2 ≤ a * (Real.log x) ^ α := by
    calc
      2 = a * (2 / a) := by field_simp
      _ ≤ a * Real.log x :=
        mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) hL) ha.le
      _ ≤ a * (Real.log x) ^ α := mul_le_mul_of_nonneg_left hLpow ha.le
  let z : ℝ := a * x * (Real.log x) ^ α
  have hz : 2 ≤ z := by
    have hxnonneg : 0 ≤ x := by positivity
    have hmul := mul_le_mul_of_nonneg_right hLpowA hxnonneg
    have hmulZ : 2 * x ≤ z := by simpa [z, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hx1 : 1 ≤ x := by linarith
    nlinarith
  have hfloor : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hhalf : z / 2 ≤ (⌊z⌋₊ : ℝ) := by nlinarith
  have hxa' : x ≤ (⌊z⌋₊ : ℝ) := by
    have hcoeff : 2 * x ≤ z := by
      have hmul := mul_le_mul_of_nonneg_right hLpowA (by positivity : 0 ≤ x)
      simpa [z, mul_assoc, mul_left_comm, mul_comm] using hmul
    nlinarith
  have hcount : 2 ≤ (⌊z⌋₊ : ℕ) := by
    have : (1 : ℝ) < (⌊z⌋₊ : ℝ) := by nlinarith [hfloor, hz]
    exact_mod_cast this
  refine ⟨hcount, ?_, ?_⟩
  · exact_mod_cast hxa'
  · dsimp [z] at hhalf ⊢
    nlinarith

/-- Two-sided power-log entropy rates imply the matching logarithmic cover
profile. Indices are the floor and ceiling of constant multiples of
`x (log x)^α`, where `x` is the inverse radius. -/
theorem entropy_rates_imply_log_cover_profile
    {d k₀ : ℕ} (hd : 2 ≤ d) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d))
    (hupper : ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) ≤
        ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ a A X₀ : ℝ, 0 < a ∧ 0 < A ∧ Real.exp 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
        Metric.externalCoveringNumber (x⁻¹).toNNReal
          (CameronMartin.KdUnitCube d) ≠ ⊤ ∧
        a * x * (Real.log x) ^ ((d : ℝ) - 1 / 2) <
          Real.log ((Metric.externalCoveringNumber
            (x⁻¹).toNNReal
            (CameronMartin.KdUnitCube d)).toNat : ℝ) ∧
        Real.log ((Metric.externalCoveringNumber
          (x⁻¹).toNNReal
          (CameronMartin.KdUnitCube d)).toNat : ℝ) ≤
          A * x * (Real.log x) ^ ((d : ℝ) - 1 / 2) := by
  let α : ℝ := (d : ℝ) - 1 / 2
  let a : ℝ := c / 4
  let A : ℝ := C * 2 ^ (α + 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hα : 1 ≤ α := by
    dsimp [α]
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    (eventually_log_ceil_powerlog_le_two hA (by linarith : 0 < α))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (eventually_floor_powerlog_lower ha hα)
  let X₀ : ℝ := max (max X₁ X₂) (max (max (k₀ : ℝ) (4 / a))
    (max (Real.exp (1 / A)) (Real.exp 2)))
  have hX0large : Real.exp 1 < X₀ := by
    dsimp [X₀]
    have he : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    exact lt_of_lt_of_le he
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨(a / 4) * Real.log 2, (A + 1) * Real.log 2, X₀, ?_, ?_, hX0large, ?_⟩
  · exact mul_pos (by positivity) (Real.log_pos (by norm_num))
  · exact mul_pos (by positivity) (Real.log_pos (by norm_num))
  intro x hx
  have houter : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
  have hxX₁ : X₁ ≤ x := le_trans (le_max_left _ _) houter
  have hxX₂ : X₂ ≤ x := le_trans (le_max_right _ _) houter
  have hscales : max (max (k₀ : ℝ) (4 / a))
      (max (Real.exp (1 / A)) (Real.exp 2)) ≤ x :=
    le_trans (le_max_right _ _) hx
  have hscalel : max (k₀ : ℝ) (4 / a) ≤ x := le_trans (le_max_left _ _) hscales
  have hxk : (k₀ : ℝ) ≤ x := le_trans (le_max_left _ _) hscalel
  have hxa : 4 / a ≤ x := le_trans (le_max_right _ _) hscalel
  have hscaler : max (Real.exp (1 / A)) (Real.exp 2) ≤ x := le_trans (le_max_right _ _) hscales
  have hxAexp : Real.exp (1 / A) ≤ x := le_trans (le_max_left _ _) hscaler
  have hxexp : Real.exp 2 ≤ x := le_trans (le_max_right _ _) hscaler
  have hceilLog := hX₁ x hxX₁
  have hfloor := hX₂ x hxX₂
  have hx2 : 2 ≤ x := hceilLog.1
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLone : 1 ≤ Real.log x := by
    have hlog : 2 ≤ Real.log x := by
      rw [← Real.log_exp 2]
      exact Real.log_le_log (by positivity) hxexp
    linarith
  have hLpowpos : 0 < (Real.log x) ^ α := Real.rpow_pos_of_pos hL α
  let j : ℕ := ⌊a * x * (Real.log x) ^ α⌋₊
  let m : ℕ := ⌈A * x * (Real.log x) ^ α⌉₊
  have hjlarge : 2 ≤ j := by simpa [j] using hfloor.1
  have hjx : x ≤ (j : ℝ) := by simpa [j] using hfloor.2.1
  have hjlow : (a / 2) * x * (Real.log x) ^ α ≤ (j : ℝ) := by
    simpa [j] using hfloor.2.2
  have hmge : A * x * (Real.log x) ^ α ≤ (m : ℝ) := by
    exact_mod_cast (Nat.le_ceil (A * x * (Real.log x) ^ α))
  have hmlog : Real.log (m : ℝ) ≤ 2 * Real.log x := by
    simpa [m] using hceilLog.2
  have hmge2 : x ≤ (m : ℝ) := by
    have hLpow : Real.log x ≤ (Real.log x) ^ α := Real.self_le_rpow_of_one_le hLone hα
    have hcoeff : 1 ≤ A * (Real.log x) ^ α := by
      have hmul := mul_le_mul_of_nonneg_left hLpow hA.le
      have hlogA : 1 / A ≤ Real.log x := by
        rw [← Real.log_exp (1 / A)]
        exact Real.log_le_log (by positivity) hxAexp
      have hAlower : 1 ≤ A * Real.log x := by
        simpa [mul_comm] using (div_le_iff₀ hA).1 hlogA
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ x)
    nlinarith [hmge]
  have hj2 : 2 ≤ j := hjlarge
  have hjrate : cmIndexRate d j ≥ 1 / (a * x) := by
    have hjlog : Real.log x ≤ Real.log (j : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hjx)
    have hjpow : (Real.log x) ^ α ≤ (Real.log (j : ℝ)) ^ α :=
      Real.rpow_le_rpow hL.le hjlog (by linarith)
    have hjupper : (j : ℝ) ≤ a * x * (Real.log x) ^ α := by
      have h := Nat.floor_le (by positivity : 0 ≤ a * x * (Real.log x) ^ α)
      exact_mod_cast h
    have hinv : (a * x * (Real.log x) ^ α)⁻¹ ≤ (j : ℝ)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hjupper
    unfold cmIndexRate logarithmicIndexRate
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    calc
      (j : ℝ)⁻¹ * (Real.log (j : ℝ)) ^ α ≥
          (a * x * (Real.log x) ^ α)⁻¹ * (Real.log x) ^ α := by
        exact mul_le_mul hinv hjpow (by positivity) (by positivity)
      _ = 1 / (a * x) := by
        have hx0 : x ≠ 0 := ne_of_gt (by linarith)
        have hL0 : (Real.log x) ^ α ≠ 0 := ne_of_gt hLpowpos
        field_simp [ha.ne', hx0, hL0]
  have hmrate : cmIndexRate d m ≤ (2 ^ α / A) / x := by
    have hmlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := le_trans hx2 hmge2
      exact lt_of_lt_of_le (by norm_num) hm2)
    have hlogpow : (Real.log (m : ℝ)) ^ α ≤ (2 * Real.log x) ^ α :=
      Real.rpow_le_rpow hmlogpos.le hmlog (by linarith)
    have hmulpow : (2 * Real.log x) ^ α = 2 ^ α * (Real.log x) ^ α := by
      rw [Real.mul_rpow (by norm_num) hL.le]
    have hinv : (m : ℝ)⁻¹ ≤ (A * x * (Real.log x) ^ α)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hmge
    unfold cmIndexRate logarithmicIndexRate
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    calc
      (m : ℝ)⁻¹ * (Real.log (m : ℝ)) ^ α ≤
          (A * x * (Real.log x) ^ α)⁻¹ * (2 ^ α * (Real.log x) ^ α) := by
        calc
          _ ≤ (m : ℝ)⁻¹ * (2 * Real.log x) ^ α :=
            mul_le_mul_of_nonneg_left hlogpow (by positivity)
          _ = _ := by rw [hmulpow]
          _ ≤ _ := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (2 ^ α / A) / x := by
        have hx0 : x ≠ 0 := ne_of_gt (by linarith)
        have hL0 : (Real.log x) ^ α ≠ 0 := ne_of_gt hLpowpos
        field_simp [ha.ne', hA.ne', hx0, hL0]
  have hlowentropy : ((x⁻¹).toNNReal : ℝ≥0∞) <
      HaarQuarter.TheoremD.entropyNumber j (CameronMartin.KdUnitCube d) := by
    have hrate : 1 / x < c * cmIndexRate d j := by
      have hxpos : 0 < x := by linarith
      have : 1 / x < 4 / x := div_lt_div_of_pos_right (by norm_num) hxpos
      have hmult := mul_le_mul_of_nonneg_left hjrate (le_of_lt hc)
      have heq : c * (1 / (a * x)) = 4 / x := by
        dsimp [a]
        field_simp [hc.ne', hxpos.ne']
      rw [heq] at hmult
      exact this.trans_le hmult
    have hratepos : 0 ≤ c * cmIndexRate d j :=
      mul_nonneg hc.le (cover_cmRate_nonneg hd hj2)
    have h := hlower j hj2
    have h' : ENNReal.ofReal (1 / x) < ENNReal.ofReal (c * cmIndexRate d j) :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by positivity) hrate)).2 hrate
    have hradius : ((x⁻¹).toNNReal : ℝ≥0∞) = ENNReal.ofReal (1 / x) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ 1 / x)]
      apply congrArg (fun y : ℝ≥0 => (y : ℝ≥0∞))
      rw [← Real.toNNReal_of_nonneg (by positivity : 0 ≤ 1 / x)]
      exact congrArg Real.toNNReal (by ring : x⁻¹ = 1 / x)
    rw [hradius]
    exact h'.trans_le h
  have hupperentropy : HaarQuarter.TheoremD.entropyNumber m
        (CameronMartin.KdUnitCube d) <
      ((x⁻¹).toNNReal : ℝ≥0∞) := by
    have hrate : C * cmIndexRate d m < 1 / x := by
      have hsmall : (2 ^ α / A) * C ≤ 1 / 4 := by
        have hpow : (2 : ℝ) ^ (α + 2) = 4 * 2 ^ α := by
          calc
            (2 : ℝ) ^ (α + 2) = 2 ^ α * 2 ^ (2 : ℝ) := Real.rpow_add (by norm_num) α 2
            _ = 4 * 2 ^ α := by ring_nf
        dsimp [A]
        rw [hpow]
        have hαpow : (2 : ℝ) ^ α ≠ 0 := by positivity
        field_simp [hC.ne', hαpow]
        norm_num
      have hmul := mul_le_mul_of_nonneg_left hmrate (le_of_lt hC)
      have hxpos : 0 < x := by linarith
      have : C * ((2 ^ α / A) / x) = ((2 ^ α / A) * C) / x := by ring
      rw [this] at hmul
      have hbound : ((2 ^ α / A) * C) / x ≤ (1 / 4) / x :=
        (div_le_div_of_nonneg_right hsmall hxpos.le)
      have hquarter : (1 / 4 : ℝ) / x < 1 / x :=
        div_lt_div_of_pos_right (by norm_num) hxpos
      exact lt_of_le_of_lt (hmul.trans hbound) hquarter
    have hm2 : 2 ≤ m := by exact_mod_cast (le_trans hx2 hmge2)
    have hratepos : 0 ≤ C * cmIndexRate d m :=
      mul_nonneg hC.le (cover_cmRate_nonneg hd hm2)
    have hkm : (k₀ : ℝ) ≤ (m : ℝ) := le_trans hxk hmge2
    have h := hupper m (by exact_mod_cast hkm)
    have h' : ENNReal.ofReal (C * cmIndexRate d m) < ENNReal.ofReal (1 / x) :=
      (ENNReal.ofReal_lt_ofReal_iff (by
        have hxpos : 0 < x := by linarith
        exact div_pos (by norm_num) hxpos)).2 hrate
    have hradius : ((x⁻¹).toNNReal : ℝ≥0∞) = ENNReal.ofReal (1 / x) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ 1 / x)]
      apply congrArg (fun y : ℝ≥0 => (y : ℝ≥0∞))
      rw [← Real.toNNReal_of_nonneg (by positivity : 0 ≤ 1 / x)]
      exact congrArg Real.toNNReal (by ring : x⁻¹ = 1 / x)
    rw [hradius]
    exact lt_of_le_of_lt h h'
  have hbracket := log_toNat_cover_bounds_of_entropy_bracket
    (K := CameronMartin.KdUnitCube d) (x⁻¹).toNNReal j m
    hlowentropy hupperentropy
  have hlogxpow : 0 < (Real.log x) ^ α := hLpowpos
  have hlterm : (a / 4) * x * (Real.log x) ^ α ≤ (j - 1 : ℕ) := by
    have hfloorbig : 4 / a ≤ x := hxa
    have hterm : 4 / a ≤ x * (Real.log x) ^ α := by
      have hpowone : 1 ≤ (Real.log x) ^ α :=
        Real.one_le_rpow hLone (by linarith : 0 ≤ α)
      calc
        4 / a ≤ x := hfloorbig
        _ ≤ x * (Real.log x) ^ α := by
          nlinarith [mul_nonneg (by positivity : 0 ≤ x)
            (sub_nonneg.mpr hpowone)]
    have hsize : 1 ≤ (a / 4) * x * (Real.log x) ^ α := by
      have heq : (a / 4) * (4 / a) = 1 := by field_simp [ha.ne']
      calc
        1 = (a / 4) * (4 / a) := heq.symm
        _ ≤ (a / 4) * (x * (Real.log x) ^ α) :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
        _ = (a / 4) * x * (Real.log x) ^ α := by ring
    have hjminus : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      have hjpos : 1 ≤ j := by omega
      rw [Nat.cast_sub hjpos]
      simp
    have hjlower := hjlow
    have hjreal : (a / 4) * x * (Real.log x) ^ α + 1 ≤ (j : ℝ) := by nlinarith [hsize]
    linarith
  have hmupper : (m - 1 : ℕ) ≤ (A + 1) * x * (Real.log x) ^ α := by
    have hceil : (m : ℝ) < A * x * (Real.log x) ^ α + 1 := by
      dsimp [m]
      exact Nat.ceil_lt_add_one (by positivity)
    have hmcast : (m - 1 : ℕ) ≤ m := Nat.sub_le _ _
    have hmcastR : (m - 1 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hmcast
    have htermone : 1 ≤ x * (Real.log x) ^ α := by
      have hpowone : 1 ≤ (Real.log x) ^ α :=
        Real.one_le_rpow hLone (by linarith : 0 ≤ α)
      nlinarith
    have hbase : A * x * (Real.log x) ^ α + 1 ≤
        (A + 1) * x * (Real.log x) ^ α := by nlinarith [htermone]
    exact (le_trans hmcastR (le_of_lt hceil)).trans hbase
  refine ⟨hbracket.1, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      ((a / 4) * Real.log 2) * x * (Real.log x) ^ α =
          Real.log 2 * ((a / 4) * x * (Real.log x) ^ α) := by ring
      _ ≤ Real.log 2 * (j - 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hlterm hlog2.le
      _ < Real.log ((Metric.externalCoveringNumber
          (x⁻¹).toNNReal (CameronMartin.KdUnitCube d)).toNat : ℝ) := by
        simpa [mul_comm] using hbracket.2.1
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      Real.log ((Metric.externalCoveringNumber
          (x⁻¹).toNNReal (CameronMartin.KdUnitCube d)).toNat : ℝ) ≤
          Real.log 2 * (m - 1 : ℕ) := by simpa [mul_comm] using hbracket.2.2
      _ ≤ Real.log 2 * ((A + 1) * x * (Real.log x) ^ α) :=
        mul_le_mul_of_nonneg_left hmupper hlog2.le
      _ = ((A + 1) * Real.log 2) * x * (Real.log x) ^ α := by ring

/-- Convert the inverse-radius profile into the literal small-radius rate
`t⁻¹(log t⁻¹)^(d−1/2)`. -/
private theorem cmCover_profile_of_entropy_rates
    {d k₀ : ℕ} (hd : 2 ≤ d) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d))
    (hupper : ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) ≤
        ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ a A t₀ : ℝ, 0 < a ∧ 0 < A ∧ 0 < t₀ ∧ t₀ < Real.exp (-1) ∧
      (∀ t : ℝ, 0 < t → t ≤ t₀ →
        Metric.externalCoveringNumber t.toNNReal (CameronMartin.KdUnitCube d) ≠ ⊤ ∧
        a * cmCoveringRate d t ≤
          logCoveringNumber (CameronMartin.KdUnitCube d) t ∧
        logCoveringNumber (CameronMartin.KdUnitCube d) t ≤ A * cmCoveringRate d t) := by
  obtain ⟨a₀, A₀, X₀, ha₀, hA₀, hX₀, hprofile⟩ :=
    entropy_rates_imply_log_cover_profile hd c C hc hC hlower hupper
  let t₀ : ℝ := X₀⁻¹
  have hX₀pos : 0 < X₀ := lt_trans (Real.exp_pos 1) hX₀
  have ht₀pos : 0 < t₀ := by dsimp [t₀]; positivity
  have ht₀small : t₀ < Real.exp (-1) := by
    rw [Real.exp_neg]
    dsimp [t₀]
    simpa [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos 1) hX₀
  refine ⟨a₀, A₀, t₀, ha₀, hA₀, ht₀pos, ht₀small, ?_⟩
  intro t ht htle
  let x : ℝ := t⁻¹
  have hx : X₀ ≤ x := by
    have hrec := one_div_le_one_div_of_le ht htle
    have hrec' : X₀⁻¹⁻¹ ≤ t⁻¹ := by simpa [t₀, x] using hrec
    simpa [x] using hrec'
  have hprof := hprofile x hx
  have hrad : (x⁻¹).toNNReal = t.toNNReal := by
    apply congrArg Real.toNNReal
    dsimp [x]
    rw [inv_inv]
  have hfinite : Metric.externalCoveringNumber t.toNNReal
      (CameronMartin.KdUnitCube d) ≠ ⊤ := by
    simpa [hrad] using hprof.1
  have hloglo : a₀ * x * (Real.log x) ^ ((d : ℝ) - 1 / 2) <
      logCoveringNumber (CameronMartin.KdUnitCube d) t := by
    simpa [logCoveringNumber, hrad, x] using hprof.2.1
  have hloghi : logCoveringNumber (CameronMartin.KdUnitCube d) t ≤
      A₀ * x * (Real.log x) ^ ((d : ℝ) - 1 / 2) := by
    simpa [logCoveringNumber, hrad, x] using hprof.2.2
  have hrate : cmCoveringRate d t = x * (Real.log x) ^ ((d : ℝ) - 1 / 2) := by
    simp [cmCoveringRate, logarithmicIndexRate, x]
  have hratepos : 0 ≤ cmCoveringRate d t := by
    rw [hrate]
    have hxlarge : Real.exp 1 < x := lt_of_lt_of_le hX₀ hx
    have hlogx : 0 < Real.log x := by
      have hexp : (1 : ℝ) < Real.exp 1 := by
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
      exact Real.log_pos (lt_trans hexp hxlarge)
    positivity
  refine ⟨hfinite, ?_, ?_⟩
  · calc
      a₀ * cmCoveringRate d t = a₀ * (x * (Real.log x) ^ ((d : ℝ) - 1 / 2)) := by rw [hrate]
      _ ≤ logCoveringNumber (CameronMartin.KdUnitCube d) t := by
        exact le_of_lt (by simpa [mul_assoc] using hloglo)
  · calc
      logCoveringNumber (CameronMartin.KdUnitCube d) t ≤
          A₀ * cmCoveringRate d t := by simpa [hrate, mul_assoc] using hloghi

/-- The literal Cameron--Martin entropy/width statement follows from a sharp
upper DKLL width estimate. The actual Gaussian lower entropy rate and Carl
width lower rate are supplied by their checked certificates; this theorem
assembles them with the converse entropy-to-cover profile. -/
theorem cameronMartinEntropyWidthStatement_of_sharp_width_upper
    (hsharp : ∀ d : ℕ, 2 ≤ d → ∃ Cup : ℝ, ∃ m₀ : ℕ,
      0 < Cup ∧ 2 ≤ m₀ ∧
      ∀ k : ℕ, m₀ ≤ k →
        HaarQuarter.TheoremD.Width.kolmogorovWidth
          (CameronMartin.KdUnitCube d) k ≤ ENNReal.ofReal (Cup * cmIndexRate d k)) :
    CameronMartinEntropyWidthStatement := by
  intro d hd
  obtain ⟨Cup, m₀, hCup, hm₀, hsharpd⟩ := hsharp d hd
  obtain ⟨cE, cW, hcE, hcW, kW, hkW, hEntropyLower, hWidth⟩ :=
    cameronMartin_width_and_entropy_lower_of_sharp_upper hd Cup hCup m₀ hm₀ hsharpd
  obtain ⟨Cent, hCent, kE, hEntropyUpper⟩ :=
    cameronMartin_entropy_upper_of_sharp_width_upper hd Cup hCup m₀ hm₀ hsharpd
  have hEntropyLower' : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (cE * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) := hEntropyLower
  have hEntropyUpper' : ∀ k : ℕ, max kW kE ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) ≤
        ENNReal.ofReal (Cent * cmIndexRate d k) := by
    intro k hk
    exact hEntropyUpper k (le_trans (le_max_right _ _) hk)
  obtain ⟨aCov, ACov, t₀, haCov, hACov, ht₀, ht₀small, hCover⟩ :=
    cmCover_profile_of_entropy_rates hd cE Cent hcE hCent hEntropyLower' hEntropyUpper'
  let c : ℝ := min aCov (min cE cW)
  let C : ℝ := max ACov (max Cent Cup)
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hk₀ : 2 ≤ max (max 2 kW) kE := by omega
  refine ⟨c, C, t₀, hc, hC, ht₀, ht₀small, ?_, ?_⟩
  · intro t ht htle
    obtain ⟨hfinite, hloglo, hloghi⟩ := hCover t ht htle
    have hratepos : 0 ≤ cmCoveringRate d t := by
      unfold cmCoveringRate
      have hrec := one_div_le_one_div_of_le ht htle
      have hX : Real.exp 1 < t⁻¹ := by
        have hX0 : Real.exp 1 < t₀⁻¹ := by
          have hinv := one_div_lt_one_div_of_lt ht₀ ht₀small
          simpa [Real.exp_neg, one_div] using hinv
        exact lt_of_lt_of_le hX0 (by simpa [one_div] using hrec)
      have hlogpos : 0 < Real.log t⁻¹ := by
        have hexp : (1 : ℝ) < Real.exp 1 := by
          have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
          linarith
        exact Real.log_pos (lt_trans hexp hX)
      positivity
    refine ⟨hfinite, ?_, ?_⟩
    · have hca : c ≤ aCov := by dsimp [c]; exact min_le_left _ _
      have hmul := mul_le_mul_of_nonneg_right hca hratepos
      exact hmul.trans hloglo
    · have hAC : ACov ≤ C := by dsimp [C]; exact le_max_left _ _
      exact hloghi.trans (mul_le_mul_of_nonneg_right hAC hratepos)
  · refine ⟨max (max 2 kW) kE, hk₀, ?_⟩
    intro k hk
    have hk2 : 2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
    have hkW' : kW ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
    have hkE' : kE ≤ k := le_trans (le_max_right _ _) hk
    have hratepos : 0 ≤ cmIndexRate d k := cover_cmRate_nonneg hd hk2
    have hcE' : c ≤ cE := by
      dsimp [c]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hcW' : c ≤ cW := by
      dsimp [c]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hCent' : Cent ≤ C := by
      dsimp [C]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hCup' : Cup ≤ C := by
      dsimp [C]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hElo := hEntropyLower k hk2
    have hEhi := hEntropyUpper k hkE'
    have hW := hWidth k hkW'
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcE' hratepos) |>.trans hElo
    · exact le_trans hEhi (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCent' hratepos))
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcW' hratepos) |>.trans hW.1
    · exact le_trans hW.2 (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCup' hratepos))

/-- Unconditional Theorem 3.1 Cameron--Martin entropy, covering, and width
rates, obtained by feeding the certified sharp DKLL width estimate into the
rate-to-cover conversion above. -/
theorem cameronMartinEntropyWidth_certified : CameronMartinEntropyWidthStatement := by
  apply cameronMartinEntropyWidthStatement_of_sharp_width_upper
  intro d hd
  obtain ⟨C, hC, m₀, hm₀, hwidth⟩ := cameronMartinSharpWidthUpper_certified hd
  exact ⟨C, m₀, hC, hm₀, hwidth⟩

end BrownianSharp
