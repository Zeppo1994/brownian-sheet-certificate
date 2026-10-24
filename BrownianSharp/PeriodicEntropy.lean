import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import BrownianSharp.TheoremDEntropyPacking
import BrownianSharp.Interpolation
import BrownianSharp.EventualRates

/-!
# Periodic mixed-smoothness entropy index transfer

This module formalizes the deterministic passage from a discrete lower bound
on covering numbers to a lower bound for dyadic entropy numbers. It also
isolates the layer-to-index numerical calculation for all three exponents in
the manuscript. The scale estimates and the covering obstruction are inputs:
they are the probabilistic/atomic-synthesis part, not proved here.
-/

open Set
open scoped ENNReal NNReal

namespace BrownianSharp

variable {X : Type*} [PseudoEMetricSpace X]

/-- Neighboring actual native Haar dimensions obey a fixed ratio bound. -/
theorem nativeDimension_step_le {d n : ℕ} (hd : 1 ≤ d) :
    nativeDimension d (n + 1) ≤ (2 * (d : ℝ)) * nativeDimension d n := by
  have hcount := hyperbolicCount_succ_mul d n hd
  have hratio : nativeDimension d n * (2 * ((n + d : ℕ) : ℝ)) =
      nativeDimension d (n + 1) * ((n + 1 : ℕ) : ℝ) := by
    unfold nativeDimension
    rw [pow_succ]
    have hcount' : hyperbolicCount d n * (↑(n + d) : ℝ) =
        hyperbolicCount d (n + 1) * (↑(n + 1) : ℝ) := by
      simpa [Nat.cast_add] using hcount
    calc
      (2 : ℝ) ^ n * hyperbolicCount d n * (2 * (↑(n + d))) =
          ((2 : ℝ) ^ n * 2) * (hyperbolicCount d n * (↑(n + d))) := by ring
      _ = ((2 : ℝ) ^ (n + 1)) *
          (hyperbolicCount d (n + 1) * (↑(n + 1))) := by
        rw [hcount']
        rw [pow_succ]
      _ = (2 : ℝ) ^ (n + 1) * hyperbolicCount d (n + 1) * ↑(n + 1) := by ring
  have hfac : 2 * ((n + d : ℕ) : ℝ) ≤
      (2 * (d : ℝ)) * ((n + 1 : ℕ) : ℝ) := by
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hmul : (n : ℝ) ≤ (d : ℝ) * n := by nlinarith
    have hbase : (n : ℝ) + d ≤ (d : ℝ) * ((n : ℝ) + 1) := by nlinarith
    calc
      2 * ((n + d : ℕ) : ℝ) = 2 * ((n : ℝ) + d) := by simp [Nat.cast_add]
      _ ≤ 2 * ((d : ℝ) * ((n : ℝ) + 1)) := by nlinarith
      _ = (2 * (d : ℝ)) * ((n + 1 : ℕ) : ℝ) := by simp [Nat.cast_add]; ring
  have hDn : 0 ≤ nativeDimension d n := by
    unfold nativeDimension hyperbolicCount
    positivity
  have hmul := mul_le_mul_of_nonneg_left hfac hDn
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul' : nativeDimension d (n + 1) * (↑(n + 1)) ≤
      ((2 * (d : ℝ)) * nativeDimension d n) * (↑(n + 1)) := by
    calc
      nativeDimension d (n + 1) * (↑(n + 1)) =
          nativeDimension d n * (2 * (↑(n + d))) := hratio.symm
      _ ≤ nativeDimension d n * ((2 * (d : ℝ)) * (↑(n + 1))) := hmul
      _ = _ := by ring
  exact le_of_mul_le_mul_right hmul' hnpos

/-- The native dimension eventually exceeds every entropy index. -/
theorem nativeEntropyCrossing_exists (d k : ℕ) (hd : 0 < d) :
    ∃ q : ℕ, (k : ℝ) ≤ nativeDimension d (2 * q) := by
  refine ⟨k, ?_⟩
  have hnat : k ≤ 2 ^ (2 * k) := by
    have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
    nlinarith
  have hreal : (k : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by exact_mod_cast hnat
  exact hreal.trans (nativeDimension_ge_dyadic d (2 * k) hd)

/-- A dyadic first-crossing grade for the exact native layer dimension. -/
noncomputable def nativeEntropyCrossing (d k : ℕ) (hd : 0 < d) : ℕ :=
  Nat.find (nativeEntropyCrossing_exists d k hd)

/-- First-crossing selection supplies the exact dimension bracket; its upper
side follows from the neighboring-binomial ratio, not an asymptotic proxy. -/
theorem nativeEntropyCrossing_bracket {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    let q := nativeEntropyCrossing d k (by omega)
    0 < q ∧
      nativeDimension d (2 * (q - 1)) < (k : ℝ) ∧
      (k : ℝ) ≤ nativeDimension d (2 * q) ∧
      nativeDimension d (2 * q) ≤ (4 * (d : ℝ) ^ 2) * (k : ℝ) := by
  dsimp [nativeEntropyCrossing]
  let P : ℕ → Prop := fun q => (k : ℝ) ≤ nativeDimension d (2 * q)
  have hP : ∃ q, P q := nativeEntropyCrossing_exists d k (by omega)
  let q := Nat.find hP
  have hq : 0 < q := by
    by_contra hnq
    have hzero : q = 0 := by omega
    have hspec : P q := by simpa [q] using Nat.find_spec hP
    rw [hzero] at hspec
    have hdim0 : nativeDimension d 0 = 1 := by
      simp [nativeDimension, hyperbolicCount]
    change (k : ℝ) ≤ nativeDimension d 0 at hspec
    rw [hdim0] at hspec
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hcurr : (k : ℝ) ≤ nativeDimension d (2 * q) := by
    simpa [P, q] using Nat.find_spec hP
  have hprevnot : ¬ P (q - 1) := by
    have hmin := Nat.find_min hP (by omega : q - 1 < Nat.find hP)
    simpa [P, q] using hmin
  have hprev : nativeDimension d (2 * (q - 1)) < (k : ℝ) := by
    exact lt_of_not_ge hprevnot
  have hstep1 := nativeDimension_step_le (d := d) (n := 2 * (q - 1)) (by omega)
  have hstep2 := nativeDimension_step_le (d := d) (n := 2 * (q - 1) + 1) (by omega)
  have hgrade : 2 * (q - 1) + 1 + 1 = 2 * q := by omega
  have hupper : nativeDimension d (2 * q) ≤
      (4 * (d : ℝ) ^ 2) * nativeDimension d (2 * (q - 1)) := by
    rw [← hgrade]
    have hstep1' := hstep1
    have hstep2' := hstep2
    rw [show (2 * (q - 1) + 1) + 1 = 2 * (q - 1) + 1 + 1 by omega] at hstep2'
    calc
      nativeDimension d (2 * (q - 1) + 1 + 1) ≤
          (2 * (d : ℝ)) * nativeDimension d (2 * (q - 1) + 1) := hstep2'
      _ ≤ (2 * (d : ℝ)) * ((2 * (d : ℝ)) *
          nativeDimension d (2 * (q - 1))) :=
        mul_le_mul_of_nonneg_left hstep1' (by positivity)
      _ = (4 * (d : ℝ) ^ 2) * nativeDimension d (2 * (q - 1)) := by ring
  refine ⟨hq, hprev, hcurr, ?_⟩
  exact hupper.trans (mul_le_mul_of_nonneg_left hprev.le (by positivity))

/-- A dimension-dependent exponential upper bound, proved from the exact
neighboring-binomial ratio. -/
theorem nativeDimension_upper_exponential {d n : ℕ} (hd : 1 ≤ d) :
    nativeDimension d n ≤ (2 * (d : ℝ)) ^ n := by
  induction n with
  | zero => simp [nativeDimension, hyperbolicCount]
  | succ n ih =>
      have hstep := nativeDimension_step_le (d := d) (n := n) hd
      calc
        nativeDimension d (n + 1) ≤ (2 * (d : ℝ)) * nativeDimension d n := hstep
        _ ≤ (2 * (d : ℝ)) * (2 * (d : ℝ)) ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * (d : ℝ)) ^ n * (2 * (d : ℝ)) := by ring
        _ = (2 * (d : ℝ)) ^ (n + 1) := by rw [pow_succ]

/-- The first-crossing index is logarithmically comparable to the actual
native grade. Constants are explicit and depend only on `d`. -/
theorem nativeEntropyCrossing_log_bounds {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    let q := nativeEntropyCrossing d k (by omega)
    Real.log (k : ℝ) ≤ (2 * Real.log (2 * (d : ℝ))) * (q : ℝ) ∧
      (q : ℝ) ≤
        ((1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) /
          (2 * Real.log 2)) * Real.log (k : ℝ) := by
  let q := nativeEntropyCrossing d k (by omega)
  have hbr := nativeEntropyCrossing_bracket hd hk
  dsimp [q] at hbr ⊢
  rcases hbr with ⟨hq, hprev, hcurr, hupper⟩
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by linarith
  have hdR : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : 1 < 2 * (d : ℝ) := by nlinarith
  have hRpos : 0 < 4 * (d : ℝ) ^ 2 := by positivity
  have hpowlower : (2 : ℝ) ^ (2 * nativeEntropyCrossing d k (by omega)) ≤
      nativeDimension d (2 * nativeEntropyCrossing d k (by omega)) :=
    nativeDimension_ge_dyadic d _ (by omega)
  have hdimupper : nativeDimension d (2 * nativeEntropyCrossing d k (by omega)) ≤
      (2 * (d : ℝ)) ^ (2 * nativeEntropyCrossing d k (by omega)) :=
    nativeDimension_upper_exponential (d := d) (n := _) (by omega)
  have hcurr' : (k : ℝ) ≤ nativeDimension d
      (2 * nativeEntropyCrossing d k (by omega)) := hcurr
  have hlogup : Real.log (k : ℝ) ≤
      (2 * Real.log (2 * (d : ℝ))) *
        (nativeEntropyCrossing d k (by omega) : ℝ) := by
    calc
      Real.log (k : ℝ) ≤ Real.log (nativeDimension d
          (2 * nativeEntropyCrossing d k (by omega))) :=
        Real.log_le_log hkpos hcurr'
      _ ≤ Real.log ((2 * (d : ℝ)) ^
          (2 * nativeEntropyCrossing d k (by omega))) :=
        Real.log_le_log (lt_of_lt_of_le hkpos hcurr') hdimupper
      _ = (2 * Real.log (2 * (d : ℝ))) *
          (nativeEntropyCrossing d k (by omega) : ℝ) := by
        rw [Real.log_pow]
        push_cast
        ring
  have hloglower : 2 * (nativeEntropyCrossing d k (by omega) : ℝ) *
      Real.log 2 ≤ Real.log (4 * (d : ℝ) ^ 2) + Real.log (k : ℝ) := by
    have hlog := Real.log_le_log (by positivity :
        0 < (2 : ℝ) ^ (2 * nativeEntropyCrossing d k (by omega)))
      (hpowlower.trans (by simpa using hupper))
    rw [Real.log_pow, Real.log_mul (ne_of_gt hRpos) (ne_of_gt hkpos)] at hlog
    convert hlog using 1 <;> push_cast <;> ring
  have hlognonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRlognonneg : 0 ≤ Real.log (4 * (d : ℝ) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (d : ℝ)])
  constructor
  · exact hlogup
  · have hlogbound : Real.log (4 * (d : ℝ) ^ 2) ≤
        (Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) * Real.log (k : ℝ) := by
      have hlog2k : Real.log 2 ≤ Real.log (k : ℝ) :=
        Real.log_le_log (by norm_num) hkR
      have hcoef : 0 ≤ Real.log (4 * (d : ℝ) ^ 2) / Real.log 2 :=
        div_nonneg hRlognonneg hlog2pos.le
      calc
        Real.log (4 * (d : ℝ) ^ 2) =
            (Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) * Real.log 2 := by
              field_simp [ne_of_gt hlog2pos]
        _ ≤ (Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) *
            Real.log (k : ℝ) := mul_le_mul_of_nonneg_left hlog2k hcoef
    have h := hloglower
    have hqpos : 0 ≤ (nativeEntropyCrossing d k (by omega) : ℝ) := by positivity
    have hmul : 2 * Real.log 2 *
        (nativeEntropyCrossing d k (by omega) : ℝ) ≤
          (1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) * Real.log (k : ℝ) := by
      nlinarith [h, hlogbound]
    have hden : 0 < 2 * Real.log 2 := by positivity
    calc
      (nativeEntropyCrossing d k (by omega) : ℝ) =
          (2 * Real.log 2 * (nativeEntropyCrossing d k (by omega) : ℝ)) /
            (2 * Real.log 2) := by field_simp
      _ ≤ ((1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) *
            Real.log (k : ℝ)) / (2 * Real.log 2) :=
        div_le_div_of_nonneg_right hmul hden.le
      _ = ((1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) /
            (2 * Real.log 2)) * Real.log (k : ℝ) := by ring

/-- Constants in the two first-crossing logarithm comparisons. -/
noncomputable def nativeLogScaleLower (d : ℕ) : ℝ := 2 * Real.log (2 * (d : ℝ))

noncomputable def nativeLogScaleUpper (d : ℕ) : ℝ :=
  (1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) / (2 * Real.log 2)

theorem nativeLogScaleLower_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < nativeLogScaleLower d := by
  unfold nativeLogScaleLower
  apply mul_pos (by norm_num)
  apply Real.log_pos
  have hdR : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

theorem nativeLogScaleUpper_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < nativeLogScaleUpper d := by
  unfold nativeLogScaleUpper
  have hdR : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < 1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2 := by
    have hR : 1 ≤ 4 * (d : ℝ) ^ 2 := by nlinarith
    have hlogR : 0 ≤ Real.log (4 * (d : ℝ) ^ 2) := Real.log_nonneg hR
    positivity
  positivity

/-- For either sign of a logarithmic power, first crossing controls it by a
dimension-dependent constant times the same power of the layer index. -/
noncomputable def nativeLogPowerConstant (d : ℕ) (α : ℝ) : ℝ :=
  if 0 ≤ α then nativeLogScaleLower d ^ α else nativeLogScaleUpper d ^ (-α)

theorem nativeLogPowerConstant_pos {d : ℕ} (hd : 2 ≤ d) (α : ℝ) :
    0 < nativeLogPowerConstant d α := by
  unfold nativeLogPowerConstant nativeLogScaleLower nativeLogScaleUpper
  have hL : 0 < 2 * Real.log (2 * (d : ℝ)) := nativeLogScaleLower_pos hd
  have hU : 0 < (1 + Real.log (4 * (d : ℝ) ^ 2) / Real.log 2) /
      (2 * Real.log 2) := nativeLogScaleUpper_pos hd
  split
  · exact Real.rpow_pos_of_pos hL _
  · exact Real.rpow_pos_of_pos hU _

theorem nativeEntropyCrossing_log_power {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k)
    (α : ℝ) :
    (Real.log (k : ℝ)) ^ α ≤
      nativeLogPowerConstant d α *
        (nativeEntropyCrossing d k (by omega) : ℝ) ^ α := by
  let q := nativeEntropyCrossing d k (by omega)
  have hlogs := nativeEntropyCrossing_log_bounds hd hk
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (nativeEntropyCrossing_bracket hd hk).1
  have hLpos : 0 < nativeLogScaleLower d := nativeLogScaleLower_pos hd
  have hUpos : 0 < nativeLogScaleUpper d := nativeLogScaleUpper_pos hd
  have hkpos : 1 < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkpos
  by_cases hα : 0 ≤ α
  · calc
      (Real.log (k : ℝ)) ^ α ≤
          (nativeLogScaleLower d * (q : ℝ)) ^ α :=
            Real.rpow_le_rpow hlogpos.le (by simpa [nativeLogScaleLower, q] using hlogs.1) hα
      _ = nativeLogScaleLower d ^ α * (q : ℝ) ^ α :=
            Real.mul_rpow hLpos.le hq.le
      _ = nativeLogPowerConstant d α * (q : ℝ) ^ α := by
            simp [nativeLogPowerConstant, hα]
  · have hquad : (q : ℝ) / nativeLogScaleUpper d ≤ Real.log (k : ℝ) := by
      have hqlog := hlogs.2
      exact (div_le_iff₀ hUpos).2 (by simpa [nativeLogScaleUpper, mul_comm] using hqlog)
    calc
      (Real.log (k : ℝ)) ^ α ≤
          ((q : ℝ) / nativeLogScaleUpper d) ^ α :=
            Real.rpow_le_rpow_of_nonpos (div_pos hq hUpos) hquad
              (le_of_not_ge hα)
      _ = nativeLogScaleUpper d ^ (-α) * (q : ℝ) ^ α := by
            rw [Real.div_rpow hq.le hUpos.le, Real.rpow_neg hUpos.le]
            ring
      _ = nativeLogPowerConstant d α * (q : ℝ) ^ α := by
            simp [nativeLogPowerConstant, hα]

/-- Polynomial part of the exact native dimension, with the explicit
factorial constant needed for the periodic rate transfer. -/
theorem nativeDimension_polynomial_lower {d q : ℕ}
    (hd : 2 ≤ d) (hq : 0 < q) :
    (1 / (Nat.factorial (d - 1) : ℝ)) * (2 : ℝ) ^ (2 * q) *
        (q : ℝ) ^ ((d - 1 : ℕ) : ℝ) ≤ nativeDimension d (2 * q) := by
  let p : ℕ := d - 1
  let f : ℝ := (Nat.factorial p : ℝ)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have h2q : (q : ℝ) ≤ (2 * q : ℕ) := by exact_mod_cast (by omega : q ≤ 2 * q)
  have hpow : (q : ℝ) ^ p ≤ (2 * (q : ℝ)) ^ p := by
    have hpow' : (q : ℝ) ^ p ≤ ((2 * q : ℕ) : ℝ) ^ p :=
      pow_le_pow_left₀ hqR.le h2q p
    simpa using hpow'
  have hfpos : 0 < f := by dsimp [f, p]; positivity
  have hcount := hyperbolicCount_lower hd (show 0 < 2 * q by omega)
  have hcount' : (q : ℝ) ^ p / f ≤ hyperbolicCount d (2 * q) := by
    calc
      (q : ℝ) ^ p / f ≤ (2 * (q : ℝ)) ^ p / f :=
        div_le_div_of_nonneg_right hpow hfpos.le
      _ = ((2 * q : ℕ) : ℝ) ^ p / f := by norm_num
      _ ≤ _ := by simpa [p, f] using hcount
  have hdimension : (1 / f) * (2 : ℝ) ^ (2 * q) * (q : ℝ) ^ p ≤
      (2 : ℝ) ^ (2 * q) * hyperbolicCount d (2 * q) := by
    calc
      (1 / f) * (2 : ℝ) ^ (2 * q) * (q : ℝ) ^ p =
          (2 : ℝ) ^ (2 * q) * ((q : ℝ) ^ p / f) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount' (by positivity)
  have hf : f = (Nat.factorial (d - 1) : ℝ) := by rfl
  simpa [nativeDimension, f, hf, p, Nat.cast_ofNat] using hdimension

/-- Polynomial upper bound for the weak-composition count. -/
theorem hyperbolicCount_upper {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    hyperbolicCount d n ≤ (((d + 1 : ℕ) : ℝ) * (n : ℝ)) ^
      ((d - 1 : ℕ) : ℕ) := by
  let p : ℕ := d - 1
  have hchoose := Nat.choose_le_pow_div p (n + d - 1) (α := ℝ)
  have hfact : 1 ≤ (Nat.factorial p : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos p)
  have hpow : 0 ≤ ((n + d - 1 : ℕ) : ℝ) ^ p := by positivity
  have hdiv : ((n + d - 1 : ℕ) : ℝ) ^ p /
      (Nat.factorial p : ℝ) ≤ ((n + d - 1 : ℕ) : ℝ) ^ p :=
    div_le_self hpow hfact
  have htopNat : n + d - 1 ≤ (d + 1) * n := by
    have hnNat : 1 ≤ n := by omega
    have hdn : d ≤ d * n := Nat.le_mul_of_pos_right d (by omega)
    calc
      n + d - 1 ≤ n + d := Nat.sub_le _ _
      _ ≤ n + d * n := Nat.add_le_add_left hdn n
      _ = (d + 1) * n := by rw [Nat.add_mul]; omega
  have htop : ((n + d - 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) * n := by
    exact_mod_cast htopNat
  calc
    hyperbolicCount d n = (Nat.choose (n + d - 1) (d - 1) : ℕ) := rfl
    _ ≤ ((n + d - 1 : ℕ) : ℝ) ^ p / (Nat.factorial p : ℝ) := by
      simpa [p] using hchoose
    _ ≤ ((n + d - 1 : ℕ) : ℝ) ^ p := hdiv
    _ ≤ (((d + 1 : ℕ) : ℝ) * n) ^ p :=
      pow_le_pow_left₀ (by positivity) htop p

/-- The exponent and constant obtained by replacing the exact polynomial
shape count by its lower (positive power) or upper (negative power) estimate.
The sign split is necessary for Besov smoothness when `θ < 2`. -/
noncomputable def periodicLayerPowerConstant (d : ℕ) (β : ℝ) : ℝ :=
  Real.sqrt 2 * if 0 ≤ β then
    (1 / (Nat.factorial (d - 1) : ℝ)) ^ β
  else
    (2 * ((d + 1 : ℕ) : ℝ)) ^ (((d - 1 : ℕ) : ℝ) * β)

theorem periodicLayerPowerConstant_pos {d : ℕ} (hd : 2 ≤ d) (β : ℝ) :
    0 < periodicLayerPowerConstant d β := by
  unfold periodicLayerPowerConstant
  have hf : 0 < (Nat.factorial (d - 1) : ℝ) := by positivity
  split
  · positivity
  · positivity

/-- Actual grade-`2q` manuscript radius dominates its explicit mixed-smoothness
power scale. This uses the true binomial coefficient shape count and treats
negative powers by the polynomial upper bound. -/
theorem periodicLayerRadius_lower {d q : ℕ} {r β : ℝ}
    (hd : 2 ≤ d) (hq : 0 < q) :
    periodicLayerPowerConstant d β * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
      (q : ℝ) ^ (1 / 2 + β * ((d - 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
        Real.sqrt (2 * (q : ℝ)) * (hyperbolicCount d (2 * q)) ^ β := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hn : 0 < 2 * q := by omega
  have hS : 0 < hyperbolicCount d (2 * q) := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ 2 * q + d - 1)
  have hsqrt : Real.sqrt (2 * (q : ℝ)) = Real.sqrt 2 * (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hshapeLower :
      (1 / (Nat.factorial (d - 1) : ℝ)) * (q : ℝ) ^ (d - 1) ≤
        hyperbolicCount d (2 * q) := by
    have h := hyperbolicCount_lower hd hn
    have hqle : (q : ℝ) ≤ (2 * q : ℕ) := by exact_mod_cast (by omega : q ≤ 2 * q)
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (q : ℝ)) hqle (d - 1)
    have hf : 0 < (Nat.factorial (d - 1) : ℝ) := by positivity
    calc
      (1 / (Nat.factorial (d - 1) : ℝ)) * (q : ℝ) ^ (d - 1) ≤
          ((2 * q : ℕ) : ℝ) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) := by
        calc
          (1 / (Nat.factorial (d - 1) : ℝ)) * (q : ℝ) ^ (d - 1) =
              (q : ℝ) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hp hf.le
      _ ≤ hyperbolicCount d (2 * q) := by simpa using h
  have hshapeUpper : hyperbolicCount d (2 * q) ≤
      (2 * ((d + 1 : ℕ) : ℝ) * (q : ℝ)) ^ ((d - 1 : ℕ) : ℕ) := by
    have h := hyperbolicCount_upper hd hn
    simpa [Nat.cast_mul, Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using h
  have hpower :
      (if 0 ≤ β then
        (1 / (Nat.factorial (d - 1) : ℝ)) ^ β * (q : ℝ) ^
          (((d - 1 : ℕ) : ℝ) * β)
       else
        (2 * ((d + 1 : ℕ) : ℝ)) ^ (((d - 1 : ℕ) : ℝ) * β) *
          (q : ℝ) ^ (((d - 1 : ℕ) : ℝ) * β)) ≤
      (hyperbolicCount d (2 * q)) ^ β := by
    by_cases hβ : 0 ≤ β
    · have hl := Real.rpow_le_rpow (by positivity) hshapeLower hβ
      have hm : (1 / (Nat.factorial (d - 1) : ℝ) *
          (q : ℝ) ^ (d - 1)) ^ β ≤
          (hyperbolicCount d (2 * q)) ^ β := hl
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul hqR.le (d - 1) β] at hm
      simpa [hβ, mul_comm] using hm
    · have hu := Real.rpow_le_rpow_of_nonpos hS hshapeUpper (le_of_not_ge hβ)
      have hu' :
          ((2 * ((d + 1 : ℕ) : ℝ) * (q : ℝ)) ^ ((d - 1 : ℕ) : ℕ)) ^ β ≤
          (hyperbolicCount d (2 * q)) ^ β := hu
      rw [← Real.rpow_natCast_mul (by positivity) (d - 1) β,
        Real.mul_rpow (by positivity) (by positivity)] at hu'
      simpa [hβ, mul_comm] using hu'
  have hprod : periodicLayerPowerConstant d β * (q : ℝ) ^
      (1 / 2 + β * ((d - 1 : ℕ) : ℝ)) ≤
        Real.sqrt (2 * (q : ℝ)) * (hyperbolicCount d (2 * q)) ^ β := by
    rw [hsqrt]
    have hfactor := mul_le_mul_of_nonneg_left hpower
      (mul_nonneg (Real.sqrt_nonneg 2)
        (Real.rpow_nonneg hqR.le (1 / 2 : ℝ)))
    calc
      periodicLayerPowerConstant d β * (q : ℝ) ^
          (1 / 2 + β * ((d - 1 : ℕ) : ℝ)) =
          Real.sqrt 2 * (q : ℝ) ^ (1 / 2 : ℝ) *
            (if 0 ≤ β then
              (1 / (Nat.factorial (d - 1) : ℝ)) ^ β * (q : ℝ) ^
                (((d - 1 : ℕ) : ℝ) * β)
             else
              (2 * ((d + 1 : ℕ) : ℝ)) ^ (((d - 1 : ℕ) : ℝ) * β) *
                (q : ℝ) ^ (((d - 1 : ℕ) : ℝ) * β)) := by
          unfold periodicLayerPowerConstant
          split_ifs with hβ
          · rw [Real.rpow_add hqR]
            ring
          · rw [Real.rpow_add hqR]
            ring
      _ ≤ Real.sqrt 2 * (q : ℝ) ^ (1 / 2 : ℝ) *
          (hyperbolicCount d (2 * q)) ^ β := hfactor
      _ = _ := by ring
  have hpow : 0 ≤ (2 : ℝ) ^ (-2 * r * (q : ℝ)) := by positivity
  calc
    periodicLayerPowerConstant d β * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
        (q : ℝ) ^ (1 / 2 + β * ((d - 1 : ℕ) : ℝ)) =
        (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
          (periodicLayerPowerConstant d β * (q : ℝ) ^
            (1 / 2 + β * ((d - 1 : ℕ) : ℝ))) := by ring
    _ ≤ (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
          (Real.sqrt (2 * (q : ℝ)) * (hyperbolicCount d (2 * q)) ^ β) :=
      mul_le_mul_of_nonneg_left hprod hpow
    _ = _ := by ring

/-- The actual manuscript radius at native grade `2q`. -/
noncomputable def periodicNativeRadius (d q : ℕ) (r β : ℝ) : ℝ :=
  (2 : ℝ) ^ (-2 * r * (q : ℝ)) * Real.sqrt (2 * (q : ℝ)) *
    (hyperbolicCount d (2 * q)) ^ β

theorem periodicNativeRadius_pos {d q : ℕ} {r β : ℝ}
    (hq : 0 < q) : 0 < periodicNativeRadius d q r β := by
  unfold periodicNativeRadius
  have hS : 0 < hyperbolicCount d (2 * q) := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ 2 * q + d - 1)
  positivity

/-- A concrete coefficient that makes the dimension-crossing transfer yield
the manuscript's exponent. Its value depends only on dimension and the
displayed smoothness exponents. -/
noncomputable def periodicNativeRateConstant (d : ℕ) (r β : ℝ) : ℝ :=
  periodicLayerPowerConstant d β /
    (((1 / (Nat.factorial (d - 1) : ℝ)) / (4 * (d : ℝ) ^ 2)) ^ (-r) *
      nativeLogPowerConstant d
        (r * ((d - 1 : ℕ) : ℝ) + (1 / 2 + β * ((d - 1 : ℕ) : ℝ))))

theorem periodicNativeRateConstant_pos {d : ℕ} (hd : 2 ≤ d) (r β : ℝ) :
    0 < periodicNativeRateConstant d r β := by
  unfold periodicNativeRateConstant
  apply div_pos (periodicLayerPowerConstant_pos hd β)
  apply mul_pos
  · apply Real.rpow_pos_of_pos
    apply div_pos
    · positivity
    · positivity
  · apply nativeLogPowerConstant_pos hd

/-- If the cover obstruction already exceeds the dyadic budget at radius
`δ`, every admissible entropy radius is at least `δ`. -/
theorem periodicEntropyNumber_ge_of_covering_gt
    (k : ℕ) (K : Set X) (δ : ℝ≥0)
    (hcover : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber δ K) :
    (δ : ℝ≥0∞) ≤ HaarQuarter.TheoremD.entropyNumber k K := by
  apply le_sInf
  rintro r ⟨ρ, rfl, hbudget⟩
  by_contra hnot
  have hnot' : ¬ δ ≤ ρ := by exact_mod_cast hnot
  have hρδ : ρ < δ := lt_of_not_ge hnot'
  have hmono := Metric.externalCoveringNumber_anti (X := X) (A := K)
    (le_of_lt hρδ)
  exact (not_le_of_gt hcover) (hmono.trans hbudget)

/-- Numeric transfer for a discrete separated scale. Here `D` is its layer
dimension, `q` its scale index, `δ` the separation radius, and `a` is the
extra logarithmic exponent. The logarithmic comparison is explicit so this
lemma also handles negative Besov exponents. -/
theorem periodic_layer_rate_transfer
    {d q k : ℕ} {r a A R cD C c₀ D δ : ℝ}
    (hq : 0 < (q : ℝ)) (hk : 1 ≤ (k : ℝ))
    (hr : 0 < r) (hA : 0 < A) (hR : 0 < R)
    (hcD : 0 < cD) (_hC : 0 < C) (_hc₀ : 0 < c₀)
    (hDlower : cD * (2 : ℝ) ^ (2 * (q : ℝ)) *
      (q : ℝ) ^ ((d - 1 : ℕ) : ℝ) ≤ D)
    (hDupper : D ≤ R * (k : ℝ))
    (hlogPower : (Real.log (k : ℝ)) ^
      (r * ((d - 1 : ℕ) : ℝ) + a) ≤
        C * (q : ℝ) ^ (r * ((d - 1 : ℕ) : ℝ) + a))
    (hconst : A * (cD / R) ^ (-r) * C ≤ c₀)
    (hscale : c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
      (q : ℝ) ^ a ≤ δ) :
    A * (k : ℝ) ^ (-r) *
      (Real.log (k : ℝ)) ^ (r * ((d - 1 : ℕ) : ℝ) + a) ≤ δ := by
  let p : ℝ := ((d - 1 : ℕ) : ℝ)
  let α : ℝ := r * p + a
  let Y : ℝ := (cD / R) * (2 : ℝ) ^ (2 * (q : ℝ)) * (q : ℝ) ^ p
  have hqpos : 0 < (q : ℝ) := hq
  have hkpos : 0 < (k : ℝ) := by positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYk : Y ≤ (k : ℝ) := by
    have hYR : Y * R ≤ D := by
      calc
        Y * R = cD * (2 : ℝ) ^ (2 * (q : ℝ)) * (q : ℝ) ^ p := by
          dsimp [Y]
          field_simp [ne_of_gt hR]
        _ ≤ D := by simpa [p] using hDlower
    have hmul : Y * R ≤ (k : ℝ) * R := by
      calc
        Y * R ≤ D := hYR
        _ ≤ R * (k : ℝ) := hDupper
        _ = (k : ℝ) * R := by ring
    nlinarith [hmul]
  have hkpow : (k : ℝ) ^ (-r) ≤ Y ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hY hYk (neg_nonpos.mpr hr.le)
  have hlogbase : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk
  have hlogpow : (Real.log (k : ℝ)) ^ α ≤
      C * (q : ℝ) ^ α := by simpa [p, α] using hlogPower
  have hidentity : Y ^ (-r) * (C * (q : ℝ) ^ α) =
      (cD / R) ^ (-r) * C * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
        (q : ℝ) ^ a := by
    dsimp [Y]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul hq.le]
    have htwo : (2 * (q : ℝ)) * (-r) = -2 * r * (q : ℝ) := by ring
    rw [htwo]
    calc
      _ = (cD / R) ^ (-r) * C * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
          ((q : ℝ) ^ (p * (-r)) * (q : ℝ) ^ α) := by ring
      _ = _ := by
        rw [← Real.rpow_add hq]
        congr 2
        dsimp [α]
        ring
  have hrate : A * (k : ℝ) ^ (-r) * (Real.log (k : ℝ)) ^ α ≤
      c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a := by
    calc
      _ ≤ A * Y ^ (-r) * (C * (q : ℝ) ^ α) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hkpow hA.le)
          hlogpow (Real.rpow_nonneg hlogbase α)
          (mul_nonneg hA.le (by positivity))
      _ = (A * (cD / R) ^ (-r) * C) *
          ((2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a) := by
        rw [mul_assoc, hidentity]
        ring
      _ ≤ c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a := by
        have hfactor : 0 ≤ (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
            (q : ℝ) ^ a := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hconst hfactor]
  have hrate' : A * (k : ℝ) ^ (-r) *
      (Real.log (k : ℝ)) ^ (r * ((d - 1 : ℕ) : ℝ) + a) ≤
        c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a := by
    simpa [p, α] using hrate
  exact hrate'.trans hscale

/-- Combine the layer-to-index calculation with the exact external-cover
entropy definition. The cover obstruction must be proved by the analytic
argument; this theorem only turns it into the manuscript's entropy rate. -/
theorem periodic_entropy_rate_from_layer
    (k : ℕ) (K : Set X) (δ : ℝ≥0)
    {d q : ℕ} {r a A R cD C c₀ D : ℝ}
    (hq : 0 < (q : ℝ)) (hk : 1 ≤ (k : ℝ))
    (hr : 0 < r) (hA : 0 < A) (hR : 0 < R)
    (hcD : 0 < cD) (_hC : 0 < C) (_hc₀ : 0 < c₀)
    (hDlower : cD * (2 : ℝ) ^ (2 * (q : ℝ)) *
      (q : ℝ) ^ ((d - 1 : ℕ) : ℝ) ≤ D)
    (hDupper : D ≤ R * (k : ℝ))
    (hlogPower : (Real.log (k : ℝ)) ^
      (r * ((d - 1 : ℕ) : ℝ) + a) ≤
        C * (q : ℝ) ^ (r * ((d - 1 : ℕ) : ℝ) + a))
    (hconst : A * (cD / R) ^ (-r) * C ≤ c₀)
    (hscale : c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
      (q : ℝ) ^ a ≤ (δ : ℝ))
    (hcover : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber δ K) :
    ENNReal.ofReal (A * (k : ℝ) ^ (-r) *
      (Real.log (k : ℝ)) ^ (r * ((d - 1 : ℕ) : ℝ) + a)) ≤
    HaarQuarter.TheoremD.entropyNumber k K := by
  have hrate := periodic_layer_rate_transfer hq hk hr hA hR hcD _hC _hc₀
    hDlower hDupper hlogPower hconst hscale
  have hrate' := ENNReal.ofReal_le_ofReal hrate
  have hentropy := periodicEntropyNumber_ge_of_covering_gt k K δ hcover
  exact hrate'.trans (by simpa using hentropy)

/-- Actual first-crossing transfer from the periodic layer covering
obstruction to the exact v10 entropy number. Apart from the analytic covering
obstruction at the selected radius, the theorem internally chooses the scale,
uses the binomial dimension, and proves all scale/log comparisons. -/
theorem periodicNative_entropy_rate
    {d k : ℕ} (K : Set X) (r β : ℝ)
    (hd : 2 ≤ d) (hk : 2 ≤ k) (hr : 0 < r)
    (hcover : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber
        ⟨periodicNativeRadius d (nativeEntropyCrossing d k (by omega)) r β,
          le_of_lt (periodicNativeRadius_pos (by
            exact (nativeEntropyCrossing_bracket hd hk).1))⟩ K) :
    ENNReal.ofReal (periodicNativeRateConstant d r β * (k : ℝ) ^ (-r) *
      (Real.log (k : ℝ)) ^
        (r * ((d - 1 : ℕ) : ℝ) + (1 / 2 + β * ((d - 1 : ℕ) : ℝ)))) ≤
      HaarQuarter.TheoremD.entropyNumber k K := by
  let q := nativeEntropyCrossing d k (by omega)
  let p : ℝ := ((d - 1 : ℕ) : ℝ)
  let a : ℝ := 1 / 2 + β * p
  let α : ℝ := r * p + a
  let cD : ℝ := 1 / (Nat.factorial (d - 1) : ℝ)
  let R : ℝ := 4 * (d : ℝ) ^ 2
  let C : ℝ := nativeLogPowerConstant d α
  let c₀ : ℝ := periodicLayerPowerConstant d β
  let A : ℝ := periodicNativeRateConstant d r β
  let δ : ℝ≥0 := ⟨periodicNativeRadius d q r β,
    le_of_lt (periodicNativeRadius_pos (by
      exact (nativeEntropyCrossing_bracket hd hk).1))⟩
  have hbr := nativeEntropyCrossing_bracket hd hk
  have hq : 0 < (q : ℝ) := by exact_mod_cast hbr.1
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hR : 0 < R := by dsimp [R]; positivity
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hC : 0 < C := by dsimp [C, α, a, p]; exact nativeLogPowerConstant_pos hd _
  have hc₀ : 0 < c₀ := by dsimp [c₀]; exact periodicLayerPowerConstant_pos hd β
  have hA : 0 < A := by dsimp [A]; exact periodicNativeRateConstant_pos hd r β
  have hDlower : cD * (2 : ℝ) ^ (2 * (q : ℝ)) *
      (q : ℝ) ^ ((d - 1 : ℕ) : ℝ) ≤ nativeDimension d (2 * q) := by
    have h := nativeDimension_polynomial_lower hd hbr.1
    have hexp : 2 * (q : ℝ) = ((2 * q : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    simpa [cD, q] using h
  have hDupper : nativeDimension d (2 * q) ≤ R * (k : ℝ) := by
    simpa [R, q, mul_comm] using hbr.2.2.2
  have hlogPower : (Real.log (k : ℝ)) ^ α ≤ C * (q : ℝ) ^ α := by
    simpa [C, α, a, p, q] using nativeEntropyCrossing_log_power hd hk α
  have hconst : A * (cD / R) ^ (-r) * C ≤ c₀ := by
    let T : ℝ := (cD / R) ^ (-r) * C
    have hden : 0 < T := by dsimp [T]; positivity
    have hAeq : A = c₀ / T := by
      dsimp [A, T, c₀, periodicNativeRateConstant, C, α, a, p, cD, R]
    calc
      A * (cD / R) ^ (-r) * C = (c₀ / T) * T := by
        rw [hAeq]
        dsimp [T]
        ring
      _ = c₀ := div_mul_cancel₀ _ hden.ne'
      _ ≤ c₀ := le_rfl
  have hscale : c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) *
      (q : ℝ) ^ a ≤ (δ : ℝ) := by
    have h := periodicLayerRadius_lower (r := r) (β := β) hd
      (by exact_mod_cast hbr.1 : 0 < q)
    change c₀ * (2 : ℝ) ^ (-2 * r * (q : ℝ)) * (q : ℝ) ^ a ≤
      periodicNativeRadius d q r β
    simpa [c₀, q, a, p, periodicNativeRadius] using h
  have hcover' : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber δ K := by
    simpa [δ, q] using hcover
  have hrate := periodic_layer_rate_transfer (d := d) (q := q) (k := k)
    (r := r) (a := a) (A := A) (R := R) (cD := cD) (C := C) (c₀ := c₀)
    (D := nativeDimension d (2 * q)) hq hkR hr hA hR hcD hC hc₀
    hDlower hDupper hlogPower hconst hscale
  have hrate' := ENNReal.ofReal_le_ofReal hrate
  have hentropy := periodicEntropyNumber_ge_of_covering_gt k K δ hcover'
  simpa [A, α, a, p] using hrate'.trans (by simpa using hentropy)

end BrownianSharp
