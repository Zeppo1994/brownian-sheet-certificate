import BrownianSharp.AlignmentPaperJointGlobalHighScalar
import BrownianSharp.AlignmentPaperJointDyadicBitBudget
import BrownianSharp.AlignmentPaperJointLowGradeCostSum
import BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Cost of the actual high-window binary allocations. -/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace BrownianSharp.AlignmentPaperJointHighGradeCostSum

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGlobalHighScalar
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointDyadicBitBudget
open BrownianSharp.AlignmentPaperJointLowGradeCostSum
open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperLpJointDvp

theorem highProfile_sampleDimension_ratio_bound {d N j : ℕ} (hd : 2 ≤ d) :
    (JointSampleDimension d (N + 1 + j) : ℝ) /
        (JointSampleDimension d N : ℝ) ≤
      (Nat.factorial (d - 1) : ℝ) * (2 : ℝ) ^ (j + 1) *
        (j + 2 : ℝ) ^ (d - 1) := by
  have hDpos : 0 < (JointSampleDimension d N : ℝ) := by
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (d := d) (n := N) (by omega)
  have hupper := jointSampleDimension_upper_envelope (d := d) (n := N + 1 + j) (by omega : 1 ≤ d)
  have hlower := jointSampleDimension_lower_envelope (d := d) (n := N) (by omega : 1 ≤ d)
  have hpoly : (N + 1 + j + 1 : ℝ) ≤ (j + 2 : ℝ) * (N + 1 : ℝ) := by
    push_cast
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hpolyPow : (N + 1 + j + 1 : ℝ) ^ (d - 1) ≤
      (j + 2 : ℝ) ^ (d - 1) * (N + 1 : ℝ) ^ (d - 1) := by
    calc
      _ ≤ ((j + 2 : ℝ) * (N + 1 : ℝ)) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) hpoly _
      _ = _ := by rw [mul_pow]
  have hnum : (JointSampleDimension d (N + 1 + j) : ℝ) ≤
      (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ (N + 1 + j) *
        (N + 1 + j + 1 : ℝ) ^ (d - 1) := by
    simpa using hupper
  rw [div_le_iff₀ hDpos]
  have hcancel :
      ((2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ (N + 1 + j) *
        ((j + 2 : ℝ) ^ (d - 1) * (N + 1 : ℝ) ^ (d - 1))) ≤
      ((Nat.factorial (d - 1) : ℝ) * (2 : ℝ) ^ (j + 1) *
        (j + 2 : ℝ) ^ (d - 1)) *
        (((2 : ℝ) ^ (3 * d + 1) / (Nat.factorial (d - 1) : ℝ)) *
          (2 : ℝ) ^ N * (N + 1 : ℝ) ^ (d - 1)) := by
    have hf : 0 < (Nat.factorial (d - 1) : ℝ) := by positivity
    have hp : 0 < (N + 1 : ℝ) ^ (d - 1) := by positivity
    have h2 : (2 : ℝ) ^ (N + 1 + j) = (2 : ℝ) ^ N * (2 : ℝ) ^ (j + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2]
    field_simp
    <;> ring_nf
    <;> norm_num
  calc
    (JointSampleDimension d (N + 1 + j) : ℝ) ≤
        (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ (N + 1 + j) *
          (N + 1 + j + 1 : ℝ) ^ (d - 1) := hnum
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hpolyPow (by positivity)
    _ ≤ (Nat.factorial (d - 1) : ℝ) * (2 : ℝ) ^ (j + 1) *
        (j + 2 : ℝ) ^ (d - 1) * (JointSampleDimension d N : ℝ) := by
      exact le_trans hcancel (mul_le_mul_of_nonneg_left hlower (by positivity))

theorem highProfile_logRatio_le {d : ℕ} {p : ℝ} (hd : 2 ≤ d)
    (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ N j : ℕ, j < highProfileWindow p N →
      logRatio (JointSampleDimension d (N + 1 + j))
        (highProfileRank d p N (j + 1)) ≤ L * (j + 1 : ℝ) := by
  let η := highProfileEta p
  let F : ℝ := Nat.factorial (d - 1)
  let L : ℝ := 1 + F + 2 * Real.log 2 + (d - 1 : ℝ) + η
  have hp0 : 0 < p := by linarith
  have heta : 0 < η := by
    dsimp [η, highProfileEta]
    positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hL : 0 < L := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [L]
    nlinarith [hF, heta, hlog2]
  refine ⟨L, hL, ?_⟩
  intro N j hj
  let R := highProfileRank d p N (j + 1)
  let D := JointSampleDimension d N
  let D' := JointSampleDimension d (N + 1 + j)
  have hwindow : j + 1 ≤ highProfileWindow p N := by omega
  have hfeas := highProfileRank_feasible hd hp1 hp2 hwindow
  have hratio := highProfile_sampleDimension_ratio_bound (d := d) (N := N) (j := j) hd
  have hDpos : 0 < (D : ℝ) := by
    dsimp [D]
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (d := d) (n := N) (by omega)
  have hpowpos : 0 < (2 : ℝ) ^ R := by positivity
  have hexppos : 0 < Real.exp (η * (j + 1 : ℝ)) := Real.exp_pos _
  have hDscaled : (JointSampleDimension d N : ℝ) ≤
      2 * Real.exp (η * (j + 1 : ℝ)) * (2 : ℝ) ^ R := by
    have hmul := mul_le_mul_of_nonneg_right hfeas.2.2
      (show 0 ≤ 2 * Real.exp (η * (j + 1 : ℝ)) by positivity)
    have heq : ((D : ℝ) / 2 * Real.exp (-η * (j + 1 : ℝ))) *
        (2 * Real.exp (η * (j + 1 : ℝ))) = (D : ℝ) := by
      rw [show -η * (j + 1 : ℝ) = -(η * (j + 1 : ℝ)) by ring,
        Real.exp_neg]
      field_simp
    calc
      (JointSampleDimension d N : ℝ) = ((JointSampleDimension d N : ℝ) / 2 * Real.exp (-η * (j + 1 : ℝ))) *
          (2 * Real.exp (η * (j + 1 : ℝ))) := heq.symm
      _ ≤ (2 : ℝ) ^ R * (2 * Real.exp (η * (j + 1 : ℝ))) := by
        simpa [η, R] using hmul
      _ = 2 * Real.exp (η * (j + 1 : ℝ)) * (2 : ℝ) ^ R := by ring
  have hDdiv : (D : ℝ) / (2 : ℝ) ^ R ≤
      2 * Real.exp (η * (j + 1 : ℝ)) :=
    (div_le_iff₀ hpowpos).2 (by simpa [D, mul_comm, mul_left_comm, mul_assoc] using hDscaled)
  have hratio' : (D' : ℝ) / (D : ℝ) ≤
      F * (2 : ℝ) ^ (j + 1) * (j + 2 : ℝ) ^ (d - 1) := by
    simpa [D, D', F] using hratio
  have hquot : (D' : ℝ) / (2 : ℝ) ^ R ≤
      (F * (2 : ℝ) ^ (j + 1) * (j + 2 : ℝ) ^ (d - 1)) *
        (2 * Real.exp (η * (j + 1 : ℝ))) := by
    calc
      (D' : ℝ) / (2 : ℝ) ^ R = ((D' : ℝ) / (D : ℝ)) *
          ((D : ℝ) / (2 : ℝ) ^ R) := by field_simp
      _ ≤ _ := mul_le_mul hratio' hDdiv (by positivity) (by positivity)
  let B : ℝ := Real.exp 1 *
    (F * (2 : ℝ) ^ (j + 1) * (j + 2 : ℝ) ^ (d - 1) *
      (2 * Real.exp (η * (j + 1 : ℝ))))
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hD'pos : 0 < (D' : ℝ) := by
    dsimp [D']
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (d := d) (n := N + 1 + j) (by omega)
  have harg : Real.exp 1 * (D' : ℝ) / (2 : ℝ) ^ R ≤ B := by
    dsimp [B]
    rw [show Real.exp 1 * (D' : ℝ) / (2 : ℝ) ^ R =
      Real.exp 1 * ((D' : ℝ) / (2 : ℝ) ^ R) by ring]
    exact mul_le_mul_of_nonneg_left hquot (Real.exp_nonneg _)
  have hlogarg := Real.log_le_log (div_pos (mul_pos (Real.exp_pos _) hD'pos) hpowpos) harg
  have hlogB : Real.log B ≤ L * (j + 1 : ℝ) := by
    have hlogj : Real.log (j + 2 : ℝ) ≤ (j + 1 : ℝ) := by
      have : 0 < (j + 2 : ℝ) := by positivity
      have hh := Real.log_le_sub_one_of_pos this
      have heq : (j + 2 : ℝ) - 1 = (j + 1 : ℝ) := by push_cast; ring
      simpa [heq] using hh
    have hlogF : Real.log F ≤ F := by
      have hh := Real.log_le_sub_one_of_pos hF
      linarith
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogcalc : Real.log B = 1 + Real.log F +
        (j + 1 : ℝ) * Real.log 2 +
        (d - 1 : ℝ) * Real.log (j + 2 : ℝ) +
        Real.log 2 + η * (j + 1 : ℝ) := by
      dsimp [B]
      rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_exp, Real.log_pow, Real.log_pow]
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      ring
    rw [hlogcalc]
    have hjpos : 0 ≤ (j + 1 : ℝ) := by positivity
    have hqnonneg : 0 ≤ (d - 1 : ℝ) := by
      change 0 ≤ (d : ℝ) - 1
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ d by omega))
    have hone : 1 ≤ (j + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    dsimp [L]
    have hFterm := mul_le_mul_of_nonneg_left hlogF (show 0 ≤ (1 : ℝ) by norm_num)
    have hqterm := mul_le_mul_of_nonneg_left hlogj hqnonneg
    have hlogterm := mul_le_mul_of_nonneg_left hlog2.le (show 0 ≤ (j + 1 : ℝ) by positivity)
    nlinarith
  have htarget : logRatio D' R ≤ L * (j + 1 : ℝ) := by
    change Real.log (Real.exp 1 * (D' : ℝ) / (2 : ℝ) ^ R) ≤ _
    exact le_trans hlogarg hlogB
  simpa [D', R, logRatio] using htarget

/-- The ceiling-coded binary allocations over the whole high window cost only
a constant multiple of the current joint sample dimension. -/
theorem highProfile_count_cost_sum_le {d : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ j : Fin (highProfileWindow p N),
        (Nat.ceil ((6 * codingConstant + 1) *
          (2 : ℝ) ^ highProfileRank d p N (j.val + 1) *
          logRatio (JointSampleDimension d (N + 1 + j.val))
            (highProfileRank d p N (j.val + 1)) : ℝ) : ℝ)) ≤
        C * (JointSampleDimension d N : ℝ) := by
  obtain ⟨L, hL, hlog⟩ := highProfile_logRatio_le hd hp1 hp2
  let η := highProfileEta p
  let Wc : ℝ := 4 * p / (p - 1) + 1
  let A : ℝ := (6 * codingConstant + 1) * 2 * L
  let C : ℝ := A * expPolynomialTsum 1 η + Wc
  have hp0 : 0 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have heta : 0 < η := by dsimp [η, highProfileEta]; positivity
  have hWc : 0 < Wc := by dsimp [Wc]; positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity [codingConstant_pos, hL]
  have hsumPos : 0 < expPolynomialTsum 1 η := by
    unfold expPolynomialTsum
    exact (summable_succ_pow_exp (k := 1) heta).tsum_pos
      (fun j => by positivity) 0 (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N
  let W := highProfileWindow p N
  let D := (JointSampleDimension d N : ℝ)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (d := d) (n := N) (by omega)
  have hwindowReal : (W : ℝ) < Wc * (N + 1 : ℝ) := by
    dsimp [W, Wc, highProfileWindow]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4 * p * (N : ℝ) / (p - 1) by positivity)
    have hcoef : 0 < 4 * p / (p - 1) := by positivity
    have heq : (4 * p / (p - 1) + 1) * ((N : ℝ) + 1) =
        4 * p * (N : ℝ) / (p - 1) + 1 + 4 * p / (p - 1) + (N : ℝ) := by ring
    rw [heq]
    linarith
  have hwindowDim : (W : ℝ) ≤ Wc * D := by
    have hgrades := grade_count_le_joint_dimension (d := d) (N := N) (by omega : 1 ≤ d)
    have hWnonneg : 0 ≤ Wc := hWc.le
    nlinarith
  have hfinite :
      (∑ j ∈ Finset.range W,
        (Nat.ceil ((6 * codingConstant + 1) *
          (2 : ℝ) ^ highProfileRank d p N (j + 1) *
          logRatio (JointSampleDimension d (N + 1 + j))
            (highProfileRank d p N (j + 1)) : ℝ) : ℝ)) ≤
        A * D * expPolynomialTsum 1 η + W := by
    calc
      _ ≤ ∑ j ∈ Finset.range W,
          ((6 * codingConstant + 1) * 2 * D * L *
            (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ)) + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjW : j < W := by simpa using hj
        have hlogj := hlog N j hjW
        have hfeas := highProfileRank_feasible hd hp1 hp2 (Nat.succ_le_of_lt hjW)
        have hpow := highProfileRank_pow_upper hd hp1 hp2 (Nat.succ_le_of_lt hjW)
        have hdim : 2 ^ highProfileRank d p N (j + 1) ≤
            JointSampleDimension d (N + 1 + j) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfeas.2.1
        have hlogone : 1 ≤ logRatio (JointSampleDimension d (N + 1 + j))
            (highProfileRank d p N (j + 1)) := logRatio_one_le hdim
        let x := (6 * codingConstant + 1) *
          (2 : ℝ) ^ highProfileRank d p N (j + 1) *
          logRatio (JointSampleDimension d (N + 1 + j))
            (highProfileRank d p N (j + 1))
        have hcoeffpos : 0 < 6 * codingConstant + 1 := by positivity [codingConstant_pos]
        have hxnonneg : 0 ≤ x := by
          dsimp [x]
          apply mul_nonneg
          · exact mul_nonneg hcoeffpos.le (by positivity)
          · exact le_trans (by norm_num) hlogone
        have hceil : (Nat.ceil x : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxnonneg).le
        have hprod : (2 : ℝ) ^ highProfileRank d p N (j + 1) *
            logRatio (JointSampleDimension d (N + 1 + j))
              (highProfileRank d p N (j + 1)) ≤
          2 * D * Real.exp (-η * (j + 1 : ℝ)) * (L * (j + 1 : ℝ)) := by
          have hpow' : (2 : ℝ) ^ highProfileRank d p N (j + 1) ≤
              2 * D * Real.exp (-η * (j + 1 : ℝ)) := by
            simpa [D, η, Nat.cast_add, add_comm, add_left_comm, add_assoc] using hpow
          have hright : 0 ≤ 2 * D * Real.exp (-η * (j + 1 : ℝ)) := by positivity
          exact mul_le_mul hpow' hlogj (by positivity) (by positivity [hL])
        have hbound : x ≤ (6 * codingConstant + 1) * 2 * D * L *
            (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ)) := by
          dsimp [x]
          have hc : 0 ≤ 6 * codingConstant + 1 := by positivity [codingConstant_pos]
          calc
            _ = (6 * codingConstant + 1) *
                ((2 : ℝ) ^ highProfileRank d p N (j + 1) *
                  logRatio (JointSampleDimension d (N + 1 + j))
                    (highProfileRank d p N (j + 1))) := by ring
            _ ≤ (6 * codingConstant + 1) *
                (2 * D * Real.exp (-η * (j + 1 : ℝ)) * (L * (j + 1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hprod hc
            _ = _ := by ring
        have hgoal : x + 1 ≤
            ((6 * codingConstant + 1) * 2 * D * L *
              (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ)) + 1) := by linarith
        calc
          (Nat.ceil x : ℝ) ≤ x + 1 := hceil
          _ ≤ _ := hgoal
      _ = A * D * (∑ j ∈ Finset.range W,
          (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ))) + W := by
        rw [Finset.sum_add_distrib]
        rw [show (∑ _j ∈ Finset.range W, (1 : ℝ)) = (W : ℝ) by simp]
        rw [Finset.mul_sum]
        apply congrArg (fun z : ℝ => z + (W : ℝ))
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A]
        ring_nf
      _ ≤ A * D * expPolynomialTsum 1 η + W := by
        have hshift : ∀ j ∈ Finset.range W,
            (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ)) ≤
              (j + 1 : ℝ) * Real.exp (-η * j) := by
          intro j hj
          have harg : -η * (j + 1 : ℝ) ≤ -η * j := by
            have hjpos : 0 ≤ (j : ℝ) := by positivity
            nlinarith
          have hexp := Real.exp_le_exp.mpr harg
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
        have hsum := Finset.sum_le_sum hshift
        have htsum := finite_expPolynomialSum_le_tsum (k := 1) (K := W) heta
        have hfactor : (∑ j ∈ Finset.range W,
            (j + 1 : ℝ) * Real.exp (-η * j)) ≤ expPolynomialTsum 1 η := by
          simpa [pow_one] using htsum
        have hboundSum : (∑ j ∈ Finset.range W,
            (j + 1 : ℝ) * Real.exp (-η * (j + 1 : ℝ))) ≤
              expPolynomialTsum 1 η := hsum.trans hfactor
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hboundSum (mul_nonneg hA.le hDpos.le)
        · rfl
  have hfull :
      (∑ j : Fin W,
        (Nat.ceil ((6 * codingConstant + 1) * (2 : ℝ) ^
          highProfileRank d p N (j.val + 1) *
          logRatio (JointSampleDimension d (N + 1 + j.val))
            (highProfileRank d p N (j.val + 1)) : ℝ) : ℝ)) =
      ∑ j ∈ Finset.range W,
    (Nat.ceil ((6 * codingConstant + 1) *
      (2 : ℝ) ^ highProfileRank d p N (j + 1) *
      logRatio (JointSampleDimension d (N + 1 + j))
        (highProfileRank d p N (j + 1)) : ℝ) : ℝ) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      (Nat.ceil ((6 * codingConstant + 1) *
        (2 : ℝ) ^ highProfileRank d p N (j + 1) *
        logRatio (JointSampleDimension d (N + 1 + j))
          (highProfileRank d p N (j + 1)) : ℝ) : ℝ)) W)
  rw [hfull]
  calc
    _ ≤ A * D * expPolynomialTsum 1 η + W := hfinite
    _ ≤ (A * expPolynomialTsum 1 η + Wc) * D := by
      change A * D * expPolynomialTsum 1 η + (W : ℝ) ≤
        (A * expPolynomialTsum 1 η + Wc) * D
      nlinarith [hwindowDim]

end BrownianSharp.AlignmentPaperJointHighGradeCostSum

end
