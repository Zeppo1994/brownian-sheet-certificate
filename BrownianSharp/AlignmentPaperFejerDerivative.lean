import BrownianSharp.AlignmentPaperFejerPointwise
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Derivative decay for the Fejér kernels. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperFejerDerivative

open BrownianSharp.AlignmentPaperFejerPointwise
open HaarQuarter.TheoremD.FejerFourier
open HaarQuarter.TrigonometricHaarExtraction

def characterSum (N : ℕ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range N, character (r:ℤ) x

def characterSumDerivative (N : ℕ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range N,
    (((2*Real.pi*(r:ℝ):ℝ):ℂ) * Complex.I) * character (r:ℤ) x

private theorem character_hasDerivAt (r : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => character (r:ℤ) t)
      ((((2*Real.pi*(r:ℝ):ℝ):ℂ)*Complex.I) * character (r:ℤ) x) x := by
  let c : ℂ := ((2*Real.pi*(r:ℝ):ℝ):ℂ)*Complex.I
  have harg : HasDerivAt (fun t : ℝ => c * (t:ℂ)) c x := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul c
  have h := (Complex.hasDerivAt_exp (c*(x:ℂ))).comp x harg
  simpa [character, c, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h

theorem characterSum_hasDerivAt (N : ℕ) (x : ℝ) :
    HasDerivAt (fun t => characterSum N t) (characterSumDerivative N x) x := by
  have h := HasDerivAt.sum (u := Finset.range N)
    (fun r hr => character_hasDerivAt r x)
  simpa only [characterSum, characterSumDerivative, ← Finset.sum_apply] using h

theorem realFejerKernel_hasDerivAt (N : ℕ) (x : ℝ) :
    HasDerivAt (realFejerKernel N)
      (2 * @inner ℝ ℂ _ (characterSum N x) (characterSumDerivative N x) / (N:ℝ)) x := by
  have hS := characterSum_hasDerivAt N x
  have hnormDeriv := hS.norm_sq
  have hquot := hnormDeriv.div_const (N:ℝ)
  have hfunction : realFejerKernel N = fun t => ‖characterSum N t‖^2/(N:ℝ) := by
    funext t
    simp [realFejerKernel, characterSum, Complex.normSq_eq_norm_sq]
  rw [hfunction]
  exact hquot

private theorem characterSum_deriv_norm_le_chord (N : ℕ) (x : ℝ)
    (hD : 0 < characterChord x) :
    ‖characterSumDerivative N x‖ ≤
      (2*Real.pi) * (‖characterSum N x‖ + N) / characterChord x := by
  let z := character 1 x
  let S := characterSum N x
  have hsum : S = ∑ r ∈ Finset.range N, z^r := by
    dsimp [S, characterSum]
    apply Finset.sum_congr rfl
    intro r hr
    simpa [z] using character_nat_pow r x
  have hweighted : (∑ r ∈ Finset.range N, (r:ℂ)*z^r) =
      ∑ r ∈ Finset.range N, (r:ℂ)*character (r:ℤ) x := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [character_nat_pow r x]
  have hid0 := weighted_geometric_sum N z
  have hid : (1-z) * characterSumDerivative N x =
      (((2*Real.pi:ℝ):ℂ)*Complex.I) *
        (z*S-(N:ℂ)*z^N) := by
    dsimp [characterSumDerivative]
    have hsum' : (∑ r ∈ Finset.range N,
          (((2*Real.pi*(r:ℝ):ℝ):ℂ)*Complex.I)*character (r:ℤ) x) =
        (((2*Real.pi:ℝ):ℂ)*Complex.I) *
          (∑ r ∈ Finset.range N, (r:ℂ)*character (r:ℤ) x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      ring
    rw [hsum']
    have hid1 := congrArg (fun w : ℂ => (((2*Real.pi:ℝ):ℂ)*Complex.I) * w) hid0
    rw [hweighted, ← hsum] at hid1
    calc
      _ = (((2*Real.pi:ℝ):ℂ)*Complex.I) *
          ((1-z) * ∑ r ∈ Finset.range N, (r:ℂ)*character (r:ℤ) x) := by ring
      _ = (((2*Real.pi:ℝ):ℂ)*Complex.I) *
          (z * S - (N:ℂ)*z^N) := by simpa [mul_assoc] using hid1
  have hznorm : ‖z‖ = 1 := character_norm 1 x
  have hDnorm : ‖1-z‖ = characterChord x := by
    dsimp [characterChord, z]
    rw [norm_sub_rev]
  have hnorm : ‖z*S-(N:ℂ)*z^N‖ ≤ ‖S‖ + N := by
    calc
      _ ≤ ‖z*S‖ + ‖(N:ℂ)*z^N‖ := norm_sub_le _ _
      _ = ‖S‖ + N := by simp [hznorm, norm_pow]
  have hscale : ‖(((2*Real.pi:ℝ):ℂ)*Complex.I)‖ = 2*Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    simp
  have hmulnorm := congrArg norm hid
  rw [norm_mul, hDnorm, norm_mul, hscale] at hmulnorm
  have hπ : 0 ≤ 2*Real.pi := by positivity
  have hbound : characterChord x * ‖characterSumDerivative N x‖ ≤
      (2*Real.pi)*(‖S‖+N) := by
    calc
      _ = (2*Real.pi) * ‖z*S-(N:ℂ)*z^N‖ := hmulnorm
      _ ≤ (2*Real.pi)*(‖S‖+N) := mul_le_mul_of_nonneg_left hnorm hπ
  exact (le_div_iff₀ hD).2 (by simpa [mul_comm] using hbound)

theorem realFejerKernel_deriv_decay (N : ℕ) (hN : 0 < N) (x : ℝ) :
    |deriv (realFejerKernel N) x| ≤
      48*Real.pi*(N:ℝ)^2 /
        (1+((N:ℝ)*characterChord x)^2) := by
  let Sfun : ℝ → ℂ := characterSum N
  let Spfun : ℝ → ℂ := characterSumDerivative N
  have hS := characterSum_hasDerivAt N x
  have hSx : Sfun x = characterSum N x := rfl
  have hSpx : Spfun x = characterSumDerivative N x := rfl
  have hnormDeriv := hS.norm_sq
  have hquot := hnormDeriv.div_const (N:ℝ)
  have hfunction : (fun t => realFejerKernel N t) =
      (fun t => ‖Sfun t‖^2 / (N:ℝ)) := by
    funext t
    simp [realFejerKernel, Sfun, characterSum, Complex.normSq_eq_norm_sq]
  have hF : HasDerivAt (fun t => realFejerKernel N t)
      (2 * @inner ℝ ℂ _ (Sfun x) (Spfun x) / (N:ℝ)) x := by
    rw [hfunction]
    exact hquot
  have hderivEq := hF.deriv
  have hinner : |@inner ℝ ℂ _ (Sfun x) (Spfun x)| ≤
      ‖Sfun x‖*‖Spfun x‖ := abs_real_inner_le_norm _ _
  have hSbound : ‖Sfun x‖ ≤ N := by
    dsimp [Sfun, characterSum]
    calc
      _ ≤ ∑ r ∈ Finset.range N, ‖character (r:ℤ) x‖ := norm_sum_le _ _
      _ = N := by simp [character_norm, Finset.sum_const, nsmul_eq_mul]
  have hSpbound : ‖Spfun x‖ ≤ (2*Real.pi)*(N:ℝ)^2 := by
    dsimp [Spfun, characterSumDerivative]
    calc
      _ ≤ ∑ r ∈ Finset.range N,
          ‖(((2*Real.pi*(r:ℝ):ℝ):ℂ)*Complex.I)*character (r:ℤ) x‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ Finset.range N, (2*Real.pi)*(N:ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrle : (r:ℝ) ≤ (N:ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hr))
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), Complex.norm_I, character_norm]
        have hpi : 0 ≤ 2*Real.pi := by positivity
        nlinarith [hrle, hpi]
      _ = (2*Real.pi)*(N:ℝ)^2 := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two]
        ring
  have hSpHigh : ∀ (hD : 0 < characterChord x),
      ‖Spfun x‖ ≤ (2*Real.pi)*(‖Sfun x‖+N)/characterChord x := by
    intro hD
    exact characterSum_deriv_norm_le_chord N x hD
  have hSdecay : characterChord x ≠ 0 →
      ‖Sfun x‖ ≤ 2/characterChord x := by
    intro hD
    let z := character 1 x
    have hid := character_geometric_sum N x
    have hchar : ‖character (N:ℤ) x - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖character (N:ℤ) x‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp [character_norm]; norm_num
    have hDnorm : ‖character 1 x-1‖ = characterChord x := by
      simp [characterChord, norm_sub_rev]
    have hprod : characterChord x * ‖Sfun x‖ ≤ 2 := by
      have hp := congrArg norm hid
      rw [norm_mul, hDnorm] at hp
      have heq : characterChord x * ‖Sfun x‖ = ‖character (N:ℤ) x-1‖ := by
        simpa [Sfun, characterSum, mul_comm] using hp
      exact le_trans (le_of_eq heq) hchar
    have hDpos : 0 < characterChord x := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
    exact (le_div_iff₀ hDpos).2
      (by simpa [mul_comm] using hprod)
  by_cases hsmall : (N:ℝ)*characterChord x ≤ 1
  · have hqnon : 0 ≤ (N:ℝ)*characterChord x := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    have hderivBound : |deriv (realFejerKernel N) x| ≤ 4*Real.pi*(N:ℝ)^2 := by
      rw [hF.deriv]
      rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (N:ℝ))]
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
      have h : |@inner ℝ ℂ _ (Sfun x) (Spfun x)| ≤ (N:ℝ)*((2*Real.pi)*(N:ℝ)^2) :=
        hinner.trans (mul_le_mul hSbound hSpbound (norm_nonneg _) (by positivity))
      convert div_le_div_of_nonneg_right (show 2*|@inner ℝ ℂ _ (Sfun x) (Spfun x)| ≤
        2*((N:ℝ)*((2*Real.pi)*(N:ℝ)^2)) by nlinarith) (by positivity : 0≤(N:ℝ)) using 1
      field_simp
      ring
    have hden : 1+((N:ℝ)*characterChord x)^2 ≤ 2 := by nlinarith
    have hpos : 0<1+((N:ℝ)*characterChord x)^2 := by positivity
    have : 4*Real.pi*(N:ℝ)^2 ≤ 48*Real.pi*(N:ℝ)^2 /
        (1+((N:ℝ)*characterChord x)^2) := by
      rw [le_div_iff₀ hpos]
      have hcoef : 0 ≤ 4*Real.pi*(N:ℝ)^2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hden hcoef
      nlinarith [hmul, hcoef]
    exact hderivBound.trans this
  · have hlarge : 1 < (N:ℝ)*characterChord x := lt_of_not_ge hsmall
    have hD : characterChord x ≠ 0 := by
      intro hz
      rw [hz] at hlarge
      norm_num at hlarge
    have hDpos : 0 < characterChord x := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
    have hS : ‖Sfun x‖ ≤ 2/characterChord x := hSdecay hD
    have hSp : ‖Spfun x‖ ≤ (2*Real.pi)*(‖Sfun x‖+N)/characterChord x := hSpHigh hDpos
    have hderivBound : |deriv (realFejerKernel N) x| ≤ 24*Real.pi/(characterChord x)^2 := by
      rw [hF.deriv]
      rw [abs_div, abs_of_nonneg (by positivity : 0≤(N:ℝ))]
      rw [abs_mul, abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
      have hInv : 1/characterChord x ≤ (N:ℝ) := by
        exact (div_le_iff₀ hDpos).2 (by nlinarith [hlarge])
      have hSsmall : ‖Sfun x‖+N ≤ 3*(N:ℝ) := by
        have hS' : ‖Sfun x‖ ≤ 2*(1/characterChord x) := by
          calc
            _ ≤ 2/characterChord x := hS
            _ = 2*(1/characterChord x) := by ring
        calc
          ‖Sfun x‖ + N ≤ 2*(1/characterChord x) + N := by
            exact add_le_add hS' (le_of_eq rfl)
          _ ≤ 3*(N:ℝ) := by nlinarith [hInv]
      have hinner' : |@inner ℝ ℂ _ (Sfun x) (Spfun x)| ≤
          ‖Sfun x‖ * ((2*Real.pi)*(‖Sfun x‖+N)/characterChord x) :=
        hinner.trans (mul_le_mul_of_nonneg_left hSp (norm_nonneg _))
      have hinner'' : |@inner ℝ ℂ _ (Sfun x) (Spfun x)| ≤
          (2*Real.pi)*(6*(N:ℝ)/characterChord x^2) := by
        have hm : ‖Sfun x‖*(‖Sfun x‖+N) ≤ (2/characterChord x)*(3*(N:ℝ)) :=
          mul_le_mul hS hSsmall (by positivity) (by positivity)
        have hm' : ‖Sfun x‖*(‖Sfun x‖+N)*characterChord x ≤ 6*(N:ℝ) := by
          calc
            _ ≤ ((2/characterChord x)*(3*(N:ℝ)))*characterChord x :=
              mul_le_mul_of_nonneg_right hm (le_of_lt hDpos)
            _ = 6*(N:ℝ) := by field_simp; ring
        have hscale : 0≤(2*Real.pi)/characterChord x := by positivity
        calc
          _ ≤ ‖Sfun x‖*((2*Real.pi)*(‖Sfun x‖+N)/characterChord x) := hinner'
          _ = ((2*Real.pi)/characterChord x) *
              (‖Sfun x‖*(‖Sfun x‖+N)) := by ring
          _ ≤ ((2*Real.pi)/characterChord x) *
              ((2/characterChord x)*(3*(N:ℝ))) :=
            mul_le_mul_of_nonneg_left hm hscale
          _ = (2*Real.pi)*(6*(N:ℝ)/characterChord x^2) := by field_simp; ring
      have hmain : 2*|@inner ℝ ℂ _ (Sfun x) (Spfun x)|/(N:ℝ) ≤
          24*Real.pi/characterChord x^2 := by
        have hNpos : 0<(N:ℝ) := by exact_mod_cast hN
        have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner'' (by norm_num:0≤(2:ℝ))) hNpos.le
        convert this using 1 <;> field_simp <;> ring
      simpa [abs_div, abs_of_nonneg (by positivity : 0≤(N:ℝ)), abs_mul,
        abs_of_nonneg (by norm_num : 0≤(2:ℝ))] using hmain
    have hden : 1+((N:ℝ)*characterChord x)^2 ≤
        2*((N:ℝ)*characterChord x)^2 := by nlinarith
    have htarget : 24*Real.pi/characterChord x^2 ≤
        48*Real.pi*(N:ℝ)^2/(1+((N:ℝ)*characterChord x)^2) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hDpos) (by positivity)]
      nlinarith [show 0≤Real.pi by positivity, hden]
    exact hderivBound.trans htarget

end BrownianSharp.AlignmentPaperFejerDerivative
