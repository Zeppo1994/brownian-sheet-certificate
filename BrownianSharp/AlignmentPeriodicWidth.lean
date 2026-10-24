import BrownianSharp.CarlRateExtraction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Generic periodic width extraction

This file develops the Carl entropy-to-width argument for arbitrary compact
sets in normed spaces, with a polynomial-logarithmic rate.
-/

open Set HaarQuarter BrownianSharp
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPeriodicWidth

noncomputable section

private theorem four_pow_eq_two_pow_sq (j : ℕ) :
    (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
  calc
    (4 : ℝ) ^ j = ((2 : ℝ) ^ 2) ^ j := by norm_num
    _ = (2 : ℝ) ^ (2 * j) := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (j * 2) := by
      exact congrArg (fun e : ℕ => (2 : ℝ) ^ e) (Nat.mul_comm 2 j)
    _ = ((2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul]

/-- Polynomial-logarithmic scale used by the periodic width corollary. -/
def rate (s a : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (-s) * (Real.log (k : ℝ)) ^ a

/-- The largest scale factor needed in the finite Carl budget across the
middle range, split at the quadratic exponent. -/
def middleScaleWeight (s : ℝ) (m₀ m : ℕ) : ℝ :=
  if s ≤ 2 then (m:ℝ)^(2-s) else (m₀:ℝ)^(2-s)

/-- The corresponding budget weight for a natural polynomial budget power A. -/
def scaleWeightA (A : ℕ) (s : ℝ) (m₀ m : ℕ) : ℝ :=
  if s ≤ A then (m:ℝ)^((A:ℝ)-s) else (m₀:ℝ)^((A:ℝ)-s)

/-- Local-depth radius schedule paired with the scalar budget Q=2^A. -/
def localDepthEta (A L : ℕ) (B : ℝ) (j : Fin L) : ℝ :=
  (2:ℝ)^A * B / (2:ℝ)^(A*L) / (2:ℝ)^(L-(j.val+1))

theorem localDepthEta_pos {A L : ℕ} {B : ℝ} (hB : 0 < B) (j : Fin L) :
    0 < localDepthEta A L B j := by
  unfold localDepthEta
  positivity

/-- The local geometric radius schedule pays for an increment whose endpoint
errors are bounded by the Q-dyadic width budget. -/
theorem local_depth_ratio_of_Q_budget
    {A q L : ℕ} (hAq : A+1 ≤ 3*q) {B : ℝ} (hB : 0 < B)
    {δ : Fin (L+1) → ℝ} (hδ : ∀ j, δ j ≤ 2*B/(2:ℝ)^(A*j.val))
    (j : Fin L) :
    (δ j.succ+δ j.castSucc)/localDepthEta A L B j ≤
      10*(2:ℝ)^(3*q*(L-(j.val+1))) := by
  let d := L-(j.val+1)
  have hjL : j.val+1 ≤ L := j.isLt
  have hd : L = j.val+1+d := by dsimp [d]; omega
  have hdiff : L-(j.val+1)=d := by dsimp [d]
  have hδs : δ j.succ ≤ 2*B/(2:ℝ)^(A*(j.val+1)) := hδ j.succ
  have hδc : δ j.castSucc ≤ 2*B/(2:ℝ)^(A*j.val) := hδ j.castSucc
  have hsuccsmall : (2:ℝ)^A ≤ (2:ℝ)^(A*(j.val+1)) := by
    have he : A ≤ A*(j.val+1) := by nlinarith
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1≤2) he)
  have hδsum : δ j.succ+δ j.castSucc ≤ 4*B/(2:ℝ)^(A*j.val) := by
    have hpow : (2:ℝ)^(A*j.val) ≤ (2:ℝ)^(A*(j.val+1)) := by
      have he : A*j.val ≤ A*(j.val+1) := by nlinarith
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 1≤2) he)
    have hden : 0 < (2:ℝ)^(A*j.val) := by positivity
    have hsle : 2*B/(2:ℝ)^(A*(j.val+1)) ≤ 2*B/(2:ℝ)^(A*j.val) := by
      apply div_le_div_of_nonneg_left (by positivity) hden hpow
    calc
      δ j.succ+δ j.castSucc ≤
          2*B/(2:ℝ)^(A*(j.val+1))+2*B/(2:ℝ)^(A*j.val) := add_le_add hδs hδc
      _ ≤ 2*B/(2:ℝ)^(A*j.val)+2*B/(2:ℝ)^(A*j.val) := add_le_add hsle le_rfl
      _ = 4*B/(2:ℝ)^(A*j.val) := by ring
  have hscale :
      (4*B/(2:ℝ)^(A*j.val)) ≤
        10*(2:ℝ)^(3*q*d)*localDepthEta A L B j := by
    have hsum : j.val+1+d=L := by omega
    have hAL : A*L=A*j.val+A+A*d := by
      have heq := congrArg (fun n : ℕ => A*n) hsum
      calc
        A*L = A*(j.val+1+d) := heq.symm
        _ = A*j.val+A+A*d := by ring
    simp only [localDepthEta, hdiff, hAL]
    have hAqd : (A+1)*d ≤ 3*q*d := by
      calc
        (A+1)*d ≤ (3*q)*d := Nat.mul_le_mul_right d hAq
        _ = 3*q*d := by ring
    have hpowD : (2:ℝ)^((A+1)*d) ≤ (2:ℝ)^(3*q*d) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤2) hAqd
    have hdenpow : (2:ℝ)^(A*j.val+A+A*d)*(2:ℝ)^d =
        (2:ℝ)^(A*j.val+A)*(2:ℝ)^((A+1)*d) := by
      rw [← pow_add, show A*j.val+A+A*d+d=A*j.val+A+(A+1)*d by ring, pow_add]
    have hpos : 0 < (2:ℝ)^(A*j.val) := by positivity
    have hBpos : 0 < B := hB
    field_simp
    calc
      _ = 4*((2:ℝ)^(A*j.val+A+A*d)*(2:ℝ)^d) := by ring
      _ = 4*((2:ℝ)^(A*j.val+A)*(2:ℝ)^((A+1)*d)) := by rw [hdenpow]
      _ ≤ 4*((2:ℝ)^(A*j.val+A)*(2:ℝ)^(3*q*d)) := by gcongr
      _ ≤ 10*((2:ℝ)^(A*j.val+A)*(2:ℝ)^(3*q*d)) := by
        have hp : 0 ≤ (2:ℝ)^(A*j.val+A)*(2:ℝ)^(3*q*d) := by positivity
        nlinarith
      _ = _ := by ring
  have heta : 0 < localDepthEta A L B j := localDepthEta_pos hB j
  apply (div_le_iff₀ heta).2
  exact le_trans hδsum hscale

/-- The local radii have a finite geometric sum bounded independently of L. -/
theorem localDepthEta_sum_le (A L : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (∑ j : Fin L, localDepthEta A L B j) ≤
      (2:ℝ)^(A+1)*B/(2:ℝ)^(A*L) := by
  let c : ℝ := (2:ℝ)^A*B/(2:ℝ)^(A*L)
  have hgeom : (∑ j : Fin L, (1/2:ℝ)^(L-(j.val+1))) ≤ 2 := by
    have hrev : (∑ j : Fin L, (1/2:ℝ)^(L-(j.val+1))) =
        ∑ i : Fin L, (1/2:ℝ)^i.val := by
      apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin L))
      intro i
      simp [Fin.revPerm, Fin.rev]
    rw [hrev, Fin.sum_univ_eq_sum_range]
    simpa using (sum_geometric_two_le L)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ = c * ∑ j : Fin L, (1/2:ℝ)^(L-(j.val+1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [c, localDepthEta, div_eq_mul_inv, one_div, inv_pow]
    _ ≤ c*2 := mul_le_mul_of_nonneg_left hgeom hc
    _ = (2:ℝ)^(A+1)*B/(2:ℝ)^(A*L) := by
      dsimp [c]
      rw [pow_succ]
      ring

theorem middleScaleWeight_pos {s : ℝ} {m₀ m : ℕ}
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) : 0 < middleScaleWeight s m₀ m := by
  dsimp [middleScaleWeight]
  split_ifs <;> positivity

theorem rate_nonneg {s a : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ rate s a k := by
  unfold rate
  apply mul_nonneg
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))) _

theorem rate_pos {s a : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    0 < rate s a k := by
  unfold rate
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < k by omega))) _

theorem logPow_mono {a : ℝ} (ha : 0 ≤ a) {m n : ℕ}
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    (Real.log (m : ℝ)) ^ a ≤ (Real.log (n : ℝ)) ^ a := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmn : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmn)
  exact Real.rpow_le_rpow hlogm.le hlogmn ha

theorem rate_log_mono {s a : ℝ} (ha : 0 ≤ a) {m n : ℕ}
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    (m : ℝ) ^ (-s) * (Real.log (m : ℝ)) ^ a ≤
      (m : ℝ) ^ (-s) * (Real.log (n : ℝ)) ^ a := by
  exact mul_le_mul_of_nonneg_left (logPow_mono ha hm hmn)
    (Real.rpow_nonneg (by positivity) _)

/-- For rates no faster than quadratic, dyadic dilation pays for the two
orders contributed by the Carl cover. -/
theorem dyadic_rate_scale_le {s a : ℝ} (ha : 0 ≤ a)
    {r m₀ m N j : ℕ} (hr : 2 ≤ r) (hm₀ : 1 ≤ m₀) (hm₀r : m₀ ≤ r)
    (hrm : r ≤ m) (hmN : m ≤ N)
    (hindex : r + 1 = 2 ^ j) :
    (4 : ℝ) ^ j * rate s a r ≤
      4 * middleScaleWeight s m₀ m * (Real.log (N : ℝ)) ^ a := by
  have hrpos : 0 < (r : ℝ) := by positivity
  have hlogr : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hlogmono : (Real.log (r : ℝ)) ^ a ≤ (Real.log (N : ℝ)) ^ a := by
    have hlogle : Real.log (r : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (le_trans hrm hmN))
    exact Real.rpow_le_rpow hlogr.le hlogle ha
  have hindexR : (r : ℝ) + 1 = (2 : ℝ) ^ j := by exact_mod_cast hindex
  have h4 : (4 : ℝ) ^ j = ((r : ℝ) + 1) ^ 2 := by
    rw [four_pow_eq_two_pow_sq, hindexR]
  have hgeom : ((r : ℝ) + 1) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := by
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hpow : (r : ℝ) ^ (2 - s) ≤ middleScaleWeight s m₀ m := by
    by_cases hs2 : s ≤ 2
    · simp [middleScaleWeight, hs2]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrm) (by linarith)
    · have hm₀pos : 0 < (m₀:ℝ) := by exact_mod_cast (show 0 < m₀ by omega)
      have hm₀rR : (m₀:ℝ) ≤ (r:ℝ) := by exact_mod_cast hm₀r
      have hrev := Real.rpow_le_rpow_of_nonpos hm₀pos hm₀rR (by linarith : 2-s ≤ 0)
      simpa [middleScaleWeight, hs2] using hrev
  rw [h4]
  unfold rate
  have hfactor : ((r : ℝ) + 1) ^ 2 * (r : ℝ) ^ (-s) ≤
      4 * middleScaleWeight s m₀ m := by
    calc
      ((r : ℝ) + 1) ^ 2 * (r : ℝ) ^ (-s) ≤
          4 * (r : ℝ) ^ 2 * (r : ℝ) ^ (-s) := by
            exact mul_le_mul_of_nonneg_right hgeom (by positivity)
      _ = 4 * (r : ℝ) ^ (2 - s) := by
            have hpower : (r : ℝ) ^ 2 * (r : ℝ) ^ (-s) = (r : ℝ) ^ (2 - s) := by
              rw [← Real.rpow_natCast (r : ℝ) 2, ← Real.rpow_add hrpos]
              congr 1
            calc
              4 * (r : ℝ) ^ 2 * (r : ℝ) ^ (-s) =
                  4 * ((r : ℝ) ^ 2 * (r : ℝ) ^ (-s)) := by ring
              _ = 4 * (r : ℝ) ^ (2 - s) := by rw [hpower]
      _ ≤ 4 * middleScaleWeight s m₀ m := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hqnonneg : 0 ≤ (Real.log (r : ℝ)) ^ a := by positivity
  calc
    ((r : ℝ) + 1) ^ 2 * ((r : ℝ) ^ (-s) * (Real.log (r : ℝ)) ^ a) ≤
        (4 * middleScaleWeight s m₀ m) * (Real.log (r : ℝ)) ^ a := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfactor hqnonneg
    _ ≤ 4 * middleScaleWeight s m₀ m * (Real.log (N : ℝ)) ^ a := by
      have hcoef : 0 ≤ 4 * middleScaleWeight s m₀ m := by
        dsimp [middleScaleWeight]
        split_ifs <;> positivity
      nlinarith [mul_le_mul_of_nonneg_left hlogmono hcoef]

/-- Polynomial-log rate scaling for a general natural scalar budget power A.
This is the scale estimate needed when Q=2^A replaces the quadratic 4. -/
theorem dyadic_rate_scale_le_A {s a : ℝ} (ha : 0 ≤ a) (A : ℕ)
    {r m₀ m N j : ℕ} (hr : 2 ≤ r) (hm₀ : 1 ≤ m₀) (hm₀r : m₀ ≤ r)
    (hrm : r ≤ m) (hmN : m ≤ N)
    (hindex : r + 1 = 2 ^ j) :
    ((2:ℝ)^(A*j)) * rate s a r ≤
      (2:ℝ)^A * scaleWeightA A s m₀ m * (Real.log (N:ℝ))^a := by
  have hrpos : 0 < (r:ℝ) := by positivity
  have hlogr : 0 < Real.log (r:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hlogmono : (Real.log (r:ℝ))^a ≤ (Real.log (N:ℝ))^a := by
    have hle : Real.log (r:ℝ) ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (le_trans hrm hmN))
    exact Real.rpow_le_rpow hlogr.le hle ha
  have hindexR : (r:ℝ)+1=(2:ℝ)^j := by exact_mod_cast hindex
  have hpowindex : ((2:ℝ)^(A*j)) = ((r:ℝ)+1)^A := by
    rw [hindexR, ← pow_mul, Nat.mul_comm A j]
  have hgeom : ((r:ℝ)+1)^A ≤ (2:ℝ)^A*(r:ℝ)^A := by
    have hsum : (r:ℝ)+1 ≤ 2*(r:ℝ) := by
      have hrR : (1:ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      linarith
    calc
      ((r:ℝ)+1)^A ≤ (2*(r:ℝ))^A := by gcongr
      _ = (2:ℝ)^A*(r:ℝ)^A := by rw [mul_pow]
  have hweight : (r:ℝ)^((A:ℝ)-s) ≤ scaleWeightA A s m₀ m := by
    by_cases hsa : s ≤ A
    · simp [scaleWeightA, hsa]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrm) (by linarith)
    · have hm₀pos : 0 < (m₀:ℝ) := by exact_mod_cast (show 0 < m₀ by omega)
      have hm₀rR : (m₀:ℝ) ≤ (r:ℝ) := by exact_mod_cast hm₀r
      have hrev := Real.rpow_le_rpow_of_nonpos hm₀pos hm₀rR (by linarith : (A:ℝ)-s ≤ 0)
      simpa [scaleWeightA, hsa] using hrev
  have hfactor : ((r:ℝ)+1)^A*(r:ℝ)^(-s) ≤
      (2:ℝ)^A*scaleWeightA A s m₀ m := by
    calc
      _ ≤ (2:ℝ)^A*(r:ℝ)^A*(r:ℝ)^(-s) :=
        mul_le_mul_of_nonneg_right hgeom (by positivity)
      _ = (2:ℝ)^A*((r:ℝ)^A*(r:ℝ)^(-s)) := by ring
      _ = (2:ℝ)^A*(r:ℝ)^((A:ℝ)-s) := by
        rw [← Real.rpow_natCast (r:ℝ) A, ← Real.rpow_add hrpos]
        congr 2
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)
  have hcoeff : 0 ≤ (2:ℝ)^A*scaleWeightA A s m₀ m := by
    dsimp [scaleWeightA]
    split_ifs <;> positivity
  have hlognonneg : 0 ≤ (Real.log (r:ℝ))^a := by positivity
  unfold rate
  rw [hpowindex]
  calc
    ((r:ℝ)+1)^A*((r:ℝ)^(-s)*(Real.log (r:ℝ))^a) ≤
        ((2:ℝ)^A*scaleWeightA A s m₀ m)*(Real.log (r:ℝ))^a := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfactor hlognonneg
    _ ≤ (2:ℝ)^A*scaleWeightA A s m₀ m*(Real.log (N:ℝ))^a := by
          exact mul_le_mul_of_nonneg_left hlogmono hcoeff

/-- Assemble a sharp polynomial-logarithmic width upper estimate into the
finite dyadic width budget used by the certified Carl cover. The ambient set
and its zero-width radius are completely generic. -/
theorem dyadic_width_budget_of_rate_upper
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {s a : ℝ} (ha : 0 ≤ a)
    {m₀ m L : ℕ} (hm₀ : 2 ≤ m₀) (hm₀m : m₀ ≤ m)
    (hmN : m ≤ 2 ^ L) (_hL : 1 ≤ L)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 < C)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth S 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth S k ≤
        ENNReal.ofReal (C * rate s a k)) :
    ∃ B : ℝ,
      B = R * (m₀ : ℝ)^2 + 4 * C * middleScaleWeight s m₀ m *
        (Real.log (2 ^ L : ℝ))^a +
        (2 ^ L : ℝ)^2 *
          (HaarQuarter.TheoremD.Width.kolmogorovWidth S m).toReal ∧
      0 < B ∧
      ∀ j : Fin (L + 1),
        HaarQuarter.TheoremD.Width.kolmogorovWidth S (2 ^ j.val - 1) ≤
          ENNReal.ofReal (B / (4 : ℝ)^j.val) := by
  let N : ℝ := (2 ^ L : ℕ)
  let Q : ℝ := (Real.log N)^a
  have hm2 : 2 ≤ m := le_trans hm₀ hm₀m
  have hN2 : 2 ≤ 2 ^ L := le_trans hm2 hmN
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by
      dsimp [N]
      exact_mod_cast (show 1 ≤ 2 ^ L by omega))
    exact Real.rpow_nonneg hlog _
  have hfinite : HaarQuarter.TheoremD.Width.kolmogorovWidth S m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper m hm₀m)
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth S m).toReal
  have hw : HaarQuarter.TheoremD.Width.kolmogorovWidth S m = ENNReal.ofReal w := by
    dsimp [w]
    exact (ENNReal.ofReal_toReal hfinite).symm
  have hw0 : 0 ≤ w := by dsimp [w]; exact ENNReal.toReal_nonneg
  let B : ℝ := R*(m₀:ℝ)^2 + 4*C*middleScaleWeight s m₀ m*Q + N^2*w
  have hB : 0 < B := by
    dsimp [B]
    have hNlog : 0 < Real.log N := Real.log_pos (by
      dsimp [N]
      exact_mod_cast (by omega : 1 < 2 ^ L))
    have hQpos : 0 < (Real.log N)^a := Real.rpow_pos_of_pos hNlog _
    have hweight : 0 < middleScaleWeight s m₀ m := by
      dsimp [middleScaleWeight]
      split_ifs <;> positivity
    positivity
  refine ⟨B, ?_, hB, ?_⟩
  · simp [B, Q, N, w]
  intro j
  let q : ℕ := 2 ^ j.val - 1
  have hqplus : q + 1 = 2 ^ j.val := by
    dsimp [q]
    exact Nat.sub_add_cancel (Nat.one_le_pow j.val 2 (by omega))
  have hpow4 : (4:ℝ)^j.val = ((q:ℝ)+1)^2 := by
    rw [four_pow_eq_two_pow_sq]
    have hcast : (q:ℝ)+1 = (2:ℝ)^j.val := by exact_mod_cast hqplus
    rw [hcast]
  by_cases hsmall : q < m₀
  · have hmono := HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone S (Nat.zero_le q)
    have hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth S q ≤ ENNReal.ofReal R :=
      le_trans hmono hzero
    have hqplusR : (q:ℝ)+1 ≤ (m₀:ℝ) := by
      have hh : q+1 ≤ m₀ := by omega
      exact_mod_cast hh
    have hbudget : R ≤ B/(4:ℝ)^j.val := by
      apply (le_div_iff₀ (by positivity)).2
      dsimp [B]
      rw [hpow4]
      have hsq : ((q:ℝ)+1)^2 ≤ (m₀:ℝ)^2 := by nlinarith
      have hweight : 0 ≤ middleScaleWeight s m₀ m :=
        (middleScaleWeight_pos (by omega) (by omega)).le
      have hQ0 : 0 ≤ Q := hQ
      have hrest : 0 ≤ 4*C*middleScaleWeight s m₀ m*Q + N^2*w := by positivity
      nlinarith
    exact le_trans hwidth (ENNReal.ofReal_le_ofReal hbudget)
  · have hlarge : m₀ ≤ q := by omega
    by_cases hqle : q ≤ m
    · have hup := hupper q hlarge
      have hscale := dyadic_rate_scale_le (s:=s) (a:=a) (r:=q)
        (m₀:=m₀) (m:=m) (N:=2^L) (j:=j.val) ha
        (by omega : 2 ≤ q) (by omega : 1 ≤ m₀)
        hlarge hqle hmN hqplus
      have hbudget : C*rate s a q ≤ B/(4:ℝ)^j.val := by
        apply (le_div_iff₀ (by positivity)).2
        have hscaled : C*rate s a q*(4:ℝ)^j.val ≤
            4*C*middleScaleWeight s m₀ m*Q := by
          calc
            _ = C*((4:ℝ)^j.val*rate s a q) := by ring
            _ ≤ C*(4*middleScaleWeight s m₀ m*Q) := mul_le_mul_of_nonneg_left hscale hC.le
            _ = _ := by dsimp [Q]; ring
        dsimp [B]
        have hrest : 0 ≤ R*(m₀:ℝ)^2 + N^2*w := by positivity
        nlinarith
      exact le_trans hup (ENNReal.ofReal_le_ofReal hbudget)
    · have hmq : m ≤ q := by omega
      have hmono := HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone S hmq
      have hjL : j.val ≤ L := by omega
      have hpow2 : (2:ℝ)^j.val ≤ N := by
        dsimp [N]
        exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hjL
      have hfactor : (4:ℝ)^j.val ≤ N^2 := by
        rw [four_pow_eq_two_pow_sq]
        have hx0 : 0 ≤ (2:ℝ)^j.val := by positivity
        calc
          ((2:ℝ)^j.val)^2 = (2:ℝ)^j.val * (2:ℝ)^j.val := by ring
          _ ≤ N*(2:ℝ)^j.val := mul_le_mul_of_nonneg_right hpow2 hx0
          _ ≤ N*N := mul_le_mul_of_nonneg_left hpow2 (by positivity)
          _ = N^2 := by ring
      have hbudget : w ≤ B/(4:ℝ)^j.val := by
        apply (le_div_iff₀ (by positivity)).2
        dsimp [B]
        have hprod := mul_le_mul_of_nonneg_right hfactor hw0
        have hweight : 0 ≤ middleScaleWeight s m₀ m :=
          (middleScaleWeight_pos (by omega) (by omega)).le
        have hQ0 : 0 ≤ Q := hQ
        have hrest : 0 ≤ R*(m₀:ℝ)^2 + 4*C*middleScaleWeight s m₀ m*Q := by positivity
        nlinarith
      exact le_trans (le_trans hmono (le_of_eq hw)) (ENNReal.ofReal_le_ofReal hbudget)

/-- General-power version of the dyadic width budget. Taking A>s makes the
middle-scale contribution grow like N^(A−s), which can absorb the fixed
coarse-scale term in an asymptotic extraction. -/
theorem dyadic_width_budget_of_rate_upper_A
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {s a : ℝ} (ha : 0 ≤ a) (A : ℕ) (hsA : s < A)
    {m₀ m L : ℕ} (hm₀ : 2 ≤ m₀) (hm₀m : m₀ ≤ m)
    (hmN : m ≤ 2 ^ L) (_hL : 1 ≤ L)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 < C)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth S 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth S k ≤
        ENNReal.ofReal (C * rate s a k)) :
    ∃ B : ℝ,
      B = R * (m₀:ℝ)^A + (2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log (2^L:ℝ))^a +
        (2^L:ℝ)^A*(HaarQuarter.TheoremD.Width.kolmogorovWidth S m).toReal ∧
      0 < B ∧
      ∀ j : Fin (L+1),
        HaarQuarter.TheoremD.Width.kolmogorovWidth S (2^j.val-1) ≤
          ENNReal.ofReal (B/((2:ℝ)^(A*j.val))) := by
  let N : ℝ := (2 ^ L : ℕ)
  have hm2 : 2 ≤ m := le_trans hm₀ hm₀m
  have hN2 : 2 ≤ 2^L := le_trans hm2 hmN
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hlog : 0 < Real.log N := Real.log_pos (by dsimp [N]; exact_mod_cast (by omega : 1 < 2^L))
  have hlogpow : 0 < (Real.log N)^a := Real.rpow_pos_of_pos hlog _
  have hweight0 : 0 ≤ scaleWeightA A s m₀ m := by
    dsimp [scaleWeightA]
    split_ifs <;> positivity
  have hfinite : HaarQuarter.TheoremD.Width.kolmogorovWidth S m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper m hm₀m)
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth S m).toReal
  have hw : HaarQuarter.TheoremD.Width.kolmogorovWidth S m = ENNReal.ofReal w := by
    dsimp [w]
    exact (ENNReal.ofReal_toReal hfinite).symm
  have hw0 : 0 ≤ w := by dsimp [w]; exact ENNReal.toReal_nonneg
  let B : ℝ := R*(m₀:ℝ)^A + (2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log N)^a + N^A*w
  have hB : 0 < B := by
    dsimp [B]
    have hweight : 0 < scaleWeightA A s m₀ m := by
      dsimp [scaleWeightA]
      split_ifs with hs
      · positivity
      · have hpow : (A:ℝ)-s < 0 := by linarith
        have hm₀pos : 0 < (m₀:ℝ) := by exact_mod_cast (show 0 < m₀ by omega)
        exact Real.rpow_pos_of_pos hm₀pos _
    positivity
  refine ⟨B, ?_, hB, ?_⟩
  · simp [B,N,w]
  intro j
  let q : ℕ := 2^j.val-1
  have hqplus : q+1=2^j.val := by dsimp [q]; exact Nat.sub_add_cancel (Nat.one_le_pow j.val 2 (by omega))
  have hqplusR : (q:ℝ)+1=(2:ℝ)^j.val := by exact_mod_cast hqplus
  have hqscale : ((2:ℝ)^(A*j.val))=((q:ℝ)+1)^A := by
    rw [hqplusR, ← pow_mul, Nat.mul_comm j.val A]
  by_cases hsmall : q < m₀
  · have hmono := HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone S (Nat.zero_le q)
    have hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth S q ≤ ENNReal.ofReal R := le_trans hmono hzero
    have hqle : q+1 ≤ m₀ := by omega
    have hqleR : (q:ℝ)+1 ≤ (m₀:ℝ) := by exact_mod_cast hqle
    have hpow : ((q:ℝ)+1)^A ≤ (m₀:ℝ)^A := by gcongr
    have hbudget : R ≤ B/((2:ℝ)^(A*j.val)) := by
      apply (le_div_iff₀ (by positivity)).2
      rw [hqscale]
      dsimp [B]
      have hrest : 0 ≤ (2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log N)^a+N^A*w := by positivity
      nlinarith
    exact le_trans hwidth (ENNReal.ofReal_le_ofReal hbudget)
  · have hlarge : m₀ ≤ q := by omega
    by_cases hqle : q ≤ m
    · have hup := hupper q hlarge
      have hscale := dyadic_rate_scale_le_A (s:=s) (a:=a) ha A
        (r:=q) (m₀:=m₀) (m:=m) (N:=2^L) (j:=j.val)
        (by omega) (by omega) hlarge hqle hmN hqplus
      have hbudget : C*rate s a q ≤ B/((2:ℝ)^(A*j.val)) := by
        apply (le_div_iff₀ (by positivity)).2
        have hscaled : C*rate s a q*((2:ℝ)^(A*j.val)) ≤
            (2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log N)^a := by
          calc
            _ = C*(((2:ℝ)^(A*j.val))*rate s a q) := by ring
            _ ≤ C*((2:ℝ)^A*scaleWeightA A s m₀ m*(Real.log N)^a) := by
              exact mul_le_mul_of_nonneg_left hscale hC.le
            _ = _ := by ring
        dsimp [B]
        have hrest : 0 ≤ R*(m₀:ℝ)^A+N^A*w := by positivity
        nlinarith
      exact le_trans hup (ENNReal.ofReal_le_ofReal hbudget)
    · have hmq : m ≤ q := by omega
      have hmono := HaarQuarter.TheoremD.Width.kolmogorovWidth_antitone S hmq
      have hjL : j.val ≤ L := by omega
      have hpow : (2:ℝ)^(A*j.val) ≤ N^A := by
        have h2j : (2:ℝ)^j.val ≤ N := by dsimp [N]; exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤2) hjL
        have heq : (2:ℝ)^(A*j.val)=((2:ℝ)^j.val)^A := by
          rw [← pow_mul, Nat.mul_comm j.val A]
        rw [heq]
        exact pow_le_pow_left₀ (by positivity) h2j A
      have hbudget : w ≤ B/((2:ℝ)^(A*j.val)) := by
        apply (le_div_iff₀ (by positivity)).2
        dsimp [B]
        have hprod : (2:ℝ)^(A*j.val)*w ≤ N^A*w := mul_le_mul_of_nonneg_right hpow hw0
        have hrest : 0 ≤ R*(m₀:ℝ)^A+(2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log N)^a := by positivity
        nlinarith
      exact le_trans (le_trans hmono (le_of_eq hw)) (ENNReal.ofReal_le_ofReal hbudget)

/-- Entropy lower bounds force the scalar Carl cover budget to be large.
The statement is rate-generic; only positivity of the polynomial exponent
and nonnegativity of the logarithmic exponent are used. -/
theorem dyadic_budget_lower_of_entropy_lower
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    {L : ℕ} (hL : 1 ≤ L) (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hEntropy : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * rate s a k) ≤ HaarQuarter.TheoremD.entropyNumber k S)
    (hCover : HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1) S ≤
      ENNReal.ofReal (4 * B / (4:ℝ)^L)) :
    (c/4) * (2 ^ L:ℝ)^2 *
      ((97 * (2 ^ L:ℝ)) ^ (-s)) * (Real.log (2 ^ L:ℝ))^a ≤ B := by
  let N : ℝ := (2 ^ L : ℕ)
  have hN2 : 2 ≤ 2^L := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^L := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ L)
  have hN2R : 2 ≤ N := by dsimp [N]; exact_mod_cast hN2
  have hNpos : 0 < N := by linarith
  have hk : 2 ≤ 96*2^L+1 := by omega
  have hkR : 0 < (96*(2^L:ℕ)+1:ℕ) := by omega
  have hNle : (96*(2^L:ℕ)+1:ℕ) ≤ 97*(2^L:ℕ) := by
    have hNpos' : 1 ≤ 2^L := by omega
    omega
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  let K : ℝ := 96*N+1
  have hNleK : N ≤ K := by
    dsimp [K]
    nlinarith
  have hlogcmp : Real.log N ≤ Real.log K :=
    Real.log_le_log (by positivity) hNleK
  have hinv : (97*N)^(-s) ≤ (96*(2^L:ℕ)+1:ℝ)^(-s) := by
    have hKdef : K = (96*(2^L:ℕ)+1:ℝ) := by
      dsimp [K, N]
    rw [← hKdef]
    have hxy : K ≤ 97*N := by dsimp [K]; nlinarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hxy (by linarith)
  have hlogpow : (Real.log N)^a ≤
      (Real.log K)^a := Real.rpow_le_rpow hlog hlogcmp ha
  have hrateLower :
      (97*N)^(-s)*(Real.log N)^a ≤ rate s a (96*2^L+1) := by
    unfold rate
    have hlogpow' : (Real.log N)^a ≤
        (Real.log (96*(2^L:ℝ)+1))^a := by
      simpa [K, N, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using hlogpow
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using
      mul_le_mul hinv hlogpow' (Real.rpow_nonneg hlog _) (by positivity)
  have hpair := le_trans (hEntropy (96*2^L+1) hk) hCover
  have hNpow : (4:ℝ)^L = N^2 := by
    have h := four_pow_eq_two_pow_sq L
    simpa [N, Nat.cast_pow] using h
  have hnonneg : 0 ≤ 4*B/N^2 := by positivity
  have hpairReal : c*rate s a (96*2^L+1) ≤ 4*B/N^2 := by
    have hpair' : ENNReal.ofReal (c*rate s a (96*2^L+1)) ≤
        ENNReal.ofReal (4*B/N^2) := by simpa [hNpow] using hpair
    have hleft0 : 0 ≤ c*rate s a (96*2^L+1) := by
      exact mul_nonneg hc.le (rate_nonneg (by omega))
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hpair'
  have hmulLower : c*((97*N)^(-s)*(Real.log N)^a)*N^2 ≤
      c*rate s a (96*2^L+1)*N^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrateLower hc.le)
      (sq_nonneg N)
  have hmulUpper : c*rate s a (96*2^L+1)*N^2 ≤ 4*B := by
    have := mul_le_mul_of_nonneg_right hpairReal (sq_nonneg N)
    have hNne' : N ≠ 0 := ne_of_gt hNpos
    field_simp [hNne'] at this
    nlinarith [this]
  have hmul' : c*((97*N)^(-s)*(Real.log N)^a)*N^2 ≤ 4*B :=
    le_trans hmulLower hmulUpper
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hfinal : (c/4)*N^2*((97*N)^(-s))*(Real.log N)^a ≤ B := by
    nlinarith [hmul']
  simpa [N] using hfinal

/-- General-power scalar extraction from a local-depth entropy cover. `D` is
the center-exponent multiplier and `Krad` is the cover-radius multiplier. -/
theorem dyadic_budget_lower_of_entropy_lower_A
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (A D : ℕ) (hD : 1 ≤ D)
    {L : ℕ} (hL : 1 ≤ L) (c B Krad : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hKrad : 0 < Krad)
    (hEntropy : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c*rate s a k) ≤ HaarQuarter.TheoremD.entropyNumber k S)
    (hCover : HaarQuarter.TheoremD.entropyNumber (D*2^L+1) S ≤
      ENNReal.ofReal (B*Krad/((2:ℝ)^(A*L)))) :
    c/Krad * (2^L:ℝ)^A * (((D+1)*(2^L:ℝ))^(-s)) *
      (Real.log (2^L:ℝ))^a ≤ B := by
  let N : ℝ := (2^L:ℕ)
  have hN2 : 2 ≤ 2^L := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^L := Nat.pow_le_pow_right (by omega : 1≤2) hL
  have hN2R : 2 ≤ N := by dsimp [N]; exact_mod_cast hN2
  have hNpos : 0 < N := by linarith
  have hk : 2 ≤ D*2^L+1 := by
    have hmul : 1*2^L ≤ D*2^L := Nat.mul_le_mul_right (2^L) hD
    have hmul' : 2^L ≤ D*2^L := by simpa using hmul
    omega
  have hkR : 0 < (D*2^L+1:ℕ) := by omega
  have hidx : (D*2^L+1:ℝ) ≤ ((D+1:ℕ):ℝ)*N := by
    dsimp [N]
    have hNone : (1:ℝ) ≤ (2^L:ℝ) := by exact_mod_cast (show 1≤2^L by omega)
    have hDreal : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    push_cast
    nlinarith
  have hidxpos : 0 < ((D+1:ℕ):ℝ)*N := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogcmp : Real.log N ≤ Real.log ((D*2^L+1:ℕ):ℝ) :=
    Real.log_le_log (by positivity) (by
      have hle : N ≤ ((D*2^L+1:ℕ):ℝ) := by
        have hD' : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
        have hN : 2 ≤ N := hN2R
        have hpowR : 0 ≤ (2^L:ℝ) := by positivity
        have hmul : (1:ℝ)*(2^L:ℝ) ≤ (D:ℝ)*(2^L:ℝ) :=
          mul_le_mul_of_nonneg_right hD' hpowR
        have hmul' : (2^L:ℝ) ≤ (D:ℝ)*(2^L:ℝ) := by simpa using hmul
        have hleR : (2^L:ℝ) ≤ (D:ℝ)*(2^L:ℝ)+1 := by linarith
        simpa [N, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using hleR
      exact hle)
  have hinv : (((D+1:ℕ):ℝ)*N)^(-s) ≤ (D*2^L+1:ℝ)^(-s) := by
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hidx (by linarith)
  have hlogpow : (Real.log N)^a ≤ (Real.log ((D*2^L+1:ℕ):ℝ))^a :=
    Real.rpow_le_rpow hlogN hlogcmp ha
  have hrate : (((D+1:ℕ):ℝ)*N)^(-s)*(Real.log N)^a ≤ rate s a (D*2^L+1) := by
    unfold rate
    have hinv' : (((D+1:ℕ):ℝ)*N)^(-s) ≤ ((D*2^L+1:ℕ):ℝ)^(-s) := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using hinv
    have hlogpow' : (Real.log N)^a ≤
        (Real.log ((D*2^L+1:ℕ):ℝ))^a := by simpa using hlogpow
    exact mul_le_mul hinv' hlogpow' (Real.rpow_nonneg hlogN _) (by positivity)
  have hpair := le_trans (hEntropy (D*2^L+1) hk) hCover
  have hNpow : (2:ℝ)^(A*L) = N^A := by
    dsimp [N]
    norm_cast
    rw [← pow_mul, Nat.mul_comm L A]
  have hpairReal : c*rate s a (D*2^L+1) ≤ B*Krad/N^A := by
    have hright : 0 ≤ B*Krad/N^A := by positivity
    have hleft : 0 ≤ c*rate s a (D*2^L+1) := by
      exact mul_nonneg hc.le (rate_nonneg (by omega))
    have hpair' : ENNReal.ofReal (c*rate s a (D*2^L+1)) ≤
        ENNReal.ofReal (B*Krad/N^A) := by simpa [hNpow] using hpair
    have hreal := (ENNReal.ofReal_le_ofReal_iff hright).mp hpair'
    simpa [hNpow] using hreal
  have hmulLower : c*((((D+1:ℕ):ℝ)*N)^(-s)*(Real.log N)^a) ≤
      c*rate s a (D*2^L+1) := by
    exact mul_le_mul_of_nonneg_left hrate hc.le
  have hmulUpper : c*rate s a (D*2^L+1)*N^A ≤ B*Krad := by
    have h := mul_le_mul_of_nonneg_right hpairReal (by positivity : 0≤N^A)
    have hNpos' : (N:ℝ) ^ A ≠ 0 := pow_ne_zero _ (ne_of_gt hNpos)
    have heq : (B*Krad/N^A)*N^A=B*Krad := by field_simp
    nlinarith [h]
  have hfinal : c/Krad*N^A*((((D+1:ℕ):ℝ)*N)^(-s))*(Real.log N)^a ≤ B := by
    have h := mul_le_mul_of_nonneg_right hmulLower (by positivity : 0≤N^A)
    have hscaled : c*((((D+1:ℕ):ℝ)*N)^(-s)*(Real.log N)^a)*N^A ≤ B*Krad :=
      le_trans h hmulUpper
    have hdiv :
        (c*((((D+1:ℕ):ℝ)*N)^(-s)*(Real.log N)^a)*N^A)/Krad ≤ B :=
      (div_le_iff₀ hKrad).2 hscaled
    calc
      c/Krad*N^A*((((D+1:ℕ):ℝ)*N)^(-s))*(Real.log N)^a =
          (c*((((D+1:ℕ):ℝ)*N)^(-s)*(Real.log N)^a)*N^A)/Krad := by ring
      _ ≤ B := hdiv
  simpa [N] using hfinal

/-- Conditional all-exponent Carl extraction. If the entropy-forced budget
beats the explicit low- and middle-scale contributions, the remaining budget
forces a same-scale lower bound on the target Kolmogorov width. The scalar
margin is kept visible so applications must discharge it rather than silently
assuming a sharp width lower estimate. -/
theorem width_lower_of_entropy_budget_margin
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    {m₀ k L : ℕ} (hm₀ : 2 ≤ m₀) (hm₀k : m₀ ≤ k)
    (hkN : k ≤ 2^L) (hL : 1 ≤ L)
    (R C c : ℝ) (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth S 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ n : ℕ, m₀ ≤ n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth S n ≤
        ENNReal.ofReal (C*rate s a n))
    (hEntropy : ∀ n : ℕ, 2 ≤ n →
      ENNReal.ofReal (c*rate s a n) ≤ HaarQuarter.TheoremD.entropyNumber n S)
    (hmargin : R*(m₀:ℝ)^2 + 4*C*middleScaleWeight s m₀ k*(Real.log (2^L:ℝ))^a ≤
      (c/8)*(2^L:ℝ)^2*(97*(2^L:ℝ))^(-s)*(Real.log (2^L:ℝ))^a) :
    ENNReal.ofReal ((c/8)*(97*(2^L:ℝ))^(-s)*(Real.log (2^L:ℝ))^a) ≤
      HaarQuarter.TheoremD.Width.kolmogorovWidth S k := by
  let N : ℝ := (2^L:ℕ)
  obtain ⟨B,hBform,hBpos,hwidth⟩ := dyadic_width_budget_of_rate_upper
    S ha hm₀ hm₀k hkN hL R C hR hC hzero hupper
  obtain ⟨P, hcoverRaw⟩ := Carl.exists_entropy_cover_of_dyadic_width_bound
    S L B hBpos hwidth
  have hcover : HaarQuarter.TheoremD.entropyNumber (96*2^L+1) S ≤
      ENNReal.ofReal (4*B/(4:ℝ)^L) := by
    calc
      _ ≤ (NNReal.mk (4*B/(4:ℝ)^L) (by positivity) : ENNReal) := hcoverRaw
      _ = ENNReal.ofReal (4*B/(4:ℝ)^L) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        rfl
  have hbudget := dyadic_budget_lower_of_entropy_lower S hs ha hL c B hc hBpos
    hEntropy hcover
  have hbase : R*(m₀:ℝ)^2 + 4*C*middleScaleWeight s m₀ k*(Real.log N)^a ≤
      (c/8)*N^2*(97*N)^(-s)*(Real.log N)^a := by
    simpa [N] using hmargin
  have hwfinite : HaarQuarter.TheoremD.Width.kolmogorovWidth S k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper k hm₀k)
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth S k).toReal
  have hweq : HaarQuarter.TheoremD.Width.kolmogorovWidth S k = ENNReal.ofReal w := by
    dsimp [w]
    exact (ENNReal.ofReal_toReal hwfinite).symm
  have hw0 : 0 ≤ w := by dsimp [w]; exact ENNReal.toReal_nonneg
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hremain : (c/8)*N^2*(97*N)^(-s)*(Real.log N)^a ≤ N^2*w := by
    have hleft := hbudget
    rw [hBform] at hleft
    simp at hleft
    have hbase' := hbase
    simp [N] at hbase'
    simp [N, w]
    nlinarith [hleft, hbase']
  have hwidthReal : (c/8)*(97*N)^(-s)*(Real.log N)^a ≤ w := by
    have hdiv : ((c/8)*N^2*(97*N)^(-s)*(Real.log N)^a)/N^2 ≤ w :=
      (div_le_iff₀ (sq_pos_of_pos hNpos)).2 (by nlinarith [hremain])
    calc
      (c/8)*(97*N)^(-s)*(Real.log N)^a =
          ((c/8)*N^2*(97*N)^(-s)*(Real.log N)^a)/N^2 := by field_simp
      _ ≤ w := hdiv
  have htargetnonneg : 0 ≤ (c/8)*(97*N)^(-s)*(Real.log N)^a := by positivity
  rw [hweq]
  simpa [N] using ENNReal.ofReal_le_ofReal hwidthReal

/-- Local terminal depths decouple dimension growth from the residual accuracy.
This is the arbitrary-rate finite Carl cover interface. `depth j` is the
terminal depth used only to certify the j-th volumetric increment. -/
theorem entropy_cover_of_local_depth_width_approximants
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (L : ℕ) [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : Fin (L+1) → Submodule ℝ X)
    (f : ∀ j, {x : X // x ∈ K} → X)
    (δ : Fin (L+1) → ℝ) (η : Fin L → ℝ) (depth : Fin L → ℕ)
    (hzero : ∀ x, f 0 x = 0)
    (hrank : ∀ j, Module.rank ℝ (V j) ≤ ((2^j.val-1:ℕ):Cardinal))
    (hmem : ∀ j x, f j x ∈ V j)
    (happrox : ∀ (j : Fin (L+1)) (x : {x : X // x ∈ K}),
      ‖(x:X)-f j x‖ ≤ δ j)
    (hfd : ∀ j, FiniteDimensional ℝ (V j))
    (hδ : ∀ j, 0 ≤ δ j) (hη : ∀ j, 0 < η j)
    (hdepth : ∀ j : Fin L, j.val+1 ≤ depth j)
    (hratio : ∀ j : Fin L,
      (δ j.succ + δ j.castSucc)/η j ≤
        10*2^(3*(depth j-(j.val+1))))
    (k : ℕ)
    (hbudget : (∑ j : Fin L, 24*2^(j.val+1)*(depth j-(j.val+1)+1)) ≤ k-1) :
    ∃ P : Fin L → Carl.CoverPiece X,
      (∀ j : Fin L,
        (P j).source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
            (V j.succ ⊔ V j.castSucc) (δ j.succ+δ j.castSucc) ∧
        (P j).radius = NNReal.mk (η j) (hη j).le ∧
        (P j).centers.encard ≤
          ((2^(24*2^(j.val+1)*(depth j-(j.val+1)+1)):ℕ):ℕ∞)) ∧
      HaarQuarter.TheoremD.entropyNumber k K ≤
        Carl.sumRadii ((Carl.zeroBallPiece 0 : Carl.CoverPiece X) ::
          (List.ofFn P ++
            [Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)))])) ∧
      Carl.sumRadii ((Carl.zeroBallPiece 0 : Carl.CoverPiece X) ::
          (List.ofFn P ++
            [Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)))])) ≤
        NNReal.mk ((∑ j : Fin L, η j)+δ (Fin.last L))
          (add_nonneg (Finset.sum_nonneg (fun j _ => (hη j).le)) (hδ (Fin.last L))) := by
  classical
  let P : Fin L → Carl.CoverPiece X := fun j => Classical.choose
    (Carl.exists_sup_increment_piece (V j.succ) (V j.castSucc)
      (L:=depth j) (j:=j.val+1) (R:=δ j.succ+δ j.castSucc) (ε:=η j)
      (hdepth j) (add_nonneg (hδ j.succ) (hδ j.castSucc)) (hη j)
      (by simpa [Nat.add_assoc] using Carl.finrank_consecutive_width_sup_le V hrank hfd j)
      (hratio j))
  have hP (j : Fin L) :
      (P j).source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ+δ j.castSucc) ∧
      (P j).radius = NNReal.mk (η j) (hη j).le ∧
      (P j).centers.encard ≤
        ((2^(24*2^(j.val+1)*(depth j-(j.val+1)+1)):ℕ):ℕ∞) := by
    exact Classical.choose_spec (Carl.exists_sup_increment_piece (V j.succ) (V j.castSucc)
      (L:=depth j) (j:=j.val+1) (R:=δ j.succ+δ j.castSucc) (ε:=η j)
      (hdepth j) (add_nonneg (hδ j.succ) (hδ j.castSucc)) (hη j)
      (by simpa [Nat.add_assoc] using Carl.finrank_consecutive_width_sup_le V hrank hfd j)
      (hratio j))
  let pieces : List (Carl.CoverPiece X) :=
    (Carl.zeroBallPiece 0 : Carl.CoverPiece X) ::
      (List.ofFn P ++ [Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)))])
  let exps : List ℕ := 0 ::
    (List.ofFn (fun j : Fin L => 24*2^(j.val+1)*(depth j-(j.val+1)+1)) ++ [0])
  have hcounts : List.Forall₂
      (fun p e => p.centers.encard ≤ ((2^e:ℕ):ℕ∞)) pieces exps := by
    have hmiddle : List.Forall₂
        (fun p e => p.centers.encard ≤ ((2^e:ℕ):ℕ∞))
        (List.ofFn P)
        (List.ofFn (fun j : Fin L => 24*2^(j.val+1)*(depth j-(j.val+1)+1))) :=
      Carl.forall₂_ofFn _ _ _ (fun j => (hP j).2.2)
    have hfirst : (Carl.zeroBallPiece 0 : Carl.CoverPiece X).centers.encard ≤ ((2^0:ℕ):ℕ∞) := by
      simp [Carl.zeroBallPiece]
    have hlast : (Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L))) :
      Carl.CoverPiece X).centers.encard ≤ ((2^0:ℕ):ℕ∞) := by simp [Carl.zeroBallPiece]
    simp only [pieces, exps]
    exact List.Forall₂.cons hfirst
      (List.rel_append hmiddle (List.Forall₂.cons hlast List.Forall₂.nil))
  have hsrc : pieces.map Carl.CoverPiece.source =
      ({0} :: (List.ofFn (fun j : Fin L =>
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ+δ j.castSucc)) ++
        [Metric.closedBall (0:X) (δ (Fin.last L))])) := by
    have hz : (Carl.zeroBallPiece 0 : Carl.CoverPiece X).source = ({0}:Set X) := by
      ext y
      simp [Carl.zeroBallPiece, Metric.closedBall, dist_eq_norm]
    have ht : (Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L))) :
      Carl.CoverPiece X).source = Metric.closedBall (0:X) (δ (Fin.last L)) := rfl
    simp only [pieces, List.map_cons, List.map_append, List.map_ofFn]
    simp only [hz, ht]
    congr 2
    apply List.ofFn_inj.mpr
    funext j
    exact (hP j).1
  have hselected := Carl.selected_width_approximation_chain K L V f δ hzero hmem happrox
  have hchain : ∀ x ∈ K, ∃ approximants : List X,
      List.Forall₂ (fun z p => z ∈ p.source) (Carl.chainIncrements x approximants) pieces := by
    intro x hx
    refine ⟨List.ofFn (fun j : Fin (L+1) => f j ⟨x,hx⟩), ?_⟩
    apply (List.forall₂_map_right_iff (R:=fun z S => z ∈ S)
      (f:=Carl.CoverPiece.source)).mp
    rw [hsrc]
    exact hselected ⟨x,hx⟩
  have hexp : exps.sum ≤
      (∑ j : Fin L, 24*2^(j.val+1)*(depth j-(j.val+1)+1)) := by
    simp [exps, List.sum_ofFn]
  have hentropy := Carl.entropyNumber_le_of_dyadic_approximation_chain
    K pieces k exps hchain hcounts (by simpa [exps,List.sum_ofFn] using hbudget)
  have hPradius (j : Fin L) : (P j).radius = NNReal.mk (η j) (hη j).le :=
    (hP j).2.1
  have hradReal : (Carl.sumRadii pieces : ℝ) =
      (∑ j : Fin L, η j)+δ (Fin.last L) := by
    rw [Carl.sumRadii_eq_list_sum]
    simp [pieces, List.map_ofFn, List.sum_ofFn, hPradius,
      Carl.zeroBallPiece]
  refine ⟨P, hP, ?_, ?_⟩
  · simpa [pieces] using hentropy
  · apply NNReal.coe_le_coe.mp
    have hrad := hradReal
    simpa [pieces] using hrad.le

/-- Replacing the common terminal depth by a q-times longer local residual
depth costs at most a factor q in the total center exponent. -/
theorem local_depth_exponent_sum_le (q L : ℕ) (hq : 1 ≤ q) :
    (∑ j : Fin L, 24*2^(j.val+1)*
      (q*(L-(j.val+1))+1)) ≤ 96*q*2^L := by
  have hterm (j : Fin L) :
      24*2^(j.val+1)*(q*(L-(j.val+1))+1) ≤
        q*(24*2^(j.val+1)*(L-(j.val+1)+1)) := by
    have hqmul : q*(L-(j.val+1)) + 1 ≤ q*(L-(j.val+1)+1) := by
      calc
        q*(L-(j.val+1)) + 1 ≤ q*(L-(j.val+1)) + q := by omega
        _ = q*(L-(j.val+1)+1) := by ring
    calc
      24*2^(j.val+1)*(q*(L-(j.val+1))+1) ≤
          24*2^(j.val+1)*(q*(L-(j.val+1)+1)) := Nat.mul_le_mul_left _ hqmul
      _ = q*(24*2^(j.val+1)*(L-(j.val+1)+1)) := by ring
  calc
    _ ≤ ∑ j : Fin L, q*(24*2^(j.val+1)*(L-(j.val+1)+1)) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = q * (∑ j : Fin L, 24*2^(j.val+1)*(L-(j.val+1)+1)) := by
      rw [Finset.mul_sum]
    _ ≤ q * (96*2^L) := by
      exact mul_le_mul_of_nonneg_left (Carl.dyadicCarl_increment_exponent_sum_le L)
        (by positivity)
    _ = 96*q*2^L := by ring

/-- Q-dyadic width bounds yield a local-depth entropy cover. The radius is a
constant depending on A times B/Q^L, while the entropy index is O(q·2^L). -/
theorem entropy_cover_of_Q_dyadic_width_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (A q L : ℕ) (hAq : A+1 ≤ 3*q) {B : ℝ} (hB : 0 < B)
    (hwidth : ∀ j : Fin (L+1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2^j.val-1) ≤
        ENNReal.ofReal (B/(2:ℝ)^(A*j.val)))
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] :
    ∃ P : Fin L → Carl.CoverPiece X,
      (∀ j : Fin L, (P j).radius = NNReal.mk (localDepthEta A L B j)
        (localDepthEta_pos hB j).le ∧
        (P j).centers.encard ≤
          ((2^(24*2^(j.val+1)*(q*(L-(j.val+1))+1)):ℕ):ℕ∞)) ∧
      HaarQuarter.TheoremD.entropyNumber (96*q*2^L+1) K ≤
        ENNReal.ofReal (((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L)) := by
  classical
  let δ : Fin (L+1) → ℝ := fun j => 2*B/(2:ℝ)^(A*j.val)
  let η : Fin L → ℝ := localDepthEta A L B
  let depth : Fin L → ℕ := fun j => j.val+1+q*(L-(j.val+1))
  have hδpos : ∀ j, 0 < δ j := by intro j; dsimp [δ]; positivity
  have hwidth' : ∀ j : Fin (L+1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2^j.val-1) < ENNReal.ofReal (δ j) := by
    intro j
    have hreal : B/(2:ℝ)^(A*j.val) < 2*B/(2:ℝ)^(A*j.val) := by
      have hp : 0 < (2:ℝ)^(A*j.val) := by positivity
      exact div_lt_div_of_pos_right (by linarith) hp
    exact lt_of_le_of_lt (hwidth j)
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by simpa [δ] using hreal))
  have hηpos : ∀ j, 0 < η j := by intro j; exact localDepthEta_pos hB j
  have hdepth : ∀ j : Fin L, j.val+1 ≤ depth j := by
    intro j
    dsimp [depth]
    omega
  have hratio : ∀ j : Fin L,
      (δ j.succ+δ j.castSucc)/η j ≤ 10*2^(3*(depth j-(j.val+1))) := by
    intro j
    have hratio' := local_depth_ratio_of_Q_budget hAq hB
      (δ:=δ) (by intro i; dsimp [δ]; exact le_rfl) j
    simpa [η, depth, Nat.mul_assoc] using hratio'
  obtain ⟨V,hV,hfd,hdata⟩ := Carl.exists_selected_width_chain K L δ hδpos hwidth'
  rcases hdata with ⟨f,hzero,happ,_⟩
  have hmem : ∀ (j : Fin (L+1)) (x : {x : X // x ∈ K}), f j x ∈ V j :=
    fun j x => (happ j x).1
  have happrox : ∀ (j : Fin (L+1)) (x : {x : X // x ∈ K}),
      ‖(x:X)-f j x‖ ≤ δ j := fun j x => (happ j x).2
  have hδnonneg : ∀ j, 0 ≤ δ j := fun j => (hδpos j).le
  have hbudget :
      (∑ j : Fin L, 24*2^(j.val+1)*(depth j-(j.val+1)+1)) ≤ 96*q*2^L := by
    have hsum : (∑ j : Fin L, 24*2^(j.val+1)*(depth j-(j.val+1)+1)) =
        ∑ j : Fin L, 24*2^(j.val+1)*(q*(L-(j.val+1))+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [depth]
      
    rw [hsum]
    exact local_depth_exponent_sum_le q L (by omega)
  obtain ⟨P,hP,hcover,hcoverRad⟩ := entropy_cover_of_local_depth_width_approximants
    K L V f δ η depth hzero hV hmem happrox hfd hδnonneg hηpos hdepth hratio
    (96*q*2^L+1) (by omega)
  have hEtaSum := localDepthEta_sum_le A L (le_of_lt hB)
  have hlast : δ (Fin.last L) = 2*B/(2:ℝ)^(A*L) := by
    simp [δ, Fin.last]
  have htotal : (∑ j : Fin L, η j)+δ (Fin.last L) ≤
      ((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L) := by
    rw [hlast]
    have hsum : (∑ j : Fin L, η j) ≤ (2:ℝ)^(A+1)*B/(2:ℝ)^(A*L) := by
      simpa [η] using hEtaSum
    calc
      (∑ j : Fin L, η j)+2*B/(2:ℝ)^(A*L) ≤
          (2:ℝ)^(A+1)*B/(2:ℝ)^(A*L)+2*B/(2:ℝ)^(A*L) :=
            add_le_add hsum le_rfl
      _ = ((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L) := by ring
  have hrad : Carl.sumRadii
      ((Carl.zeroBallPiece 0 : Carl.CoverPiece X) ::
        (List.ofFn P ++ [Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδnonneg _))])) ≤
      NNReal.mk (((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L)) (by positivity) := by
    exact le_trans hcoverRad (by
      apply NNReal.coe_le_coe.mp
      have hradReal : (↑(NNReal.mk ((∑ j : Fin L, η j)+δ (Fin.last L))
          (add_nonneg (Finset.sum_nonneg (fun j _ => (hηpos j).le)) (hδnonneg _))):ℝ) =
            (∑ j : Fin L, η j)+δ (Fin.last L) := rfl
      simpa using htotal)
  refine ⟨P, ?_, ?_⟩
  · intro j
    refine ⟨(hP j).2.1, ?_⟩
    simpa [depth] using (hP j).2.2
  · calc
      _ ≤ (Carl.sumRadii
          ((Carl.zeroBallPiece 0 : Carl.CoverPiece X) ::
            (List.ofFn P ++ [Carl.zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδnonneg _))])) : ENNReal) := hcover
      _ ≤ (NNReal.mk (((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L)) (by positivity) : ENNReal) := by exact_mod_cast hrad
      _ = ENNReal.ofReal (((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L)) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        rfl

/-- General-power conditional extraction. Since A>s, the width upper budget
has a growing middle-scale term; taking N sufficiently larger than m can make
the explicit margin true and leave the target-width contribution. -/
theorem width_lower_of_entropy_budget_margin_A
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (A q : ℕ) (hsA : s < A) (hAq : A+1 ≤ 3*q)
    {m₀ m L : ℕ} (hm₀ : 2 ≤ m₀) (hm₀m : m₀ ≤ m)
    (hmN : m ≤ 2^L) (hL : 1 ≤ L)
    (R C c : ℝ) (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth S 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ n : ℕ, m₀ ≤ n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth S n ≤ ENNReal.ofReal (C*rate s a n))
    (hEntropy : ∀ n : ℕ, 2 ≤ n →
      ENNReal.ofReal (c*rate s a n) ≤ HaarQuarter.TheoremD.entropyNumber n S)
    (hmargin : R*(m₀:ℝ)^A+(2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log (2^L:ℝ))^a ≤
      (c/(2*((2:ℝ)^(A+1)+2)))*(2^L:ℝ)^A*
        (((96*q+1:ℝ)*(2^L:ℝ))^(-s))*(Real.log (2^L:ℝ))^a) :
    ENNReal.ofReal ((c/(2*((2:ℝ)^(A+1)+2)))*
        (((96*q+1:ℝ)*(2^L:ℝ))^(-s))*(Real.log (2^L:ℝ))^a) ≤
      HaarQuarter.TheoremD.Width.kolmogorovWidth S m := by
  let N : ℝ := (2^L:ℕ)
  let Krad : ℝ := (2:ℝ)^(A+1)+2
  let D : ℕ := 96*q
  obtain ⟨B,hBform,hBpos,hwidth⟩ := dyadic_width_budget_of_rate_upper_A
    S ha A hsA hm₀ hm₀m hmN hL R C hR hC hzero hupper
  obtain ⟨P,hpieces,hcoverRaw⟩ := entropy_cover_of_Q_dyadic_width_bound
    S A q L hAq hBpos hwidth
  have hcover : HaarQuarter.TheoremD.entropyNumber (D*2^L+1) S ≤
      ENNReal.ofReal (B*Krad/(2:ℝ)^(A*L)) := by
    simpa [D,Krad, mul_comm, mul_left_comm, mul_assoc] using hcoverRaw
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hbudget := dyadic_budget_lower_of_entropy_lower_A S hs ha A D hD hL
    c B Krad hc hBpos (by dsimp [Krad]; positivity) hEntropy hcover
  have hmargin' : R*(m₀:ℝ)^A+(2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log N)^a ≤
      (c/(2*Krad))*N^A*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a := by
    simpa [N,Krad,D] using hmargin
  have hwfinite : HaarQuarter.TheoremD.Width.kolmogorovWidth S m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper m hm₀m)
  let w : ℝ := (HaarQuarter.TheoremD.Width.kolmogorovWidth S m).toReal
  have hweq : HaarQuarter.TheoremD.Width.kolmogorovWidth S m = ENNReal.ofReal w := by
    dsimp [w]
    exact (ENNReal.ofReal_toReal hwfinite).symm
  have hw0 : 0 ≤ w := by dsimp [w]; exact ENNReal.toReal_nonneg
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hremain : (c/(2*Krad))*N^A*
      (((D+1:ℝ)*N)^(-s))*(Real.log N)^a ≤ N^A*w := by
    have hleft := hbudget
    rw [hBform] at hleft
    have hbase' := hmargin'
    simp [N,w] at hleft hbase' ⊢
    dsimp [Krad] at hbase'
    have hcoef : c/Krad = 2*(c/(2*Krad)) := by field_simp
    rw [hcoef] at hleft
    nlinarith [hleft,hbase']
  have hwidthReal : (c/(2*Krad))*
      (((D+1:ℝ)*N)^(-s))*(Real.log N)^a ≤ w := by
    have hdiv : ((c/(2*Krad))*N^A*
        (((D+1:ℝ)*N)^(-s))*(Real.log N)^a)/N^A ≤ w :=
      (div_le_iff₀ (by positivity : 0<N^A)).2 (by nlinarith [hremain])
    calc
      _ = ((c/(2*Krad))*N^A*
          (((D+1:ℝ)*N)^(-s))*(Real.log N)^a)/N^A := by field_simp
      _ ≤ w := hdiv
  rw [hweq]
  have hnonneg : 0 ≤ (c/(2*Krad))*
      (((D+1:ℝ)*N)^(-s))*(Real.log N)^a := by positivity
  simpa [N,Krad,D] using ENNReal.ofReal_le_ofReal hwidthReal

private theorem carlDyadicFactor_eq {A D L : ℕ} {s : ℝ} :
    (2^L:ℝ)^A * (((D+1:ℝ)*(2^L:ℝ))^(-s)) =
      ((D+1:ℝ)^(-s))*((2:ℝ)^((A:ℝ)-s))^L := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hD : (0:ℝ) < (D+1:ℝ) := by positivity
  have hN : (0:ℝ) < (2:ℝ)^L := by positivity
  have hpow : (2^L:ℝ)^A * (2^L:ℝ)^(-s) = (2^L:ℝ)^((A:ℝ)-s) := by
    rw [← Real.rpow_natCast (2^L:ℝ) A, ← Real.rpow_add hN]
    congr 1
  calc
    (2^L:ℝ)^A * (((D+1:ℝ)*(2^L:ℝ))^(-s)) =
        (2^L:ℝ)^A * ((D+1:ℝ)^(-s) * (2^L:ℝ)^(-s)) := by
          rw [Real.mul_rpow hD.le hN.le]
    _ = (D+1:ℝ)^(-s) * ((2^L:ℝ)^A * (2^L:ℝ)^(-s)) := by ring
    _ = (D+1:ℝ)^(-s) * (2^L:ℝ)^((A:ℝ)-s) := by rw [hpow]
    _ = (D+1:ℝ)^(-s) * ((2:ℝ)^((A:ℝ)-s))^L := by
      congr 1
      calc
        (2^L:ℝ)^((A:ℝ)-s) =
            (2:ℝ)^(((L:ℝ))*((A:ℝ)-s)) := by
          rw [← Real.rpow_natCast (2:ℝ) L, ← Real.rpow_mul h2.le]
        _ = (2:ℝ)^(((A:ℝ)-s)*(L:ℝ)) := by congr 1 <;> ring
        _ = ((2:ℝ)^((A:ℝ)-s))^L := by
          rw [← Real.rpow_natCast ((2:ℝ)^((A:ℝ)-s)) L]
          exact Real.rpow_mul h2.le _ _

private theorem dyadic_log2_bracket (m J : ℕ) (hm : 1 ≤ m) :
    m ≤ 2^(m.log2+J+1) ∧ 2^J*m ≤ 2^(m.log2+J+1) ∧
      2^(m.log2+J+1) ≤ 2^(J+1)*m := by
  have hm0 : m ≠ 0 := by omega
  have hlow := Nat.log2_self_le hm0
  have hhigh := Nat.lt_log2_self (n := m)
  have hmul : m*2^J < 2^(m.log2+1)*2^J :=
    (Nat.mul_lt_mul_right (by positivity : 0 < 2^J)).2 hhigh
  have heq : 2^(m.log2+1)*2^J = 2^(m.log2+J+1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmul' : 2^J*m < 2^(m.log2+J+1) := by
    have hn : m*2^J < 2^(m.log2+J+1) := by simpa [heq] using hmul
    simpa [Nat.mul_comm] using hn
  constructor
  · have hmulAtLeast : m ≤ m*2^J := by
      have hone : 1 ≤ 2^J := Nat.one_le_pow J 2 (by omega)
      simpa using Nat.mul_le_mul_left m hone
    exact hmulAtLeast.trans (le_of_lt (by simpa [Nat.mul_comm] using hmul'))
  · refine ⟨le_of_lt hmul', ?_⟩
    calc
      2^(m.log2+J+1) = 2^(m.log2+(J+1)) := by congr 1 <;> omega
      _ = 2^m.log2*2^(J+1) := by rw [pow_add]
      _ ≤ m*2^(J+1) := Nat.mul_le_mul_right _ hlow
      _ = 2^(J+1)*m := Nat.mul_comm _ _

private theorem dyadic_rpow_mul {J : ℕ} {β : ℝ} :
    ((2:ℝ)^J)^β = ((2:ℝ)^β)^J := by
  have h2 : (0:ℝ) < 2 := by norm_num
  calc
    ((2:ℝ)^J)^β = (2:ℝ)^((J:ℝ)*β) := by
      rw [← Real.rpow_natCast (2:ℝ) J, ← Real.rpow_mul h2.le]
    _ = (2:ℝ)^(β*(J:ℝ)) := by congr 1 <;> push_cast <;> ring
    _ = ((2:ℝ)^β)^J := by
      rw [← Real.rpow_natCast ((2:ℝ)^β) J]
      exact Real.rpow_mul h2.le _ _

/-- The scalar remainder margin is eventually available whenever the budget
power A strictly exceeds the entropy exponent s. -/
theorem eventually_carl_budget_margin
    {s a R C c : ℝ} {A q m₀ : ℕ} (hs : 0 < s) (ha : 0 ≤ a)
    (hsA : s < A) (hAq : A+1 ≤ 3*q) (hm₀ : 2 ≤ m₀)
    (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      R*(m₀:ℝ)^A + (2:ℝ)^A*C*scaleWeightA A s m₀ m₀ *
          (Real.log (2^L:ℝ))^a ≤
        (c/(2*((2:ℝ)^(A+1)+2)))*(2^L:ℝ)^A*
          (((96*q+1:ℝ)*(2^L:ℝ))^(-s))*(Real.log (2^L:ℝ))^a := by
  let D : ℕ := 96*q
  let Krad : ℝ := (2:ℝ)^(A+1)+2
  let wt : ℝ := scaleWeightA A s m₀ m₀
  let base : ℝ := R*(m₀:ℝ)^A+(2:ℝ)^A*C*wt
  let b : ℝ := (2:ℝ)^((A:ℝ)-s)
  let kpow : ℝ := ((D+1:ℝ)^(-s))
  let coeff : ℝ := c/(2*Krad)
  have hApos : 0 < (A:ℝ) := by linarith
  have hKrad : 0 < Krad := by dsimp [Krad]; positivity
  have hcoeff : 0 < coeff := by dsimp [coeff]; positivity
  have hwt : 0 < wt := by
    dsimp [wt, scaleWeightA]
    split_ifs <;> positivity
  have hbase : 0 ≤ base := by
    dsimp [base]
    positivity
  have hb : 1 < b := by
    dsimp [b]
    apply Real.one_lt_rpow (by norm_num)
    linarith
  have hkpow : 0 < kpow := by
    dsimp [kpow]
    positivity
  have hbTendsto : Filter.Tendsto (fun L : ℕ => b^L) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hfactorTendsto : Filter.Tendsto
      (fun L : ℕ => (2^L:ℝ)^A*(((D+1:ℝ)*(2^L:ℝ))^(-s)))
      Filter.atTop Filter.atTop := by
    have hconst := hbTendsto.atTop_mul_const hkpow
    have heq : (fun L : ℕ => (2^L:ℝ)^A*(((D+1:ℝ)*(2^L:ℝ))^(-s))) =
        (fun L : ℕ => b^L*kpow) := by
      funext L
      dsimp [b,kpow]
      rw [carlDyadicFactor_eq]
      ring
    rw [heq]
    exact hconst
  have hpowTendsto : Filter.Tendsto (fun L : ℕ => (2:ℝ)^L)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlogTendsto : Filter.Tendsto
      (fun L : ℕ => Real.log ((2:ℝ)^L)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hpowTendsto
  have hlogEv : ∀ᶠ L : ℕ in Filter.atTop, 1 ≤ Real.log ((2:ℝ)^L) :=
    hlogTendsto.eventually_ge_atTop 1
  have hfactorEv : ∀ᶠ L : ℕ in Filter.atTop,
      base/coeff ≤ (2^L:ℝ)^A*(((D+1:ℝ)*(2^L:ℝ))^(-s)) :=
    hfactorTendsto.eventually_ge_atTop (base/coeff)
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.1 (hlogEv.and hfactorEv)
  refine ⟨L₀, ?_⟩
  intro L hL
  obtain ⟨hlog,hfactor⟩ := hL₀ L hL
  have hlogpow : 1 ≤ (Real.log ((2:ℝ)^L))^a := by
    calc
      1 = (1:ℝ)^a := by simp
      _ ≤ (Real.log ((2:ℝ)^L))^a :=
        Real.rpow_le_rpow (by norm_num) hlog ha
  have hRpart : R*(m₀:ℝ)^A ≤ R*(m₀:ℝ)^A*(Real.log ((2:ℝ)^L))^a := by
    have hRnonneg : 0 ≤ R*(m₀:ℝ)^A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogpow hRnonneg]
  have hleft : R*(m₀:ℝ)^A+(2:ℝ)^A*C*wt*(Real.log ((2:ℝ)^L))^a ≤
      base*(Real.log ((2:ℝ)^L))^a := by
    dsimp [base]
    nlinarith [hRpart]
  have hbaseFactor : base ≤ coeff*((2^L:ℝ)^A*
      (((D+1:ℝ)*(2^L:ℝ))^(-s))) :=
    by
      have h := (div_le_iff₀ hcoeff).1 hfactor
      nlinarith [h]
  have hright : base*(Real.log ((2:ℝ)^L))^a ≤
      coeff*((2^L:ℝ)^A*(((D+1:ℝ)*(2^L:ℝ))^(-s)))*
        (Real.log ((2:ℝ)^L))^a :=
    mul_le_mul_of_nonneg_right hbaseFactor (by positivity)
  have htotal := hleft.trans hright
  simpa [D,Krad,coeff,wt, mul_assoc] using htotal

/-- Uniform-in-m Carl margin with a dyadic level chosen at a fixed offset from
`log₂ m`. The offset pays for the middle-scale constant, while the low-scale
term is absorbed for all sufficiently large m. -/
theorem exists_uniform_carl_budget_margin_offset
    {s a R C c : ℝ} {A q m₀ : ℕ}
    (hs : 0 < s) (ha : 0 ≤ a) (hsA : s < A)
    (hAq : A+1 ≤ 3*q) (hm₀ : 2 ≤ m₀)
    (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c) :
    ∃ J M : ℕ, m₀ ≤ M ∧ ∀ m : ℕ, M ≤ m →
      let L := m.log2+J+1
      R*(m₀:ℝ)^A+(2:ℝ)^A*C*scaleWeightA A s m₀ m*(Real.log (2^L:ℝ))^a ≤
        (c/(2*((2:ℝ)^(A+1)+2)))*(2^L:ℝ)^A*
          (((96*q+1:ℝ)*(2^L:ℝ))^(-s))*(Real.log (2^L:ℝ))^a := by
  let D : ℕ := 96*q
  let Krad : ℝ := (2:ℝ)^(A+1)+2
  let kpow : ℝ := ((D+1:ℝ)^(-s))
  let β : ℝ := (A:ℝ)-s
  let b : ℝ := (2:ℝ)^β
  let g : ℝ := (c/(4*Krad))*kpow
  let mid : ℝ := (2:ℝ)^A*C
  have hβ : 0 < β := by dsimp [β]; exact sub_pos.mpr hsA
  have hKrad : 0 < Krad := by dsimp [Krad]; positivity
  have hkpow : 0 < kpow := by dsimp [kpow]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hbase : 0 ≤ R*(m₀:ℝ)^A := by positivity
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hβ
  have hbpow : Filter.Tendsto (fun n : ℕ => b^n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hJEv : ∀ᶠ j : ℕ in Filter.atTop, mid/g ≤ b^j :=
    hbpow.eventually_ge_atTop (mid/g)
  obtain ⟨J,hJ⟩ := Filter.eventually_atTop.1 hJEv
  have hJineq : mid ≤ g*b^J := by
    have h := hJ J le_rfl
    simpa [mul_comm] using (div_le_iff₀ hg).1 h
  have hmPowTendsto : Filter.Tendsto (fun n : ℕ => (n:ℝ)^β)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  have hMpowEv : ∀ᶠ m : ℕ in Filter.atTop,
      R*(m₀:ℝ)^A/g ≤ (m:ℝ)^β :=
    hmPowTendsto.eventually_ge_atTop (R*(m₀:ℝ)^A/g)
  have hlogTendsto : Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hMlogEv : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ Real.log (m:ℝ) :=
    hlogTendsto.eventually_ge_atTop 1
  obtain ⟨Mpow,hMpow⟩ := Filter.eventually_atTop.1 hMpowEv
  obtain ⟨Mlog,hMlog⟩ := Filter.eventually_atTop.1 hMlogEv
  let M : ℕ := max m₀ (max Mpow (max Mlog 2))
  refine ⟨J,M,?_,?_⟩
  · dsimp [M]
    omega
  intro m hm
  dsimp [M] at hm
  have hm₀m : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hmPow : R*(m₀:ℝ)^A/g ≤ (m:ℝ)^β := hMpow m (by omega)
  have hmLog : 1 ≤ Real.log (m:ℝ) := hMlog m (by omega)
  let L : ℕ := m.log2+J+1
  have hbracket := dyadic_log2_bracket m J (by omega)
  have hmN : m ≤ 2^L := by simpa [L] using hbracket.1
  have hscaledN : 2^J*m ≤ 2^L := by simpa [L] using hbracket.2.1
  have hNupper : 2^L ≤ 2^(J+1)*m := by simpa [L] using hbracket.2.2
  let N : ℝ := (2:ℝ)^L
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNlowerR : (2:ℝ)^J*(m:ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hscaledN
  have hNupperR : N ≤ (2:ℝ)^(J+1)*(m:ℝ) := by
    dsimp [N]
    exact_mod_cast hNupper
  have hNgeM : (m:ℝ) ≤ N := by
    have hmN' : (m:ℝ) ≤ (2:ℝ)^L := by exact_mod_cast hmN
    simpa [N] using hmN'
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogN : 1 ≤ Real.log N := by
    have hlogmono : Real.log (m:ℝ) ≤ Real.log N :=
      Real.log_le_log hmpos hNgeM
    dsimp [N] at hlogmono ⊢
    exact hmLog.trans hlogmono
  have hlogpow : 1 ≤ (Real.log N)^a := by
    calc
      1 = (1:ℝ)^a := by simp
      _ ≤ (Real.log N)^a := Real.rpow_le_rpow (by norm_num) hlogN ha
  have hNβ : b^J*(m:ℝ)^β ≤ N^β := by
    have hmul : ((2:ℝ)^J*(m:ℝ))^β = b^J*(m:ℝ)^β := by
      rw [Real.mul_rpow (by positivity) (by positivity), dyadic_rpow_mul]
    rw [← hmul]
    have hleftpos : 0 < (2:ℝ)^J*(m:ℝ) := mul_pos (by positivity) hmpos
    exact Real.rpow_le_rpow hleftpos.le hNlowerR hβ.le
  have hfactor : N^A*(((D+1:ℝ)*N)^(-s)) = kpow*N^β := by
    dsimp [N,kpow]
    rw [carlDyadicFactor_eq (A:=A) (D:=D) (L:=L) (s:=s)]
    dsimp [β]
    rw [dyadic_rpow_mul (J:=L) (β:=(A:ℝ)-s)]
  have hlow : R*(m₀:ℝ)^A ≤ g*N^β := by
    have hlowm : R*(m₀:ℝ)^A ≤ g*(m:ℝ)^β :=
      by simpa [mul_comm] using (div_le_iff₀ hg).1 hmPow
    have hmono : (m:ℝ)^β ≤ N^β :=
      Real.rpow_le_rpow hmpos.le hNgeM hβ.le
    exact hlowm.trans (mul_le_mul_of_nonneg_left hmono hg.le)
  have hmid : mid*(m:ℝ)^β ≤ g*N^β := by
    calc
      mid*(m:ℝ)^β ≤ (g*b^J)*(m:ℝ)^β :=
        mul_le_mul_of_nonneg_right hJineq (by positivity)
      _ = g*(b^J*(m:ℝ)^β) := by ring
      _ ≤ g*N^β := mul_le_mul_of_nonneg_left hNβ hg.le
  have hweight : scaleWeightA A s m₀ m = (m:ℝ)^β := by
    simp [scaleWeightA, β, le_of_lt hsA]
  have hbaseLog : R*(m₀:ℝ)^A ≤ g*N^β*(Real.log N)^a := by
    have hnonneg : 0 ≤ g*N^β := by positivity
    exact hlow.trans (le_trans (by nlinarith [hlogpow, hnonneg]) le_rfl)
  have hmidLog : mid*scaleWeightA A s m₀ m*(Real.log N)^a ≤
      g*N^β*(Real.log N)^a := by
    rw [hweight]
    exact mul_le_mul_of_nonneg_right hmid (by positivity)
  have hsum : R*(m₀:ℝ)^A+mid*scaleWeightA A s m₀ m*(Real.log N)^a ≤
      (2*g)*N^β*(Real.log N)^a := by
    calc
      _ ≤ g*N^β*(Real.log N)^a+g*N^β*(Real.log N)^a := add_le_add hbaseLog hmidLog
      _ = (2*g)*N^β*(Real.log N)^a := by ring
  have hright : (2*g)*N^β*(Real.log N)^a =
      (c/(2*Krad))*N^A*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a := by
    calc
      (2*g)*N^β*(Real.log N)^a =
          (c/(2*Krad))*(kpow*N^β)*(Real.log N)^a := by
            dsimp [g]
            ring
      _ = (c/(2*Krad))*N^A*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a := by
            rw [← hfactor]
            ring
  simpa [D,Krad,mid,N,L] using hsum.trans_eq hright

/-- A sharp same-order Carl lower bound from matching polynomial-log entropy
and width upper bounds, for every positive entropy exponent. The fixed dyadic
offset absorbs the middle-scale budget; no restriction `s < 2` is used. -/
theorem eventually_width_lower_of_entropy_rate_upper_A
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) {s a R C c : ℝ} {A q m₀ : ℕ}
    (hs : 0 < s) (ha : 0 ≤ a) (hsA : s < A)
    (hAq : A+1 ≤ 3*q) (hm₀ : 2 ≤ m₀)
    (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth S 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ n : ℕ, m₀ ≤ n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth S n ≤ ENNReal.ofReal (C*rate s a n))
    (hEntropy : ∀ n : ℕ, 2 ≤ n →
      ENNReal.ofReal (c*rate s a n) ≤ HaarQuarter.TheoremD.entropyNumber n S) :
    ∃ c' : ℝ, ∃ M : ℕ, 0 < c' ∧ ∀ m : ℕ, M ≤ m →
      ENNReal.ofReal (c'*rate s a m) ≤
        HaarQuarter.TheoremD.Width.kolmogorovWidth S m := by
  obtain ⟨J,M,hM₀M,hoffset⟩ := exists_uniform_carl_budget_margin_offset
    hs ha hsA hAq hm₀ hR hC hc
  let D : ℕ := 96*q
  let Krad : ℝ := (2:ℝ)^(A+1)+2
  let K : ℝ := (D+1:ℝ)*(2:ℝ)^(J+1)
  let c' : ℝ := (c/(2*Krad))*K^(-s)
  have hKrad : 0 < Krad := by dsimp [Krad]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hc' : 0 < c' := by dsimp [c']; positivity
  refine ⟨c',M,hc',?_⟩
  intro m hm
  have hm₀m : m₀ ≤ m := hM₀M.trans hm
  let L : ℕ := m.log2+J+1
  have hbracket := dyadic_log2_bracket m J (by omega)
  have hmN : m ≤ 2^L := by simpa [L] using hbracket.1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hmargin := hoffset m hm
  have hwidth := width_lower_of_entropy_budget_margin_A S hs ha A q
    hsA hAq hm₀ hm₀m hmN hL R C c hR hC hc hzero hupper hEntropy
    (by simpa [L] using hmargin)
  let N : ℝ := (2:ℝ)^L
  have hNgeM : (m:ℝ) ≤ N := by
    have hmN' : (m:ℝ) ≤ 2^L := by exact_mod_cast hmN
    simpa [N] using hmN'
  have hNupperR : N ≤ (2:ℝ)^(J+1)*(m:ℝ) := by
    have hnat := hbracket.2.2
    have hcast : ((2^L:ℕ):ℝ) ≤ (2:ℝ)^(J+1)*(m:ℝ) := by exact_mod_cast hnat
    simpa [N] using hcast
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hlogmono : Real.log (m:ℝ) ≤ Real.log N := Real.log_le_log hmpos hNgeM
  have hlogpower : (Real.log (m:ℝ))^a ≤ (Real.log N)^a :=
    Real.rpow_le_rpow hlogm hlogmono ha
  have hlogNpos : 0 < Real.log N := Real.log_pos (by
    have : 1 < (m:ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith)
  have hlogpower_nonneg : 0 ≤ (Real.log N)^a := (Real.rpow_pos_of_pos hlogNpos a).le
  have hbase : ((D+1:ℝ)*N) ≤ K*(m:ℝ) := by
    calc
      ((D+1:ℝ)*N) ≤ (D+1:ℝ)*((2:ℝ)^(J+1)*(m:ℝ)) :=
        mul_le_mul_of_nonneg_left hNupperR (by positivity)
      _ = K*(m:ℝ) := by dsimp [K]; ring
  have hbasepos : 0 < ((D+1:ℝ)*N) := by positivity
  have hKmpost : 0 < K*(m:ℝ) := mul_pos hK hmpos
  have hnegpow : (K*(m:ℝ))^(-s) ≤ (((D+1:ℝ)*N)^(-s)) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hbase (neg_nonpos.mpr hs.le)
  have hfactor : (K*(m:ℝ))^(-s) = K^(-s)*(m:ℝ)^(-s) := by
    rw [Real.mul_rpow hK.le hmpos.le]
  have hrate : c'*rate s a m ≤
      (c/(2*Krad))*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a := by
    have hcoef : 0 ≤ c/(2*Krad) := by positivity
    calc
      c'*rate s a m = (c/(2*Krad))*(K*(m:ℝ))^(-s)*(Real.log (m:ℝ))^a := by
        dsimp [c',rate]
        calc
          _ = (c/(2*Krad))*(K^(-s)*(m:ℝ)^(-s))*(Real.log (m:ℝ))^a := by ring
          _ = (c/(2*Krad))*(K*(m:ℝ))^(-s)*(Real.log (m:ℝ))^a := by
            rw [← hfactor]
      _ ≤ (c/(2*Krad))*(((D+1:ℝ)*N)^(-s))*(Real.log (m:ℝ))^a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnegpow hcoef) (by positivity)
      _ ≤ (c/(2*Krad))*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a :=
        mul_le_mul_of_nonneg_left hlogpower (by positivity)
  have hwidth' : ENNReal.ofReal (c'*rate s a m) ≤
      ENNReal.ofReal ((c/(2*Krad))*(((D+1:ℝ)*N)^(-s))*(Real.log N)^a) :=
    ENNReal.ofReal_le_ofReal hrate
  exact hwidth'.trans (by simpa [N,Krad,D] using hwidth)

end

end BrownianSharp.AlignmentPeriodicWidth
