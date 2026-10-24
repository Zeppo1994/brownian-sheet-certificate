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

private theorem KdUnitCube_isCompact (d : ℕ) :
    IsCompact (CameronMartin.KdUnitCube d) := by
  rw [CameronMartin.KdUnitCube_eq_Kd d]
  exact CameronMartin.Kd_isCompact d

private theorem KdUnitCube_widthReal_zero_le_one (d : ℕ) :
    HaarQuarter.TheoremD.Width.kolmogorovWidthReal
      (CameronMartin.KdUnitCube d) 0 ≤ 1 := by
  let K := CameronMartin.KdUnitCube d
  have hK := KdUnitCube_isCompact d
  have herror : HaarQuarter.TheoremD.Width.approximationError K ⊥ ≤ ENNReal.ofReal 1 := by
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
        Metric.infEDist_le_edist_of_mem
          (show (0 : C(BrownianCubeAnchor d, ℝ)) ∈
            (⊥ : Submodule ℝ C(BrownianCubeAnchor d, ℝ)) by simp)
      _ = ENNReal.ofReal (dist (x : C(BrownianCubeAnchor d, ℝ)) 0) :=
        edist_dist _ _
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hdist
  rw [HaarQuarter.TheoremD.Width.kolmogorovWidthReal_zero_eq_bot K hK.isBounded]
  simpa using ENNReal.toReal_mono (by simp) herror

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

private theorem cmIndexRate_pos {d k : ℕ} (hk : 2 ≤ k) :
    0 < cmIndexRate d k := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hpow : 0 < (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
    Real.rpow_pos_of_pos hlog _
  have hkinv : 0 < (k : ℝ) ^ (-1 : ℝ) := by positivity
  simpa [cmIndexRate, logarithmicIndexRate] using mul_pos hkinv hpow

private theorem cmIndexRate_lower_dyadic {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (1 / (97 * (N : ℝ))) * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤
      cmIndexRate d (96 * N + 1) := by
  have hNR : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hkR : 0 < (96 * N + 1 : ℝ) := by positivity
  have hkUpper : (96 * N + 1 : ℝ) ≤ 97 * (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    push_cast
    nlinarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hlogCmp : Real.log (N : ℝ) ≤ Real.log (96 * N + 1 : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ha : 0 ≤ (d : ℝ) - 1 / 2 := by linarith
  have hpow := Real.rpow_le_rpow hlogN hlogCmp ha
  have hinv := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (96 * N + 1 : ℝ))
    hkUpper (by norm_num : (-1 : ℝ) ≤ 0)
  have hrate := mul_le_mul hinv hpow (by positivity) (by positivity)
  have hleft : (96 * N + 1 : ℝ) ^ (-1 : ℝ) = 1 / (96 * N + 1 : ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    ring
  have hright : (97 * (N : ℝ)) ^ (-1 : ℝ) = 1 / (97 * (N : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    ring
  simpa [cmIndexRate, logarithmicIndexRate, hright] using hrate

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

private theorem cmIndexRate_log_ge_one {d m : ℕ}
    (hd : 2 ≤ d) (hm : 3 ≤ m) :
    1 ≤ (Real.log (m : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
  have hmR : Real.exp 1 ≤ (m : ℝ) := by
    have h : Real.exp 1 < 3 := Real.exp_one_lt_three
    exact le_trans (le_of_lt h) (by exact_mod_cast hm)
  have hlog : 1 ≤ Real.log (m : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by positivity) hmR
  have ha : 1 ≤ (d : ℝ) - 1 / 2 := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hlog ha
  calc
    1 ≤ Real.log (m : ℝ) := hlog
    _ = (Real.log (m : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ (Real.log (m : ℝ)) ^ ((d : ℝ) - 1 / 2) := hpow

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

/-- Carl's dyadic cover budget must be at least the entropy lower scale. -/
theorem dyadic_budget_lower_of_entropy_lower
    {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L)
    (c B : ℝ) (hc : 0 < c)
    (hEntropy : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d))
    (hCover : HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1)
      (CameronMartin.KdUnitCube d) ≤ ENNReal.ofReal
        (4 * B / (4 : ℝ) ^ L)) :
    (c / 388) * (2 ^ L : ℝ) *
      (Real.log (2 ^ L : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤ B := by
  let N : ℝ := (2 ^ L : ℕ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hN2 : 2 ≤ 2 ^ L := by
    have : 1 ≤ L := hL
    nlinarith [Nat.pow_le_pow_right (by omega : 1 ≤ 2) this]
  have hNR : 2 ≤ N := by dsimp [N]; exact_mod_cast hN2
  have hQ : 0 ≤ (Real.log N) ^ ((d : ℝ) - 1 / 2) := by positivity
  have hrate := cmIndexRate_lower_dyadic hd hN2
  have hlower : c * ((1 / (97 * N)) * (Real.log N) ^ ((d : ℝ) - 1 / 2)) ≤
      c * cmIndexRate d (96 * 2 ^ L + 1) := by
    have hcast : ((2 ^ L : ℕ) : ℝ) = N := by rfl
    simpa [N, hcast] using (mul_le_mul_of_nonneg_left hrate hc.le)
  have hnonneg : 0 ≤ 4 * B / N ^ 2 := by
    have hBnonneg : 0 ≤ B := by
      by_contra hn
      have hneg : B < 0 := lt_of_not_ge hn
      have hright : 4 * B / (4 : ℝ) ^ L < 0 := div_neg_of_neg_of_pos
        (by nlinarith) (by positivity)
      have htop : ENNReal.ofReal (4 * B / (4 : ℝ) ^ L) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (le_of_lt hright)
      have hpos := cmIndexRate_pos (d := d) (k := 96 * 2 ^ L + 1) (by omega)
      have hpos' : 0 < c * cmIndexRate d (96 * 2 ^ L + 1) := mul_pos hc hpos
      have hcontra := le_trans (hEntropy _ (by omega)) hCover
      rw [htop] at hcontra
      exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hpos')) hcontra
    have hNsq : 0 < N ^ 2 := by positivity
    positivity
  have hNpow : (4 : ℝ) ^ L = N ^ 2 := by
    have hpow : (4 : ℝ) ^ L = ((2 : ℝ) ^ L) ^ 2 := by
      calc
        (4 : ℝ) ^ L = ((2 : ℝ) ^ 2) ^ L := by norm_num
        _ = (2 : ℝ) ^ (2 * L) := by rw [← pow_mul]
        _ = (2 : ℝ) ^ (L * 2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ L) ^ 2 := by rw [← pow_mul]
    simpa [N, Nat.cast_pow] using hpow
  have hupper : c * cmIndexRate d (96 * 2 ^ L + 1) ≤ 4 * B / N ^ 2 := by
    have hpair := le_trans (hEntropy _ (by omega)) hCover
    have hpair' : ENNReal.ofReal (c * cmIndexRate d (96 * 2 ^ L + 1)) ≤
        ENNReal.ofReal (4 * B / N ^ 2) := by simpa [hNpow] using hpair
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hpair'
  have hscalar : c * ((1 / (97 * N)) * (Real.log N) ^ ((d : ℝ) - 1 / 2)) ≤
      4 * B / N ^ 2 := le_trans hlower hupper
  have hmultiply := mul_le_mul_of_nonneg_right hscalar (sq_nonneg N)
  have hmultiply' : c * ((1 / (97 * N)) * (Real.log N) ^ ((d : ℝ) - 1 / 2)) * N ^ 2 ≤
      (4 * B / N ^ 2) * N ^ 2 := by simpa [pow_two] using hmultiply
  have hfinal : (c / 388) * N * (Real.log N) ^ ((d : ℝ) - 1 / 2) ≤ B := by
    have hN : N ≠ 0 := ne_of_gt hNpos
    field_simp [hN] at hmultiply'
    have hexp : ((d : ℝ) * 2 - 1) / 2 = (d : ℝ) - 1 / 2 := by ring
    rw [hexp] at hmultiply'
    nlinarith [hmultiply']
  simpa [N] using hfinal

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

/-- Carl's finite multiscale cover turns the actual Ehrhard entropy lower
bound into the matching width lower bound whenever the sharp width upper
bound is available. No entropy-to-width implication is assumed. -/
theorem KdUnitCube_width_lower_of_productGaussianEhrhard_and_sharp_upper
    (hEhrhard : ProductGaussianEhrhard) {d : ℕ} (hd : 2 ≤ d)
    (C : ℝ) (hC : 0 < C) (m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ≤
        ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c' * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k := by
  obtain ⟨c, hc, hEntropy⟩ :=
    cameronMartinEntropyLower_of_productGaussianEhrhard hEhrhard hd
  let lam : ℕ := Nat.ceil (776 * (4 * C + 2) / c) + 1
  have hlamPos : 0 < lam := by dsimp [lam]; omega
  have hlamReal : 776 * (4 * C + 2) / c ≤ (lam : ℝ) := by
    dsimp [lam]
    have hceil := Nat.le_ceil (776 * (4 * C + 2) / c)
    push_cast
    linarith
  have hlamBudget : 4 * C + 1 ≤ c / 776 * (lam : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hlamReal (by positivity : 0 ≤ c / 776)
    have hcancel : (776 * (4 * C + 2) / c) * (c / 776) = 4 * C + 2 := by
      field_simp
    nlinarith [hmul]
  let k₀ : ℕ := max (m₀ ^ 2) 3
  refine ⟨c / (1552 * (lam : ℝ)), by positivity, ?_⟩
  refine ⟨k₀, ?_⟩
  intro k hk
  have hm₀sq : m₀ ^ 2 ≤ k := le_trans (Nat.le_max_left _ _) hk
  have hk3 : 3 ≤ k := le_trans (Nat.le_max_right _ _) hk
  have hk2 : 2 ≤ k := by omega
  let x : ℕ := lam * k
  let L : ℕ := Nat.clog 2 x
  let N : ℕ := 2 ^ L
  have hlamNat : 1 ≤ lam := by omega
  have hx : 1 < x := by
    dsimp [x]
    have hkx : k ≤ lam * k := by
      calc
        k ≤ k * lam := Nat.le_mul_of_pos_right k (by omega)
        _ = lam * k := Nat.mul_comm _ _
    have hk1 : 1 < k := by omega
    exact lt_of_lt_of_le hk1 hkx
  have hNlo : x ≤ N := by
    dsimp [N, L, x]
    exact Nat.le_pow_clog (by omega : 1 < 2) _
  have hLpos : 0 < L := by
    by_contra hn
    have hLzero : L = 0 := by omega
    simp [N, hLzero] at hNlo
    dsimp [x] at hx
    omega
  have hpred : 2 ^ (L - 1) < x := by
    dsimp [L]
    exact Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hx
  have hLidentity : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
  have hNhi : N < 2 * x := by
    dsimp [N]
    calc
      2 ^ L = 2 ^ (L - 1 + 1) := by rw [hLidentity]
      _ = 2 ^ (L - 1) * 2 := by rw [pow_succ]
      _ < x * 2 := Nat.mul_lt_mul_of_pos_right hpred (by omega)
      _ = 2 * x := by omega
  have hkN : k ≤ N := by
    have hkx : k ≤ x := by
      dsimp [x]
      calc
        k ≤ k * lam := Nat.le_mul_of_pos_right k (by omega)
        _ = lam * k := Nat.mul_comm _ _
    exact le_trans hkx hNlo
  have hLpos1 : 1 ≤ L := by omega
  have hm₀K : m₀ ≤ k := by
    have hsq : m₀ ≤ m₀ ^ 2 := by
      calc
        m₀ ≤ m₀ * m₀ := Nat.le_mul_of_pos_right m₀ (by omega)
        _ = m₀ ^ 2 := by simp [pow_two]
    exact le_trans hsq hm₀sq
  have hNreal : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogge : 1 ≤ (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
    cmIndexRate_log_ge_one hd hk3
  have hlogmono := cmIndexRate_log_mono (m := k) (N := N) hd hk2 hkN
  have hQge : 1 ≤ (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := le_trans hlogge hlogmono
  have hm₀sqR : (m₀ : ℝ) ^ 2 ≤ (k : ℝ) := by exact_mod_cast hm₀sq
  have hNloR : (lam : ℝ) * (k : ℝ) ≤ (N : ℝ) := by
    have h := hNlo
    dsimp [x] at h
    exact_mod_cast h
  have hNhiR : (N : ℝ) ≤ 2 * (lam : ℝ) * (k : ℝ) := by
    have h := hNhi
    dsimp [x] at h
    have hcast : (N : ℝ) ≤ ((2 * (lam * k) : ℕ) : ℝ) := by exact_mod_cast h.le
    push_cast at hcast
    nlinarith [hcast]
  obtain ⟨B, hBformula, hBpos, hwidth⟩ :=
    dyadic_width_budget_of_sharp_upper hd hm₀ hm₀K
      hkN hLpos1 C hC hupper
  have hCover := entropy_le_of_dyadic_width_bound
    (K := CameronMartin.KdUnitCube d) B hBpos hwidth
  have hBudget := dyadic_budget_lower_of_entropy_lower
    hd hLpos1 c B hc hEntropy hCover
  have hlowScale : (4 * C + 1) * (k : ℝ) ≤ c / 776 * (N : ℝ) := by
    calc
      _ ≤ (c / 776 * (lam : ℝ)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hlamBudget (by positivity)
      _ = c / 776 * ((lam : ℝ) * (k : ℝ)) := by ring
      _ ≤ c / 776 * (N : ℝ) := mul_le_mul_of_nonneg_left hNloR (by positivity)
  have hlowTotal : (m₀ : ℝ) ^ 2 + 4 * C * (k : ℝ) *
        (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤
      (c / 776) * (N : ℝ) * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
    have hkQ : (k : ℝ) ≤ (k : ℝ) *
        (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := by nlinarith
    have hQnonneg' : 0 ≤ (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
      le_trans (by norm_num) hQge
    have hscaleQ := mul_le_mul_of_nonneg_right hlowScale hQnonneg'
    nlinarith [hm₀sqR, hkQ, hscaleQ]
  have hbudget' : (c / 388) * (N : ℝ) *
      (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤
      (m₀ : ℝ) ^ 2 + 4 * C * (k : ℝ) *
        (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) +
        (N : ℝ) ^ 2 *
          (HaarQuarter.TheoremD.Width.kolmogorovWidth
            (CameronMartin.KdUnitCube d) k).toReal := by
    simpa [hBformula, N] using hBudget
  have hvarianceLower : (c / 776) * (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤
      (N : ℝ) ^ 2 *
        (HaarQuarter.TheoremD.Width.kolmogorovWidth
          (CameronMartin.KdUnitCube d) k).toReal := by
    linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := by positivity
  have hwidthReal : (c / 776) *
      ((Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) / (N : ℝ)) ≤
      (HaarQuarter.TheoremD.Width.kolmogorovWidth
        (CameronMartin.KdUnitCube d) k).toReal := by
    have hdiv : ((c / 776) * (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2)) / (N : ℝ) ^ 2 ≤
        (HaarQuarter.TheoremD.Width.kolmogorovWidth
          (CameronMartin.KdUnitCube d) k).toReal :=
      (div_le_iff₀ (sq_pos_of_pos hNposR)).2 (by nlinarith [hvarianceLower])
    calc
      _ = ((c / 776) * (N : ℝ) *
          (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2)) / (N : ℝ) ^ 2 := by
            field_simp
            <;> ring
      _ ≤ _ := hdiv
  have htarget : (c / (1552 * (lam : ℝ))) * cmIndexRate d k ≤
      (HaarQuarter.TheoremD.Width.kolmogorovWidth
        (CameronMartin.KdUnitCube d) k).toReal := by
    have hrate : cmIndexRate d k =
        (1 / (k : ℝ)) * (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) := by
      unfold cmIndexRate logarithmicIndexRate
      rw [Real.rpow_neg (by positivity : 0 ≤ (k : ℝ)), Real.rpow_one]
      ring
    rw [hrate]
    have hcoef : c / (1552 * (lam : ℝ)) * (1 / (k : ℝ)) ≤
        c / 776 / (N : ℝ) := by
      have hposLam : 0 < (lam : ℝ) := by exact_mod_cast hlamPos
      have hposk : 0 < (k : ℝ) := by positivity
      have hineq : (N : ℝ) ≤ 2 * (lam : ℝ) * (k : ℝ) := hNhiR
      field_simp
      nlinarith [hineq, hc, hposLam, hposk]
    have hlogkNonneg : 0 ≤ (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
      le_trans (by norm_num) hlogge
    have hqprod := mul_le_mul hcoef hlogmono hlogkNonneg (by positivity)
    calc
      _ = (c / (1552 * (lam : ℝ)) * (1 / (k : ℝ))) *
          (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) := by ring
      _ ≤ (c / 776 / (N : ℝ)) * (Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) := hqprod
      _ = (c / 776) *
          ((Real.log (N : ℝ)) ^ ((d : ℝ) - 1 / 2) / (N : ℝ)) := by ring
      _ ≤ _ := hwidthReal
  have hfiniteK : HaarQuarter.TheoremD.Width.kolmogorovWidth
      (CameronMartin.KdUnitCube d) k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hupper k hm₀K)
  rw [← ENNReal.ofReal_toReal hfiniteK]
  exact ENNReal.ofReal_le_ofReal htarget


end

end BrownianSharp.CarlRateExtraction
