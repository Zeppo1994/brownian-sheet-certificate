import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
import BrownianSharp.AlignmentPeriodicFeatureEntropy
import BrownianSharp.LayerIndex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Index inversion for a discrete joint-grade entropy estimate. -/

noncomputable section
set_option maxHeartbeats 600000
open Filter Topology
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperJointGradeEntropyInversion

open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperLpJointDvp

def stageEntropyIndex (Cbudget : ℝ) (d N : ℕ) : ℕ :=
  Nat.ceil (Cbudget * (JointSampleDimension d N : ℝ)) + 1

theorem entropyNumber_antitone {X : Type*} [PseudoEMetricSpace X]
    {i j : ℕ} (hij : i ≤ j) (K : Set X) :
    HaarQuarter.TheoremD.entropyNumber j K ≤ HaarQuarter.TheoremD.entropyNumber i K := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro ρ ⟨ε, rfl, hcover⟩
  apply sInf_le
  refine ⟨ε, rfl, ?_⟩
  exact hcover.trans (by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < 2)
      (Nat.sub_le_sub_right hij 1)))

theorem jointSampleDimension_ge_pow {d n : ℕ} (hd : 2 ≤ d) :
    2^n ≤ JointSampleDimension d n := by
  rw [jointSampleDimension_eq_grid_formula, BrownianSharp.shape_card
    d n (by omega : 0 < d)]
  have hc : 1 ≤ Nat.choose (n+d-1) (d-1) := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  calc
    2^n ≤ 2^(n+3*d+1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2^(n+3*d+1) * 1 := by simp
    _ ≤ 2^(n+3*d+1) * Nat.choose (n+d-1) (d-1) :=
      Nat.mul_le_mul_left _ hc

theorem jointSampleDimension_step_le {d n : ℕ} (hd : 2 ≤ d) :
    (JointSampleDimension d (n+1) : ℝ) ≤
      ((Nat.factorial (d-1) : ℝ) * (2:ℝ)^d) *
        (JointSampleDimension d n : ℝ) := by
  let A : ℝ := (2:ℝ)^(3*d+1)
  let B : ℝ := A / (Nat.factorial (d-1) : ℝ)
  have hA : 0 < A := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hu := jointSampleDimension_upper_envelope (d:=d) (n:=n+1) (by omega : 1≤d)
  have hl := jointSampleDimension_lower_envelope (d:=d) (n:=n) (by omega : 1≤d)
  have hpoly : (n+2:ℝ)^(d-1) ≤ (2:ℝ)^(d-1)*(n+1:ℝ)^(d-1) := by
    have hb : (n+2:ℝ) ≤ 2*(n+1:ℝ) := by nlinarith
    calc
      (n+2:ℝ)^(d-1) ≤ (2*(n+1:ℝ))^(d-1) := by gcongr
      _ = (2:ℝ)^(d-1)*(n+1:ℝ)^(d-1) := by rw [mul_pow]
  have hupper : (JointSampleDimension d (n+1):ℝ) ≤
      A * (2:ℝ)^(n+1) * (n+2:ℝ)^(d-1) := by
    convert hu using 1 <;> dsimp [A] <;> push_cast <;> ring
  have hlower : B * (2:ℝ)^n * (n+1:ℝ)^(d-1) ≤
      (JointSampleDimension d n:ℝ) := by
    simpa [A, B] using hl
  have hcalc : A * (2:ℝ)^(n+1) * (n+2:ℝ)^(d-1) ≤
      ((Nat.factorial (d-1):ℝ) * (2:ℝ)^d) *
        (B * (2:ℝ)^n * (n+1:ℝ)^(d-1)) := by
    calc
      A * (2:ℝ)^(n+1) * (n+2:ℝ)^(d-1) ≤
          A * (2:ℝ)^(n+1) * ((2:ℝ)^(d-1)*(n+1:ℝ)^(d-1)) := by
        exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = ((Nat.factorial (d-1):ℝ) * (2:ℝ)^d) *
          (B * (2:ℝ)^n * (n+1:ℝ)^(d-1)) := by
        rw [pow_succ, show d = (d-1)+1 by omega, pow_succ]
        dsimp [B]
        field_simp
  calc
    (JointSampleDimension d (n+1):ℝ) ≤
      A * (2:ℝ)^(n+1) * (n+2:ℝ)^(d-1) := hupper
    _ ≤ ((Nat.factorial (d-1):ℝ) * (2:ℝ)^d) *
        (B * (2:ℝ)^n * (n+1:ℝ)^(d-1)) := hcalc
    _ ≤ ((Nat.factorial (d-1):ℝ) * (2:ℝ)^d) *
        (JointSampleDimension d n:ℝ) := by
      exact mul_le_mul_of_nonneg_left hlower (by positivity)

private theorem exists_stage_index_gt {d N₀ k : ℕ} (hd : 2 ≤ d)
    {Cbudget : ℝ} (hCb : 0 < Cbudget) :
    ∃ j : ℕ, k < stageEntropyIndex Cbudget d (N₀+j) := by
  have htend : Tendsto (fun j : ℕ => (2:ℝ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨j, hj⟩ := (htend.eventually_gt_atTop ((k:ℝ)/Cbudget)).exists
  have hdim := jointSampleDimension_ge_pow (d:=d) (n:=N₀+j) hd
  have hpow : (2:ℝ)^j ≤ (JointSampleDimension d (N₀+j):ℝ) := by
    have hnat : 2^j ≤ JointSampleDimension d (N₀+j) := by
      exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hdim
    exact_mod_cast hnat
  have hbudget : (k:ℝ) < Cbudget * (JointSampleDimension d (N₀+j):ℝ) := by
    calc
      (k:ℝ) < Cbudget * (2:ℝ)^j := by
        have := (div_lt_iff₀ hCb).mp hj
        nlinarith [this]
      _ ≤ Cbudget * (JointSampleDimension d (N₀+j):ℝ) :=
        mul_le_mul_of_nonneg_left hpow hCb.le
  have hceil : (k:ℝ) < (Nat.ceil (Cbudget *
      (JointSampleDimension d (N₀+j):ℝ)) : ℝ) := by
    exact lt_of_lt_of_le hbudget (Nat.le_ceil _)
  have hnat : k < Nat.ceil (Cbudget *
      (JointSampleDimension d (N₀+j):ℝ)) := by exact_mod_cast hceil
  exact ⟨j, by dsimp [stageEntropyIndex]; omega⟩

/-- A stage estimate at the actual joint sample dimension converts to the
sharp all-index power-log upper rate. The constants are fixed before `k`. -/
theorem eventually_entropy_powerlog_of_joint_stage_bounds
    {X : Type*} [PseudoEMetricSpace X] {d : ℕ} (hd : 2 ≤ d) (K : Set X)
    {Cbudget Cerror : ℝ} (hCb : 0 < Cbudget) (hCe : 0 < Cerror)
    (N₀ : ℕ)
    (hstage : ∀ N : ℕ, N₀ ≤ N →
      HaarQuarter.TheoremD.entropyNumber (stageEntropyIndex Cbudget d N) K ≤
        ENNReal.ofReal (Cerror * (2:ℝ)^(-(N:ℝ)) *
          Real.sqrt ((N+1:ℕ):ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k K ≤
        ENNReal.ofReal (C * (k:ℝ)⁻¹ *
          Real.rpow (Real.log (k:ℝ)) ((d:ℝ)-1/2)) := by
  classical
  let Mdim : ℝ := (2:ℝ)^(3*d+1)
  let ratio : ℝ := (Nat.factorial (d-1):ℝ) * (2:ℝ)^d
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Cbudget⁻¹ ≤ (2:ℝ)^M := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
    obtain ⟨M, hM⟩ := (ht.eventually_ge_atTop Cbudget⁻¹).exists
    exact ⟨M, hM⟩
  let L : ℝ := ((M:ℝ)+1)/Real.log 2 + (1/Real.log 2)
  let beta : ℝ := (d:ℝ)-1/2
  let C : ℝ := Cerror * Mdim * (2*Cbudget*ratio) * Real.rpow L beta
  let k₀ : ℕ := max 3 (stageEntropyIndex Cbudget d N₀)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  have hbeta : 0 < beta := by
    dsimp [beta]
    have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, k₀, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hq0 : stageEntropyIndex Cbudget d N₀ ≤ k :=
    le_trans (le_max_right _ _) hk
  have hk2 : 2 ≤ k := by omega
  have hPexists := exists_stage_index_gt (d:=d) (N₀:=N₀) (k:=k) hd hCb
  let P : ℕ → Prop := fun j => k < stageEntropyIndex Cbudget d (N₀+j)
  have hP : ∃ j, P j := by simpa [P] using hPexists
  let j : ℕ := Nat.find hP
  have hjcross : P j := Nat.find_spec hP
  have hj0 : 0 < j := by
    by_contra hnot
    have hjzero : j = 0 := by omega
    have hfalse : ¬ P 0 := by
      change ¬ k < stageEntropyIndex Cbudget d N₀
      exact not_lt_of_ge hq0
    have hjc0 : P 0 := by simpa [j, hjzero] using hjcross
    exact hfalse hjc0
  let n : ℕ := N₀ + (j-1)
  have hsucc : N₀+j = n+1 := by dsimp [n]; omega
  have hprev : stageEntropyIndex Cbudget d n ≤ k := by
    have hmin := Nat.find_min hP (Nat.sub_lt hj0 (by omega : 0<1))
    have hnot : ¬ k < stageEntropyIndex Cbudget d (N₀+(j-1)) := by
      simpa [P] using hmin
    have heq : N₀+(j-1)=n := by dsimp [n]
    rw [← heq]
    exact Nat.le_of_not_gt hnot
  have hcross' : k < stageEntropyIndex Cbudget d (n+1) := by
    have ht : k < stageEntropyIndex Cbudget d (N₀+j) := by
      simpa [P] using hjcross
    rw [hsucc] at ht
    exact ht
  have hceil_prev : (Cbudget * (JointSampleDimension d n:ℝ)) ≤ (k:ℝ)-1 := by
    have hc : Nat.ceil (Cbudget * (JointSampleDimension d n:ℝ)) ≤ k-1 := by
      dsimp [stageEntropyIndex] at hprev
      omega
    have hreal := Nat.le_ceil (Cbudget * (JointSampleDimension d n:ℝ))
    have hcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1≤k)]
      simp
    have hcReal : (Nat.ceil (Cbudget * (JointSampleDimension d n:ℝ)):ℝ) ≤
        ((k-1:ℕ):ℝ) := by exact_mod_cast hc
    calc
      Cbudget * (JointSampleDimension d n:ℝ) ≤
          (Nat.ceil (Cbudget * (JointSampleDimension d n:ℝ)):ℝ) := hreal
      _ ≤ ((k-1:ℕ):ℝ) := hcReal
      _ = (k:ℝ)-1 := hcast
  have hceil_next : (k:ℝ)-1 <
      Cbudget * (JointSampleDimension d (n+1):ℝ) := by
    have hc : k ≤ Nat.ceil (Cbudget * (JointSampleDimension d (n+1):ℝ)) := by
      dsimp [stageEntropyIndex] at hcross'
      omega
    have hlt := Nat.ceil_lt_add_one
      (show 0 ≤ Cbudget * (JointSampleDimension d (n+1):ℝ) by positivity)
    have hc' : (k:ℝ) ≤ (Nat.ceil (Cbudget *
        (JointSampleDimension d (n+1):ℝ)):ℝ) := by exact_mod_cast hc
    linarith
  have hDupper : (JointSampleDimension d n:ℝ) ≤ (k:ℝ)/Cbudget := by
    exact (le_div_iff₀ hCb).2 (by linarith [hceil_prev])
  have hDnextlower : (k:ℝ)/(2*Cbudget*ratio) ≤
      (JointSampleDimension d n:ℝ) := by
    have hstep := jointSampleDimension_step_le (d:=d) (n:=n) hd
    have hk2R : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hkminus : (k:ℝ)/2 ≤ (k:ℝ)-1 := by nlinarith [hk2R]
    have hprod : (k:ℝ)/2 < Cbudget*ratio*(JointSampleDimension d n:ℝ) := by
      calc
        (k:ℝ)/2 ≤ (k:ℝ)-1 := hkminus
        _ < Cbudget*(JointSampleDimension d (n+1):ℝ) := hceil_next
        _ ≤ Cbudget*(ratio*(JointSampleDimension d n:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hstep hCb.le
        _ = Cbudget*ratio*(JointSampleDimension d n:ℝ) := by ring
    apply (div_le_iff₀ (by positivity : 0 < 2*Cbudget*ratio)).2
    have hdouble : (k:ℝ) < (2*Cbudget*ratio)*(JointSampleDimension d n:ℝ) := by
      calc
        (k:ℝ) = 2*((k:ℝ)/2) := by ring
        _ < 2*(Cbudget*ratio*(JointSampleDimension d n:ℝ)) :=
          mul_lt_mul_of_pos_left hprod (by norm_num)
        _ = (2*Cbudget*ratio)*(JointSampleDimension d n:ℝ) := by ring
    simpa [mul_comm] using hdouble.le
  have hDupperM : (JointSampleDimension d n:ℝ) ≤ (2:ℝ)^M * k := by
    calc
      (JointSampleDimension d n:ℝ) ≤ (k:ℝ)/Cbudget := hDupper
      _ = Cbudget⁻¹ * k := by field_simp
      _ ≤ (2:ℝ)^M * k := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
  have hpowN : 2^n ≤ 2^M*k := by
    have hcast : (JointSampleDimension d n:ℝ) ≤ ((2^M*k:ℕ):ℝ) := by
      exact_mod_cast hDupperM
    have hnat := jointSampleDimension_ge_pow (d:=d) (n:=n) hd
    exact hnat.trans (by exact_mod_cast hcast)
  have hlogkpow : k < 2^(Nat.log2 k + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_of_log_lt (by omega) (Nat.lt_succ_self (Nat.log 2 k))
  have hgradeLog : n ≤ M + Nat.log2 k := by
    have hmul : 2^M*k < 2^M * 2^(Nat.log2 k+1) :=
      Nat.mul_lt_mul_of_pos_left hlogkpow (by positivity)
    have hpower : 2^M*k < 2^(M+(Nat.log2 k+1)) := by
      simpa [pow_add, Nat.mul_comm, Nat.add_assoc] using hmul
    have hpowle : 2^n < 2^(M+(Nat.log2 k+1)) := hpowN.trans_lt hpower
    have hexp : n < M+(Nat.log2 k+1) := (Nat.pow_lt_pow_iff_right (by omega)).mp hpowle
    omega
  have hlogNat : (Nat.log2 k:ℝ) * Real.log 2 ≤ Real.log (k:ℝ) := by
    have hpNat := Nat.log2_self_le (by omega : k ≠ 0)
    have hpReal : Real.rpow 2 (Nat.log2 k:ℝ) ≤ (k:ℝ) := by
      have hpReal' : (2:ℝ)^(Nat.log2 k) ≤ (k:ℝ) := by exact_mod_cast hpNat
      calc
        Real.rpow 2 (Nat.log2 k:ℝ) = (2:ℝ)^(Nat.log2 k) :=
          Real.rpow_natCast 2 (Nat.log2 k)
        _ ≤ (k:ℝ) := hpReal'
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hpReal
    simpa [Real.log_rpow (by norm_num : (0:ℝ)<2)] using hlog
  have hlog2le : Real.log 2 ≤ Real.log (k:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
  have hgradeLogReal : (n:ℝ)+1 ≤ L * Real.log (k:ℝ) := by
    have hNcast : (n:ℝ) ≤ (M:ℝ)+(Nat.log2 k:ℝ) := by exact_mod_cast hgradeLog
    have hMlog : (M:ℝ)+1 ≤ ((M:ℝ)+1)/Real.log 2 * Real.log (k:ℝ) := by
      calc
        (M:ℝ)+1 ≤ (((M:ℝ)+1)*Real.log (k:ℝ))/Real.log 2 := by
          apply (le_div_iff₀ hlog2).2
          have hh := mul_le_mul_of_nonneg_left hlog2le (by positivity : 0≤(M:ℝ)+1)
          nlinarith
        _ = ((M:ℝ)+1)/Real.log 2*Real.log (k:ℝ) := by ring
    have hNlog : (Nat.log2 k:ℝ) ≤ (1/Real.log 2)*Real.log (k:ℝ) := by
      calc
        (Nat.log2 k:ℝ) ≤ Real.log (k:ℝ)/Real.log 2 :=
          (le_div_iff₀ hlog2).2 hlogNat
        _ = (1/Real.log 2)*Real.log (k:ℝ) := by ring
    have hsum : (M:ℝ)+1+(Nat.log2 k:ℝ) ≤
        (((M:ℝ)+1)/Real.log 2 + 1/Real.log 2)*Real.log (k:ℝ) := by
      calc
        _ ≤ (((M:ℝ)+1)/Real.log 2*Real.log (k:ℝ)) +
            ((1/Real.log 2)*Real.log (k:ℝ)) := add_le_add hMlog hNlog
        _ = (((M:ℝ)+1)/Real.log 2 + 1/Real.log 2)*Real.log (k:ℝ) := by ring
    have hn : (n:ℝ)+1 ≤ (M:ℝ)+1+(Nat.log2 k:ℝ) := by linarith [hNcast]
    dsimp [L]
    exact hn.trans hsum
  have henv : (JointSampleDimension d n:ℝ) ≤
      Mdim*(2:ℝ)^n*(n+1:ℝ)^(d-1) := by
    convert jointSampleDimension_upper_envelope (d:=d) (n:=n) (by omega : 1≤d)
      using 1 <;> dsimp [Mdim] <;> push_cast <;> ring
  have hDpos : 0 < (JointSampleDimension d n:ℝ) := by
    have hn : 0 < JointSampleDimension d n :=
      lt_of_lt_of_le (Nat.pow_pos (by omega))
        (jointSampleDimension_ge_pow (d:=d) (n:=n) hd)
    exact_mod_cast hn
  have hpowpos : 0 < (2:ℝ)^n := by positivity
  have hpowNegId : (2:ℝ)^(-(n:ℝ)) = ((2:ℝ)^n)⁻¹ := by
    rw [← Real.rpow_natCast, Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  have hpowNeg : (2:ℝ)^(-(n:ℝ)) ≤
      Mdim*(n+1:ℝ)^(d-1)/(JointSampleDimension d n:ℝ) := by
    rw [hpowNegId]
    apply (le_div_iff₀ hDpos).2
    calc
      ((2:ℝ)^n)⁻¹ * (JointSampleDimension d n:ℝ) ≤
          ((2:ℝ)^n)⁻¹ * (Mdim*(2:ℝ)^n*(n+1:ℝ)^(d-1)) :=
        mul_le_mul_of_nonneg_left henv (by positivity)
      _ = Mdim*(n+1:ℝ)^(d-1) := by field_simp
  have hzpos : 0 < (n+1:ℝ) := by positivity
  have hrootPoly : (n+1:ℝ)^(d-1) * Real.sqrt (n+1:ℝ) =
      Real.rpow (n+1:ℝ) beta := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hzpos]
    congr 1
    dsimp [beta]
    rw [Nat.cast_sub (by omega : 1≤d)]
    push_cast
    ring
  have hrootMono : Real.rpow (n+1:ℝ) beta ≤
      Real.rpow (L*Real.log (k:ℝ)) beta := by
    apply Real.rpow_le_rpow hzpos.le hgradeLogReal hbeta.le
  have hDlowerForRate : (k:ℝ)/(2*Cbudget*ratio) ≤
      (JointSampleDimension d n:ℝ) := hDnextlower
  have hDinv : (JointSampleDimension d n:ℝ)⁻¹ ≤
      (2*Cbudget*ratio)*(k:ℝ)⁻¹ := by
    have hkpos : 0 < (k:ℝ) := by positivity
    have hconst : 0 < 2*Cbudget*ratio := by positivity
    have hprod : (k:ℝ) ≤ (2*Cbudget*ratio)*(JointSampleDimension d n:ℝ) :=
      by simpa [mul_comm] using (div_le_iff₀ hconst).mp hDlowerForRate
    have hdiv : (k:ℝ)/(JointSampleDimension d n:ℝ) ≤ 2*Cbudget*ratio :=
      (div_le_iff₀ hDpos).2 hprod
    apply (le_div_iff₀ hkpos).2
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have herr : Cerror*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) ≤
      C*(k:ℝ)⁻¹*Real.rpow (Real.log (k:ℝ)) beta := by
    have hrate0 : Cerror*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) ≤
        Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹*
          Real.rpow (n+1:ℝ) beta := by
      calc
        Cerror*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) =
            (Cerror*(2:ℝ)^(-(n:ℝ)))*Real.sqrt (n+1:ℝ) := by ring
        _ ≤ (Cerror*(Mdim*(n+1:ℝ)^(d-1)/(JointSampleDimension d n:ℝ)))*
              Real.sqrt (n+1:ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowNeg (by positivity)) (Real.sqrt_nonneg _)
        _ = Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹ *
              ((n+1:ℝ)^(d-1)*Real.sqrt (n+1:ℝ)) := by field_simp <;> ring
        _ = Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹*
              Real.rpow (n+1:ℝ) beta := by rw [← hrootPoly]
    have hrate1 : Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹*
        Real.rpow (n+1:ℝ) beta ≤
        Cerror*Mdim*(2*Cbudget*ratio)*(k:ℝ)⁻¹*
          Real.rpow (L*Real.log (k:ℝ)) beta := by
      calc
        Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹*Real.rpow (n+1:ℝ) beta =
            (Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹)*Real.rpow (n+1:ℝ) beta := by ring
        _ ≤ (Cerror*Mdim*((2*Cbudget*ratio)*(k:ℝ)⁻¹))*
            Real.rpow (n+1:ℝ) beta := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDinv (by positivity)) (Real.rpow_nonneg hzpos.le _)
        _ = Cerror*Mdim*(2*Cbudget*ratio)*(k:ℝ)⁻¹*
            Real.rpow (n+1:ℝ) beta := by ring
        _ ≤ Cerror*Mdim*(2*Cbudget*ratio)*(k:ℝ)⁻¹*
            Real.rpow (L*Real.log (k:ℝ)) beta := by
          exact mul_le_mul_of_nonneg_left hrootMono (by positivity)
    calc
      _ ≤ Cerror*Mdim*(JointSampleDimension d n:ℝ)⁻¹*
          Real.rpow (n+1:ℝ) beta := hrate0
      _ ≤ Cerror*Mdim*(2*Cbudget*ratio)*(k:ℝ)⁻¹*
          Real.rpow (L*Real.log (k:ℝ)) beta := hrate1
      _ = Cerror*Mdim*(2*Cbudget*ratio)*Real.rpow L beta*(k:ℝ)⁻¹*
          Real.rpow (Real.log (k:ℝ)) beta := by
        have hsplit : Real.rpow (L*Real.log (k:ℝ)) beta =
            Real.rpow L beta * Real.rpow (Real.log (k:ℝ)) beta :=
          Real.mul_rpow hL.le
            (Real.log_nonneg (by exact_mod_cast (show 1≤k by omega)))
        rw [hsplit]
        ring
      _ = C*(k:ℝ)⁻¹*Real.rpow (Real.log (k:ℝ)) beta := by
        dsimp [C]
  have hmono := entropyNumber_antitone hprev K
  have hst := hstage n (by dsimp [n]; omega)
  have hst' : HaarQuarter.TheoremD.entropyNumber (stageEntropyIndex Cbudget d n) K ≤
      ENNReal.ofReal (Cerror*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hst
  calc
    HaarQuarter.TheoremD.entropyNumber k K ≤
        HaarQuarter.TheoremD.entropyNumber (stageEntropyIndex Cbudget d n) K := hmono
    _ ≤ ENNReal.ofReal (Cerror*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)) := hst'
    _ ≤ ENNReal.ofReal (C*(k:ℝ)⁻¹*Real.rpow (Real.log (k:ℝ)) beta) :=
      ENNReal.ofReal_le_ofReal herr

end BrownianSharp.AlignmentPaperJointGradeEntropyInversion
