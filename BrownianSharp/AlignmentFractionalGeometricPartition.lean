import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A finite positive geometric partition for the MvN time variable. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalGeometricPartition

/-- Linear cutoff, zero through `1/2` and one from `1` onward. -/
def cutoff (x : ℝ) : ℝ := min 1 (max 0 (2*x-1))

theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := by
  have hm : 0 ≤ max 0 (2*x-1) := le_max_left _ _
  exact le_min (by norm_num) hm

theorem cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := min_le_left _ _

theorem cutoff_mono {x y : ℝ} (hxy : x ≤ y) : cutoff x ≤ cutoff y := by
  unfold cutoff
  apply min_le_min (le_refl 1)
  exact max_le_max (le_refl 0) (by linarith)

theorem cutoff_eq_zero_of_le_half {x : ℝ} (h : x ≤ 1/2) : cutoff x = 0 := by
  unfold cutoff
  rw [max_eq_left (by linarith : 2*x-1 ≤ 0)]
  simp

theorem cutoff_eq_one_of_one_le {x : ℝ} (h : 1 ≤ x) : cutoff x = 1 := by
  unfold cutoff
  rw [max_eq_right (by linarith : 0 ≤ 2*x-1)]
  rw [min_eq_left (by linarith : 1 ≤ 2*x-1)]

theorem cutoff_pos_iff {x : ℝ} : 0 < cutoff x ↔ 1/2 < x := by
  constructor
  · intro h
    by_contra h'
    have hx : x ≤ 1/2 := le_of_not_gt h'
    rw [cutoff_eq_zero_of_le_half hx] at h
    exact (lt_irrefl 0 h)
  · intro hx
    unfold cutoff
    have hlin : 0 < 2*x-1 := by linarith
    have hmax : 0 < max 0 (2*x-1) := by
      exact lt_of_lt_of_le hlin (le_max_right _ _)
    exact lt_min (by norm_num) hmax

theorem cutoff_lt_one_imp_lt_one {x : ℝ} (h : cutoff x < 1) : x < 1 := by
  by_contra hx
  have hone : cutoff x = 1 := cutoff_eq_one_of_one_le (le_of_not_gt hx)
  linarith

/-- Dyadic shell weight `χ(2^(j+1)t)-χ(2^j t)`. -/
def shellWeight (j : ℕ) (t : ℝ) : ℝ :=
  cutoff (t*(2:ℝ)^(j+1)) - cutoff (t*(2:ℝ)^j)

/-- The coarse component is `χ(t)`. -/
def coarseWeight (t : ℝ) : ℝ := cutoff t

/-- The coarse interval followed by the finitely many dyadic shells. -/
def partitionWeight (J : ℕ) (i : Option (Fin J)) (t : ℝ) : ℝ :=
  match i with
  | none => coarseWeight t
  | some j => shellWeight j t

theorem shellWeight_nonneg {j : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ shellWeight j t := by
  unfold shellWeight
  apply sub_nonneg.mpr
  apply cutoff_mono
  rw [pow_succ]
  have hp : 0 ≤ (2:ℝ)^j := by positivity
  nlinarith [mul_nonneg ht hp]

theorem coarseWeight_nonneg (t : ℝ) : 0 ≤ coarseWeight t := cutoff_nonneg t

theorem partitionWeight_nonneg {J : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (i : Option (Fin J)) : 0 ≤ partitionWeight J i t := by
  cases i with
  | none => exact coarseWeight_nonneg t
  | some j => exact shellWeight_nonneg ht

theorem shellWeight_le_one (j : ℕ) (t : ℝ) : shellWeight j t ≤ 1 := by
  unfold shellWeight
  have h1 := cutoff_le_one (t*(2:ℝ)^(j+1))
  have h0 := cutoff_nonneg (t*(2:ℝ)^j)
  linarith

/-- The shell is supported on `[2^(-j)/4, 2^(-j)]`. -/
theorem shellWeight_support {j : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hwt : shellWeight j t ≠ 0) :
    t ∈ Set.Icc ((1/(2:ℝ)^j)/4) (1/(2:ℝ)^j) := by
  have hnonneg := shellWeight_nonneg (j:=j) ht
  have hpos : 0 < shellWeight j t := lt_of_le_of_ne hnonneg (Ne.symm hwt)
  have hfirst : 0 < cutoff (t*(2:ℝ)^(j+1)) := by
    unfold shellWeight at hpos
    have := cutoff_nonneg (t*(2:ℝ)^j)
    linarith
  have hlast : cutoff (t*(2:ℝ)^j) < 1 := by
    unfold shellWeight at hpos
    have := cutoff_le_one (t*(2:ℝ)^(j+1))
    linarith
  have hfirst' := (cutoff_pos_iff).1 hfirst
  have hlast' := cutoff_lt_one_imp_lt_one hlast
  have hp : 0 < (2:ℝ)^j := by positivity
  have hlo : (1/(2:ℝ)^j)/4 ≤ t := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).2
    apply (div_le_iff₀ hp).2
    rw [pow_succ] at hfirst'
    nlinarith
  have hhi : t ≤ 1/(2:ℝ)^j := by
    apply (le_div_iff₀ hp).2
    exact le_of_lt hlast'
  exact ⟨hlo,hhi⟩

theorem coarseWeight_support {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwt : coarseWeight t ≠ 0) : t ∈ Set.Icc (1/2:ℝ) 1 := by
  have hpos : 0 < cutoff t := by
    change cutoff t ≠ 0 at hwt
    have hn : 0 ≤ cutoff t := cutoff_nonneg t
    exact lt_of_le_of_ne hn (Ne.symm hwt)
  exact ⟨le_of_lt ((cutoff_pos_iff).1 hpos),ht1⟩

/-- A finite set of coarse-plus-shell weights telescopes exactly. -/
theorem geometricPartition_sum (J : ℕ) (t : ℝ) :
    coarseWeight t + ∑ j ∈ Finset.range J, shellWeight j t =
      cutoff (t*(2:ℝ)^J) := by
  induction J with
  | zero => simp [coarseWeight]
  | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        coarseWeight t + (∑ j ∈ Finset.range J, shellWeight j t + shellWeight J t) =
            (coarseWeight t + ∑ j ∈ Finset.range J, shellWeight j t) + shellWeight J t := by ring
        _ = cutoff (t*(2:ℝ)^J) + shellWeight J t := by rw [ih]
        _ = cutoff (t*(2:ℝ)^(J+1)) := by
          unfold shellWeight
          rw [pow_succ]
          ring

theorem partitionWeight_sum (J : ℕ) (t : ℝ) :
    (∑ i : Option (Fin J), partitionWeight J i t) = cutoff (t*(2:ℝ)^J) := by
  rw [Fintype.sum_option]
  simp only [partitionWeight]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => shellWeight j t) J]
  exact geometricPartition_sum J t

theorem geometricPartition_sum_le_one {J : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    coarseWeight t + ∑ j ∈ Finset.range J, shellWeight j t ≤ 1 := by
  rw [geometricPartition_sum]
  exact cutoff_le_one _

theorem geometricPartition_sum_nonneg {J : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ coarseWeight t + ∑ j ∈ Finset.range J, shellWeight j t := by
  rw [geometricPartition_sum]
  exact cutoff_nonneg _

theorem remainder_nonneg (J : ℕ) (t : ℝ) :
    0 ≤ 1-cutoff (t*(2:ℝ)^J) := by
  linarith [cutoff_le_one (t*(2:ℝ)^J)]

/-- The unallocated remainder vanishes above the final dyadic scale. -/
theorem remainder_eq_zero_of_scale_le {J : ℕ} {t : ℝ}
    (ht : 1/(2:ℝ)^J ≤ t) : 1-cutoff (t*(2:ℝ)^J) = 0 := by
  have hp : 0 < (2:ℝ)^J := by positivity
  have hmul : 1 ≤ t*(2:ℝ)^J := (div_le_iff₀ hp).1 ht
  rw [cutoff_eq_one_of_one_le hmul]
  ring

/-- Any nonzero remainder on `[0,1]` is confined to the final interval. -/
theorem remainder_support {J : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrem : 1-cutoff (t*(2:ℝ)^J) ≠ 0) : t ≤ 1/(2:ℝ)^J := by
  by_contra ht
  have hz := remainder_eq_zero_of_scale_le (le_of_not_ge ht)
  exact hrem hz

/-- The nominal center and radius of a dyadic shell. -/
def shellCenter (j : ℕ) : ℝ := (5/8:ℝ)/(2:ℝ)^j

def partitionCenter (i : Option (Fin J)) : ℝ :=
  match i with
  | none => 3/4
  | some j => shellCenter j

def partitionSupport (i : Option (Fin J)) : Set ℝ :=
  match i with
  | none => Set.Icc (1/2:ℝ) 1
  | some j => Set.Icc ((1/(2:ℝ)^j.val)/4) (1/(2:ℝ)^j.val)

theorem partitionWeight_support {J : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Option (Fin J)) (hwt : partitionWeight J i t ≠ 0) :
    t ∈ partitionSupport i := by
  cases i with
  | none => exact coarseWeight_support ht ht1 hwt
  | some j => exact shellWeight_support ht hwt

theorem shell_center_ratio_bound {j : ℕ} {t x : ℝ}
    (ht : t ∈ Set.Icc ((1/(2:ℝ)^j)/4) (1/(2:ℝ)^j))
    (hx : 0 ≤ x) :
    |t-shellCenter j|/(x+shellCenter j) ≤ 3/5 := by
  have hp : 0 < (2:ℝ)^j := by positivity
  let c : ℝ := 1/(2:ℝ)^j
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcs : 0 < shellCenter j := by
    dsimp [shellCenter]
    positivity
  have hcenter : shellCenter j = (5/8:ℝ)*c := by
    dsimp [shellCenter,c]
    ring
  have hrad : |t-shellCenter j| ≤ (3/8:ℝ)*c := by
    rw [abs_le]
    constructor <;> rw [hcenter] <;> nlinarith [ht.1, ht.2]
  have hden : 0 < x+shellCenter j := by linarith
  apply (div_le_iff₀ hden).2
  rw [hcenter]
  rw [hcenter] at hrad
  nlinarith [mul_nonneg hx (by norm_num : (0:ℝ)≤(3/5:ℝ))]

theorem partition_center_ratio_bound {J : ℕ} {t x : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : 0 ≤ x)
    (i : Option (Fin J)) (hwt : partitionWeight J i t ≠ 0) :
    |t-partitionCenter i|/(x+partitionCenter i) ≤ 3/5 := by
  cases i with
  | none =>
      have htop := coarseWeight_support ht0 ht1 hwt
      have hc : 0 < (3/4:ℝ) := by norm_num
      have hden : 0 < x+3/4 := by linarith
      apply (div_le_iff₀ hden).2
      have habs : |t-3/4| ≤ 1/4 := by
        rw [abs_le]
        constructor <;> linarith [htop.1,htop.2]
      dsimp [partitionCenter]
      nlinarith [mul_nonneg hx (by norm_num : (0:ℝ)≤(3/5:ℝ))]
  | some j =>
      have hs := shellWeight_support ht0 hwt
      simpa [partitionCenter] using shell_center_ratio_bound hs hx

end BrownianSharp.AlignmentFractionalGeometricPartition
