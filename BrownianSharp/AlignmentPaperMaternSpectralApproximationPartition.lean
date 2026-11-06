import BrownianSharp.AlignmentPaperMaternSpectralApproximation
import Mathlib.Order.Interval.Set.Union

/-! The actual central and signed-band cells used by the Matérn spectral
Taylor approximation: disjointness and finite partition geometry. -/

noncomputable section
open MeasureTheory
open scoped ENNReal Topology RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternSpectralApproximationPartition

open BrownianSharp.AlignmentPaperMaternSpectralApproximation

theorem dyadicBandCellIntervals_sameBand_disjoint (j m : ℕ)
    {k l : Fin (2^(j+m))} (side : Fin 2) (hkl : k ≠ l) :
    Disjoint (Set.Ico (dyadicBandCellInterval j m k side).1
        (dyadicBandCellInterval j m k side).2)
      (Set.Ico (dyadicBandCellInterval j m l side).1
        (dyadicBandCellInterval j m l side).2) := by
  have hval : k.val ≠ l.val := fun heq => hkl (Fin.ext heq)
  have hden : 0 < (2:ℝ)^m := by positivity
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hstep : k.val + 1 ≤ l.val := Nat.succ_le_of_lt hlt
    have hcast : ((k.val+1:ℕ):ℝ) ≤ (l.val:ℝ) := by exact_mod_cast hstep
    have hfrac : ((k.val+1:ℕ):ℝ)/(2:ℝ)^m ≤ (l.val:ℝ)/(2:ℝ)^m :=
      (div_le_div_iff_of_pos_right hden).2 hcast
    push_cast at hfrac
    fin_cases side
    · have hend : (dyadicBandCellInterval j m k 0).2 ≤
          (dyadicBandCellInterval j m l 0).1 := by
        simp [dyadicBandCellInterval]
        linarith
      exact Set.disjoint_left.mpr fun x hxk hxl => by
        simp [dyadicBandCellInterval] at hxk hxl
        linarith [hxk.2, hxl.1, hend]
    · have hend : (dyadicBandCellInterval j m l 1).2 ≤
          (dyadicBandCellInterval j m k 1).1 := by
        simp [dyadicBandCellInterval]
        linarith
      exact Set.disjoint_left.mpr fun x hxk hxl => by
        simp [dyadicBandCellInterval] at hxk hxl
        linarith [hxk.1, hxl.2, hend]
  · have hstep : l.val + 1 ≤ k.val := Nat.succ_le_of_lt hgt
    have hcast : ((l.val+1:ℕ):ℝ) ≤ (k.val:ℝ) := by exact_mod_cast hstep
    have hfrac : ((l.val+1:ℕ):ℝ)/(2:ℝ)^m ≤ (k.val:ℝ)/(2:ℝ)^m :=
      (div_le_div_iff_of_pos_right hden).2 hcast
    push_cast at hfrac
    fin_cases side
    · have hend : (dyadicBandCellInterval j m l 0).2 ≤
          (dyadicBandCellInterval j m k 0).1 := by
        simp [dyadicBandCellInterval]
        linarith
      exact Set.disjoint_left.mpr fun x hxk hxl => by
        simp [dyadicBandCellInterval] at hxk hxl
        linarith [hxl.2, hxk.1, hend]
    · have hend : (dyadicBandCellInterval j m k 1).2 ≤
          (dyadicBandCellInterval j m l 1).1 := by
        simp [dyadicBandCellInterval]
        linarith
      exact Set.disjoint_left.mpr fun x hxk hxl => by
        simp [dyadicBandCellInterval] at hxk hxl
        linarith [hxk.2, hxl.1, hend]

private theorem disjoint_Ico_of_le {a b c d : ℝ} (h : b ≤ c) :
    Disjoint (Set.Ico a b) (Set.Ico c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (hx.2.trans_le (h.trans hy.1)).false

private theorem two_pow_mono_real {a b : ℕ} (hab : a ≤ b) :
    (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  pow_le_pow_right₀ (by norm_num) hab

theorem dyadicBandCellIntervals_distinctBand_disjoint
    {j l : ℕ} (hjl : j < l) (m r : ℕ)
    (k : Fin (2 ^ (j + m))) (v : Fin (2 ^ (l + r))) (side : Fin 2) :
    Disjoint (Set.Ico (dyadicBandCellInterval j m k side).1
      (dyadicBandCellInterval j m k side).2)
      (Set.Ico (dyadicBandCellInterval l r v side).1
      (dyadicBandCellInterval l r v side).2) := by
  have h₁ := dyadicBandCellInterval_bounds j m k side
  have h₂ := dyadicBandCellInterval_bounds l r v side
  have hgap : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ l :=
    two_pow_mono_real (Nat.succ_le_of_lt hjl)
  fin_cases side
  · norm_num at h₁ h₂
    exact disjoint_Ico_of_le (h₁.2.trans (hgap.trans h₂.1))
  · norm_num at h₁ h₂
    have hend : (dyadicBandCellInterval l r v 1).2 ≤
        (dyadicBandCellInterval j m k 1).1 := by
      linarith only [h₂.2, h₁.1, hgap]
    exact (disjoint_Ico_of_le hend).symm

theorem dyadicBandCellIntervals_distinctSide_disjoint
    (j l m r : ℕ) (k : Fin (2 ^ (j + m))) (v : Fin (2 ^ (l + r)))
    {side other : Fin 2} (hs : side ≠ other) :
    Disjoint (Set.Ico (dyadicBandCellInterval j m k side).1
      (dyadicBandCellInterval j m k side).2)
      (Set.Ico (dyadicBandCellInterval l r v other).1
      (dyadicBandCellInterval l r v other).2) := by
  have h₁ := dyadicBandCellInterval_bounds j m k side
  have h₂ := dyadicBandCellInterval_bounds l r v other
  have hp : 0 ≤ (2 : ℝ) ^ j := by positivity
  have hq : 0 ≤ (2 : ℝ) ^ l := by positivity
  fin_cases side <;> fin_cases other
  · exact (hs rfl).elim
  · norm_num at h₁ h₂
    have hend : (dyadicBandCellInterval l r v 1).2 ≤
        (dyadicBandCellInterval j m k 0).1 := by
      linarith only [h₁.1, h₂.2, hp, hq]
    exact (disjoint_Ico_of_le hend).symm
  · norm_num at h₁ h₂
    have hend : (dyadicBandCellInterval j m k 1).2 ≤
        (dyadicBandCellInterval l r v 0).1 := by
      linarith only [h₁.2, h₂.1, hp, hq]
    exact disjoint_Ico_of_le hend
  · exact (hs rfl).elim

theorem central_dyadicBandCellIntervals_disjoint
    (N j m : ℕ) (k : Fin (2 ^ N)) (v : Fin (2 ^ (j + m))) (side : Fin 2) :
    Disjoint (Set.Ico (centralDyadicCellInterval N k).1
      (centralDyadicCellInterval N k).2)
      (Set.Ico (dyadicBandCellInterval j m v side).1
      (dyadicBandCellInterval j m v side).2) := by
  have hc := centralDyadicCellInterval_bounds N k
  have hb := dyadicBandCellInterval_bounds j m v side
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  fin_cases side
  · norm_num at hb
    exact disjoint_Ico_of_le (hc.2.trans (hp.trans hb.1))
  · norm_num at hb
    have hend : (dyadicBandCellInterval j m v 1).2 ≤
        (centralDyadicCellInterval N k).1 := by
      linarith only [hb.2, hc.1, hp]
    exact (disjoint_Ico_of_le hend).symm

/-- All cells used by the actual finite Taylor level have disjoint supports. -/
theorem spectralLevelCellIntervals_pairwise_disjoint (N : ℕ)
    {a b : spectralLevelCellIndex N} (hab : a ≠ b) :
    Disjoint (Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2)
      (Set.Ico (spectralLevelCellInterval N b).1 (spectralLevelCellInterval N b).2) := by
  classical
  rcases a with ka | ⟨ja, sa, ka⟩ <;> rcases b with kb | ⟨jb, sb, kb⟩
  · exact centralDyadicCellIntervals_disjoint (fun h => hab (congrArg Sum.inl h))
  · exact central_dyadicBandCellIntervals_disjoint N jb.val ((N - jb.val) / 2) ka kb sb
  · exact (central_dyadicBandCellIntervals_disjoint N ja.val ((N - ja.val) / 2) kb ka sa).symm
  · by_cases hs : sa = sb
    · subst sb
      by_cases hj : ja = jb
      · subst jb
        have hk : ka ≠ kb := by
          intro hk
          subst kb
          exact hab rfl
        exact dyadicBandCellIntervals_sameBand_disjoint ja.val ((N-ja.val)/2) sa hk
      · have hval : ja.val ≠ jb.val := fun h => hj (Fin.ext h)
        rcases lt_or_gt_of_ne hval with hlt | hgt
        · exact dyadicBandCellIntervals_distinctBand_disjoint hlt
            ((N-ja.val)/2) ((N-jb.val)/2) ka kb sa
        · exact (dyadicBandCellIntervals_distinctBand_disjoint hgt
            ((N-jb.val)/2) ((N-ja.val)/2) kb ka sa).symm
    · exact dyadicBandCellIntervals_distinctSide_disjoint ja.val jb.val
        ((N-ja.val)/2) ((N-jb.val)/2) ka kb hs

private theorem bandPath_end (j m : ℕ) :
    (2 : ℝ) ^ j + ((2 ^ (j + m) : ℕ) : ℝ) / (2 : ℝ) ^ m =
      (2 : ℝ) ^ (j + 1) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_add, mul_div_cancel_right₀ _ (by positivity), pow_succ]
  ring

theorem centralDyadicCellIntervals_cover (N : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) :
    ∃ k : Fin (2 ^ N), x ∈ Set.Ico (centralDyadicCellInterval N k).1
      (centralDyadicCellInterval N k).2 := by
  let a : ℕ → ℝ := fun k => -1 + 2 * (k : ℝ) / (2 : ℝ) ^ N
  have hlast : a (2 ^ N) = 1 := by
    dsimp [a]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring
  have hx' : x ∈ Set.Ico (a 0) (a (2 ^ N)) := by simpa [a, hlast] using hx
  have hcov := Ico_subset_biUnion_Ico (2 ^ N) a hx'
  rcases Set.mem_iUnion.mp hcov with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hk, hxk⟩
  exact ⟨⟨k, Finset.mem_range.mp hk⟩, hxk⟩

theorem dyadicBandCellIntervals_positive_cover (j m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))) :
    ∃ k : Fin (2 ^ (j + m)), x ∈ Set.Ico (dyadicBandCellInterval j m k 0).1
      (dyadicBandCellInterval j m k 0).2 := by
  let a : ℕ → ℝ := fun k => (2 : ℝ) ^ j + (k : ℝ) / (2 : ℝ) ^ m
  have hlast : a (2 ^ (j + m)) = (2 : ℝ) ^ (j + 1) := bandPath_end j m
  have hx' : x ∈ Set.Ico (a 0) (a (2 ^ (j + m))) := by simpa [a, hlast] using hx
  have hcov := Ico_subset_biUnion_Ico (2 ^ (j + m)) a hx'
  rcases Set.mem_iUnion.mp hcov with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hk, hxk⟩
  refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
  simpa [a, dyadicBandCellInterval] using hxk

theorem dyadicBandCellIntervals_negative_cover (j m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (-((2 : ℝ) ^ (j + 1))) (-((2 : ℝ) ^ j))) :
    ∃ k : Fin (2 ^ (j + m)), x ∈ Set.Ico (dyadicBandCellInterval j m k 1).1
      (dyadicBandCellInterval j m k 1).2 := by
  let a : ℕ → ℝ := fun k => (2 : ℝ) ^ j + (k : ℝ) / (2 : ℝ) ^ m
  have hlast : a (2 ^ (j + m)) = (2 : ℝ) ^ (j + 1) := bandPath_end j m
  have hx' : -x ∈ Set.Ioc (a 0) (a (2 ^ (j + m))) := by
    rw [hlast]
    simp only [a, Nat.cast_zero, zero_div, add_zero, Set.mem_Ioc]
    constructor <;> linarith [hx.1, hx.2]
  have hcov := Ioc_subset_biUnion_Ioc (2 ^ (j + m)) a hx'
  rcases Set.mem_iUnion.mp hcov with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hk, hxk⟩
  refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
  simp only [dyadicBandCellInterval, Fin.val_one, one_ne_zero, ↓reduceIte, Set.mem_Ico]
  dsimp [a] at hxk
  constructor <;> linarith [hxk.1, hxk.2]

theorem spectralLevelCellInterval_subset (N : ℕ) (a : spectralLevelCellIndex N) :
    Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 ⊆
      Set.Ico (-((2 : ℝ) ^ (N + 1))) ((2 : ℝ) ^ (N + 1)) := by
  have hcut : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
  rcases a with k | ⟨j, side, k⟩
  · dsimp only [spectralLevelCellInterval]
    have hc := centralDyadicCellInterval_bounds N k
    apply Set.Ico_subset_Ico
    · linarith only [hc.1, hcut]
    · exact hc.2.trans hcut
  · have hb := dyadicBandCellInterval_bounds j.val ((N-j.val)/2) k side
    have hj : j.val + 1 ≤ N + 1 := j.isLt
    have hp := two_pow_mono_real hj
    have hjpos : 0 ≤ (2 : ℝ) ^ j.val := by positivity
    fin_cases side
    · norm_num at hb
      have hlo : -((2 : ℝ) ^ (N+1)) ≤
          (dyadicBandCellInterval j.val ((N-j.val)/2) k 0).1 := by
        linarith only [hb.1, hcut, hjpos]
      exact Set.Ico_subset_Ico hlo (hb.2.trans hp)
    · norm_num at hb
      have hlo : -((2 : ℝ) ^ (N+1)) ≤
          (dyadicBandCellInterval j.val ((N-j.val)/2) k 1).1 := by
        linarith only [hb.1, hp]
      have hhi : (dyadicBandCellInterval j.val ((N-j.val)/2) k 1).2 ≤
          (2 : ℝ) ^ (N+1) := by
        linarith only [hb.2, hcut, hjpos]
      exact Set.Ico_subset_Ico hlo hhi

theorem spectralLevelCellIntervals_cover (N : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (-((2 : ℝ) ^ (N+1))) ((2 : ℝ) ^ (N+1))) :
    ∃ a : spectralLevelCellIndex N,
      x ∈ Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 := by
  by_cases hneg : x < -1
  · have hz : -x ∈ Set.Ioc (1 : ℝ) ((2 : ℝ) ^ (N+1)) := by
      constructor <;> linarith only [hneg, hx.1]
    have hz' : -x ∈ Set.Ioc ((2 : ℝ)^0) ((2 : ℝ)^(N+1)) := by simpa using hz
    have hcov := Ioc_subset_biUnion_Ioc (N+1) (fun j => (2 : ℝ)^j) hz'
    rcases Set.mem_iUnion.mp hcov with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hj, hxj⟩
    have hj' : j < N+1 := Finset.mem_range.mp hj
    have hband : x ∈ Set.Ico (-((2 : ℝ)^(j+1))) (-((2 : ℝ)^j)) := by
      constructor <;> linarith only [hxj.1, hxj.2]
    obtain ⟨k, hk⟩ := dyadicBandCellIntervals_negative_cover j ((N-j)/2) hband
    exact ⟨Sum.inr ⟨⟨j,hj'⟩, 1, k⟩, hk⟩
  · by_cases hmid : x < 1
    · have hcent : x ∈ Set.Ico (-1 : ℝ) 1 := ⟨le_of_not_gt hneg, hmid⟩
      obtain ⟨k,hk⟩ := centralDyadicCellIntervals_cover N hcent
      exact ⟨Sum.inl k,hk⟩
    · have hz : x ∈ Set.Ico ((2 : ℝ)^0) ((2 : ℝ)^(N+1)) := by
        simpa using And.intro (le_of_not_gt hmid) hx.2
      have hcov := Ico_subset_biUnion_Ico (N+1) (fun j => (2 : ℝ)^j) hz
      rcases Set.mem_iUnion.mp hcov with ⟨j,hj⟩
      rcases Set.mem_iUnion.mp hj with ⟨hj,hxj⟩
      have hj' : j < N+1 := Finset.mem_range.mp hj
      obtain ⟨k,hk⟩ := dyadicBandCellIntervals_positive_cover j ((N-j)/2) hxj
      exact ⟨Sum.inr ⟨⟨j,hj'⟩, 0, k⟩,hk⟩

/-- Exact finite partition of the truncated real frequency line. -/
theorem spectralLevelCellIntervals_iUnion (N : ℕ) :
    (⋃ a : spectralLevelCellIndex N,
      Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2) =
        Set.Ico (-((2 : ℝ) ^ (N+1))) ((2 : ℝ) ^ (N+1)) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a,ha⟩
    exact spectralLevelCellInterval_subset N a ha
  · exact spectralLevelCellIntervals_cover N

end BrownianSharp.AlignmentPaperMaternSpectralApproximationPartition
