import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.NativeLayerThetaBudget
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalWeightedGrades

open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.NativeLayerThetaBudget

/-- Active-coordinate depths, truncated to a finite box. -/
abbrev ActiveBox (ν M : ℕ) := Fin ν → Fin (M + 1)

/-- Inactive-coordinate depths, truncated to the same box. -/
abbrev InactiveBox (e M : ℕ) := Fin e → Fin (M + 1)

def activeGradeNat {ν M : ℕ} (a : ActiveBox ν M) : ℕ :=
  ∑ i : Fin ν, (a i).val

def inactiveWeightedGrade {e M : ℕ} (w : Fin e → ℝ)
    (b : InactiveBox e M) : ℝ :=
  ∑ j : Fin e, w j * ((b j).val : ℝ)

def inactiveDepth {e M : ℕ} (b : InactiveBox e M) : ℝ :=
  ∑ j : Fin e, ((b j).val : ℝ)

def inactivePenaltyExponent {e M : ℕ} (w : Fin e → ℝ)
    (b : InactiveBox e M) : ℝ :=
  ∑ j : Fin e, (w j - 1) * ((b j).val : ℝ)

def inactiveEnergyExponent {e M : ℕ} (r : ℝ) (w : Fin e → ℝ)
    (b : InactiveBox e M) : ℝ :=
  ∑ j : Fin e, (2 * r * w j - 1) * ((b j).val : ℝ)

def inactiveFloor {e M : ℕ} (w : Fin e → ℝ)
    (b : InactiveBox e M) : ℕ := Nat.floor (inactiveWeightedGrade w b)

def weightedGradeFloor {ν e M : ℕ} (w : Fin e → ℝ)
    (a : ActiveBox ν M) (b : InactiveBox e M) : ℕ :=
  Nat.floor ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b)

def activeSlabFiber {ν e M : ℕ} (w : Fin e → ℝ) (n : ℕ)
    (b : InactiveBox e M) : Finset (ActiveBox ν M) :=
  Finset.univ.filter (fun a => activeGradeNat a + inactiveFloor w b = n)

def inactivePenalty {e M : ℕ} (q : Fin e → ℝ)
    (b : InactiveBox e M) : ℝ :=
  ∏ j : Fin e, q j ^ (b j).val

/-- Adding the integer active grade inside a real floor simply shifts the
inactive weighted floor. -/
theorem weightedGradeFloor_eq_active_add_inactiveFloor
    {ν e M : ℕ} (w : Fin e → ℝ) (hw : ∀ j, 0 ≤ w j)
    (a : ActiveBox ν M) (b : InactiveBox e M) :
    weightedGradeFloor w a b = activeGradeNat a + inactiveFloor w b := by
  unfold weightedGradeFloor inactiveFloor
  calc
    Nat.floor ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b) =
        Nat.floor (inactiveWeightedGrade w b + (activeGradeNat a : ℝ)) := by
          congr 1
          ring
    _ = Nat.floor (inactiveWeightedGrade w b) + activeGradeNat a :=
      Nat.floor_add_natCast
        (Finset.sum_nonneg fun j hj => mul_nonneg (hw j) (Nat.cast_nonneg _)) _
    _ = activeGradeNat a + Nat.floor (inactiveWeightedGrade w b) := Nat.add_comm _ _

/-- For a fixed inactive profile, at most `(n+1)^(ν-1)` active profiles
fall into a weighted grade-`n` slab. -/
theorem activeSlabFiber_card_le_power
    {ν e M n : ℕ} (hν : 0 < ν) (w : Fin e → ℝ)
    (b : InactiveBox e M) :
    (activeSlabFiber (ν := ν) w n b).card ≤ (n + 1)^(ν - 1) := by
  classical
  let q := inactiveFloor w b
  by_cases hqn : q ≤ n
  · let g := n - q
    let S : Finset (Fin ν → ℕ) :=
      Fintype.piFinset (fun _ : Fin ν => Finset.range (g + 1))
    let R : Finset (Fin ν → ℕ) :=
      (activeSlabFiber (ν := ν) w n b).image (fun a i => (a i).val)
    have hRcard : R.card = (activeSlabFiber (ν := ν) w n b).card := by
      dsimp [R]
      apply Finset.card_image_of_injective
      intro a a' haa
      funext i
      exact Fin.ext (congrFun haa i)
    have hRsub : R ⊆ S.filter (fun z => (∑ i : Fin ν, z i) = g) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨a,ha,hz⟩
      subst z
      simp only [Finset.mem_filter, S, Fintype.mem_piFinset]
      constructor
      · intro i
        have hgrade : activeGradeNat a + q = n := by
          simpa [activeSlabFiber, q] using (Finset.mem_filter.mp ha).2
        have hgrade' : activeGradeNat a = g := by
          dsimp [g]
          omega
        have hi : (a i).val ≤ g := by
          calc
            (a i).val ≤ ∑ j : Fin ν, (a j).val :=
              Finset.single_le_sum (f := fun j : Fin ν => (a j).val)
                (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
            _ = g := hgrade'
        simp only [Finset.mem_range]
        omega
      ·
        have hgrade : activeGradeNat a + q = n := by
          simpa [activeSlabFiber, q] using (Finset.mem_filter.mp ha).2
        have hgrade' : activeGradeNat a = g := by
          dsimp [g]
          omega
        simpa [activeGradeNat] using hgrade'
    have hshape := shape_grade_card_le_power_pred hν S g
    have hgradeBound : g ≤ n := by
      dsimp [g]
      omega
    calc
      (activeSlabFiber (ν := ν) w n b).card = R.card := hRcard.symm
      _ ≤ (S.filter (fun z => (∑ i : Fin ν, z i) = g)).card := Finset.card_le_card hRsub
      _ ≤ (g + 1)^(ν - 1) := hshape
      _ ≤ (n + 1)^(ν - 1) := by gcongr
  · have hempty : activeSlabFiber (ν := ν) w n b = ∅ := by
      ext a
      simp [activeSlabFiber]
      intro h
      apply hqn
      dsimp [q]
      omega
    simp [hempty]

/-- The finite box sum of an inactive geometric penalty is bounded by the
product of the full one-coordinate geometric budgets. -/
theorem inactivePenalty_box_sum_le
    {e M : ℕ} (q : Fin e → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j < 1) :
    (∑ b : InactiveBox e M, inactivePenalty q b) ≤
      ∏ j : Fin e, (1 - q j)⁻¹ := by
  classical
  have hfactor :
      (∑ b : InactiveBox e M, inactivePenalty q b) =
        ∏ j : Fin e, ∑ k : Fin (M + 1), q j ^ k.val := by
    dsimp [inactivePenalty, InactiveBox]
    simpa using (Finset.sum_prod_piFinset
      (s := (Finset.univ : Finset (Fin (M + 1))))
      (g := fun (j : Fin e) (k : Fin (M + 1)) => q j ^ k.val))
  rw [hfactor]
  apply Finset.prod_le_prod₀
  · intro j hj
    exact (Finset.sum_nonneg fun k hk => pow_nonneg (hq0 j) _)
  · intro j hj
    have hnorm : ‖q j‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 j)]
      exact hq1 j
    have hgeom := (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum
      (s := Finset.range (M + 1)) (by
        intro k hk
        exact pow_nonneg (hq0 j) _)
    rw [tsum_geometric_of_lt_one (hq0 j) (hq1 j)] at hgeom
    have hsum : (∑ k : Fin (M + 1), q j ^ k.val) =
        ∑ k ∈ Finset.range (M + 1), q j ^ k := by
      simp only [Fin.sum_univ_eq_sum_range]
    rw [hsum]
    exact hgeom

/-- Weighted slab count with its inactive geometric penalty. All constants
are uniform in both the slab index and the finite depth box. -/
theorem weightedSlabPenalty_sum_le
    {ν e M n : ℕ} (hν : 0 < ν) (w q : Fin e → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) :
    (∑ b : InactiveBox e M,
      ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          inactivePenalty q b else 0) ≤
      ((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - q j)⁻¹ := by
  classical
  have hinner (b : InactiveBox e M) :
      (∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          inactivePenalty q b else 0) =
        ((activeSlabFiber (ν := ν) w n b).card : ℝ) * inactivePenalty q b := by
    rw [← Finset.sum_filter]
    simp [activeSlabFiber, mul_comm]
  calc
    _ = ∑ b : InactiveBox e M,
        ((activeSlabFiber (ν := ν) w n b).card : ℝ) * inactivePenalty q b := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hinner b
    _ ≤ ∑ b : InactiveBox e M,
        (((n + 1 : ℕ) : ℝ)^(ν - 1)) * inactivePenalty q b := by
          apply Finset.sum_le_sum
          intro b hb
          have hcard := activeSlabFiber_card_le_power (ν := ν) (n := n) hν w b
          have hpen : 0 ≤ inactivePenalty q b := by
            dsimp [inactivePenalty]
            apply Finset.prod_nonneg
            intro j hj
            exact pow_nonneg (hq0 j) _
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpen
    _ = (((n + 1 : ℕ) : ℝ)^(ν - 1)) *
          (∑ b : InactiveBox e M, inactivePenalty q b) := by
            rw [Finset.mul_sum]
    _ ≤ (((n + 1 : ℕ) : ℝ)^(ν - 1)) *
          ∏ j : Fin e, (1 - q j)⁻¹ := by
            apply mul_le_mul_of_nonneg_left (inactivePenalty_box_sum_le q hq0 hq1)
            positivity

/-- On a slab of weighted grade `n`, the ordinary dimension exponent is at
most `n+1` after charging the inactive-coordinate penalty. -/
theorem weighted_dimension_exponent_with_penalty
    {ν e M n : ℕ} (w : Fin e → ℝ) (_hw : ∀ j, 1 ≤ w j)
    (a : ActiveBox ν M) (b : InactiveBox e M)
    (hgrade : weightedGradeFloor w a b = n) :
    (activeGradeNat a : ℝ) + inactiveDepth b + inactivePenaltyExponent w b ≤ n + 1 := by
  have hfloor : Nat.floor ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b) = n := by
    simpa [weightedGradeFloor] using hgrade
  have hlt := Nat.lt_floor_add_one ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b)
  rw [hfloor] at hlt
  have hidentity :
      (activeGradeNat a : ℝ) + inactiveDepth b + inactivePenaltyExponent w b =
        (activeGradeNat a : ℝ) + inactiveWeightedGrade w b := by
    have hsum : inactiveDepth b + inactivePenaltyExponent w b =
        inactiveWeightedGrade w b := by
      unfold inactiveDepth inactivePenaltyExponent inactiveWeightedGrade
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    linarith
  rw [hidentity]
  exact hlt.le

/-- The variance exponent on the same slab dominates the target isotropic
ninety-percent exponent and the identical inactive penalty. -/
theorem weighted_energy_exponent_with_penalty
    {ν e M n : ℕ} {r : ℝ} (hr : 1 / 2 < r) (w : Fin e → ℝ)
    (hw : ∀ j, 1 ≤ w j) (a : ActiveBox ν M) (b : InactiveBox e M)
    (hgrade : weightedGradeFloor w a b = n) :
    (2 * r - 1) * n + inactivePenaltyExponent w b ≤
      (2 * r - 1) * activeGradeNat a + inactiveEnergyExponent r w b := by
  have hfloor : Nat.floor ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b) = n := by
    simpa [weightedGradeFloor] using hgrade
  have htotal_nonneg : 0 ≤ (activeGradeNat a : ℝ) + inactiveWeightedGrade w b := by
    apply add_nonneg
    · exact_mod_cast Nat.zero_le (activeGradeNat a)
    · unfold inactiveWeightedGrade
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw j))
        (Nat.cast_nonneg _)
  have htotal : (n : ℝ) ≤ (activeGradeNat a : ℝ) + inactiveWeightedGrade w b := by
    have hf := Nat.floor_le htotal_nonneg
    rw [hfloor] at hf
    exact hf
  have hidentity :
      (2 * r - 1) * activeGradeNat a + inactiveEnergyExponent r w b =
        (2 * r - 1) * ((activeGradeNat a : ℝ) + inactiveWeightedGrade w b) +
          inactivePenaltyExponent w b := by
    have hsum : inactiveEnergyExponent r w b =
        (2 * r - 1) * inactiveWeightedGrade w b + inactivePenaltyExponent w b := by
      unfold inactiveEnergyExponent inactivePenaltyExponent inactiveWeightedGrade
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring
  have hβ : 0 ≤ 2 * r - 1 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left htotal hβ
  rw [hidentity]
  linarith

/-- Exponentiating the dimension profile gives the scale `2^(n+1)` and the
inactive-coordinate geometric penalty. -/
theorem weighted_dimension_power_with_penalty
    {ν e M n : ℕ} (w : Fin e → ℝ) (hw : ∀ j, 1 ≤ w j)
    (a : ActiveBox ν M) (b : InactiveBox e M)
    (hgrade : weightedGradeFloor w a b = n) :
    Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) ≤
      Real.rpow 2 (n + 1) * Real.rpow 2 (-inactivePenaltyExponent w b) := by
  have h := weighted_dimension_exponent_with_penalty w hw a b hgrade
  calc
    Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) ≤
        Real.rpow 2 ((n + 1) - inactivePenaltyExponent w b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = Real.rpow 2 (n + 1) * Real.rpow 2 (-inactivePenaltyExponent w b) := by
      calc
        Real.rpow 2 ((n + 1) - inactivePenaltyExponent w b) =
            Real.rpow 2 ((n + 1) + (-inactivePenaltyExponent w b)) := by
              congr 1
        _ = Real.rpow 2 (n + 1) * Real.rpow 2 (-inactivePenaltyExponent w b) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _

/-- Exponentiating the variance profile gives the row-energy bound at the
target smoothness, with the same geometric penalty. -/
theorem weighted_energy_power_with_penalty
    {ν e M n : ℕ} {r : ℝ} (hr : 1 / 2 < r) (w : Fin e → ℝ)
    (hw : ∀ j, 1 ≤ w j) (a : ActiveBox ν M) (b : InactiveBox e M)
    (hgrade : weightedGradeFloor w a b = n) :
    Real.rpow 2 (-((2 * r - 1) * activeGradeNat a + inactiveEnergyExponent r w b)) ≤
      Real.rpow 2 (-(2 * r - 1) * n) * Real.rpow 2 (-inactivePenaltyExponent w b) := by
  have h := weighted_energy_exponent_with_penalty hr w hw a b hgrade
  calc
    Real.rpow 2 (-((2 * r - 1) * activeGradeNat a + inactiveEnergyExponent r w b)) ≤
        Real.rpow 2 (-((2 * r - 1) * n + inactivePenaltyExponent w b)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = Real.rpow 2 (-(2 * r - 1) * n) * Real.rpow 2 (-inactivePenaltyExponent w b) := by
      calc
        Real.rpow 2 (-((2 * r - 1) * n + inactivePenaltyExponent w b)) =
            Real.rpow 2 (-(2 * r - 1) * n + (-inactivePenaltyExponent w b)) := by
              congr 1 <;> ring
        _ = Real.rpow 2 (-(2 * r - 1) * n) * Real.rpow 2 (-inactivePenaltyExponent w b) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _

/-- The penalty factor is exactly the product of the inactive coordinate
geometric weights used in `inactivePenalty_box_sum_le`. -/
theorem inactivePenalty_rpow_eq
    {e M : ℕ} (w : Fin e → ℝ) (b : InactiveBox e M) :
    inactivePenalty (fun j => Real.rpow 2 (-(w j - 1))) b =
      Real.rpow 2 (-inactivePenaltyExponent w b) := by
  unfold inactivePenalty inactivePenaltyExponent
  calc
    ∏ j : Fin e, (Real.rpow 2 (-(w j - 1))) ^ (b j).val =
        ∏ j : Fin e, Real.rpow 2 (-((w j - 1) * ((b j).val : ℝ))) := by
          apply Finset.prod_congr rfl
          intro j hj
          calc
            (Real.rpow 2 (-(w j - 1))) ^ (b j).val =
                Real.rpow (Real.rpow 2 (-(w j - 1))) ((b j).val : ℝ) :=
              (Real.rpow_natCast _ _).symm
            _ = Real.rpow 2 (-(w j - 1) * ((b j).val : ℝ)) :=
              (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
            _ = Real.rpow 2 (-((w j - 1) * ((b j).val : ℝ))) := by
              congr 1 <;> ring
    _ = Real.rpow 2 (∑ j : Fin e, -((w j - 1) * ((b j).val : ℝ))) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)
        (fun j : Fin e => -((w j - 1) * ((b j).val : ℝ))) Finset.univ).symm
    _ = Real.rpow 2 (-∑ j : Fin e, (w j - 1) * ((b j).val : ℝ)) := by
      congr 1
      rw [Finset.sum_neg_distrib]

/-- Summed dimension weights on a weighted slab have the polynomial profile
`2^n (n+1)^(ν-1)`, up to the finite inactive geometric budget. -/
theorem weighted_dimension_slab_sum_le
    {ν e M n : ℕ} (hν : 0 < ν) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j)
    :
    (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
      if activeGradeNat a + inactiveFloor w b = n then
        Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) else 0) ≤
      Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
  have hq0 : ∀ j, 0 ≤ Real.rpow 2 (-(w j - 1)) := by
    intro j
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hq1 : ∀ j, Real.rpow 2 (-(w j - 1)) < 1 := by
    intro j
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
  let q : Fin e → ℝ := fun j => Real.rpow 2 (-(w j - 1))
  let scale : ℝ := Real.rpow 2 (n + 1)
  have hpen (b : InactiveBox e M) :
      inactivePenalty q b = Real.rpow 2 (-inactivePenaltyExponent w b) := by
    exact inactivePenalty_rpow_eq w b
  have hsum :
      (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) else 0) ≤
        scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          if activeGradeNat a + inactiveFloor w b = n then
            inactivePenalty q b else 0) := by
    calc
      _ ≤ ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          scale * (if activeGradeNat a + inactiveFloor w b = n then
            inactivePenalty q b else 0) := by
            apply Finset.sum_le_sum
            intro b hb
            apply Finset.sum_le_sum
            intro a ha
            by_cases hgrade : activeGradeNat a + inactiveFloor w b = n
            · have hfloor : weightedGradeFloor w a b = n := by
                rw [weightedGradeFloor_eq_active_add_inactiveFloor w
                  (fun j => le_trans (by norm_num) (le_of_lt (hw j)))]
                exact hgrade
              have hprofile := weighted_dimension_power_with_penalty w
                (fun j => le_trans (by norm_num) (le_of_lt (hw j))) a b hfloor
              rw [← hpen b] at hprofile
              simpa [scale, hgrade] using hprofile
            · simp [hgrade, scale]
      _ = scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
            if activeGradeNat a + inactiveFloor w b = n then
              inactivePenalty q b else 0) := by
            symm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum]
  have hcount := weightedSlabPenalty_sum_le (ν := ν) (M := M) (n := n)
    hν w q hq0 hq1
  calc
    _ ≤ scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          inactivePenalty q b else 0) := hsum
    _ ≤ scale * ((((n + 1 : ℕ) : ℝ)^(ν - 1)) *
        ∏ j : Fin e, (1 - q j)⁻¹) := by
          apply mul_le_mul_of_nonneg_left hcount
          exact Real.rpow_nonneg (by norm_num) _
    _ = Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
          simp [scale, q]

/-- Summed row energies on a weighted slab have the profile
`2^(-(2r-1)n) (n+1)^(ν-1)`, up to the same finite inactive geometric
budget. -/
theorem weighted_energy_slab_sum_le
    {ν e M n : ℕ} (hν : 0 < ν) {r : ℝ} (hr : 1 / 2 < r)
    (w : Fin e → ℝ) (hw : ∀ j, 1 < w j)
    :
    (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
      if activeGradeNat a + inactiveFloor w b = n then
        Real.rpow 2 (-((2 * r - 1) * activeGradeNat a +
          inactiveEnergyExponent r w b)) else 0) ≤
      Real.rpow 2 (-(2 * r - 1) * n) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
  have hq0 : ∀ j, 0 ≤ Real.rpow 2 (-(w j - 1)) := by
    intro j
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hq1 : ∀ j, Real.rpow 2 (-(w j - 1)) < 1 := by
    intro j
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
  let q : Fin e → ℝ := fun j => Real.rpow 2 (-(w j - 1))
  let scale : ℝ := Real.rpow 2 (-(2 * r - 1) * n)
  have hpen (b : InactiveBox e M) :
      inactivePenalty q b = Real.rpow 2 (-inactivePenaltyExponent w b) := by
    exact inactivePenalty_rpow_eq w b
  have hsum :
      (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          Real.rpow 2 (-((2 * r - 1) * activeGradeNat a +
            inactiveEnergyExponent r w b)) else 0) ≤
        scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          if activeGradeNat a + inactiveFloor w b = n then
            inactivePenalty q b else 0) := by
    calc
      _ ≤ ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          scale * (if activeGradeNat a + inactiveFloor w b = n then
            inactivePenalty q b else 0) := by
            apply Finset.sum_le_sum
            intro b hb
            apply Finset.sum_le_sum
            intro a ha
            by_cases hgrade : activeGradeNat a + inactiveFloor w b = n
            · have hfloor : weightedGradeFloor w a b = n := by
                rw [weightedGradeFloor_eq_active_add_inactiveFloor w
                  (fun j => le_trans (by norm_num) (le_of_lt (hw j)))]
                exact hgrade
              have hprofile := weighted_energy_power_with_penalty hr w
                (fun j => le_trans (by norm_num) (le_of_lt (hw j))) a b hfloor
              rw [← hpen b] at hprofile
              simpa [scale, hgrade] using hprofile
            · simp [hgrade, scale]
      _ = scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
            if activeGradeNat a + inactiveFloor w b = n then
              inactivePenalty q b else 0) := by
            symm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum]
  have hcount := weightedSlabPenalty_sum_le (ν := ν) (M := M) (n := n)
    hν w q hq0 hq1
  calc
    _ ≤ scale * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          inactivePenalty q b else 0) := hsum
    _ ≤ scale * ((((n + 1 : ℕ) : ℝ)^(ν - 1)) *
        ∏ j : Fin e, (1 - q j)⁻¹) := by
          apply mul_le_mul_of_nonneg_left hcount
          exact Real.rpow_nonneg (by norm_num) _
    _ = Real.rpow 2 (-(2 * r - 1) * n) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
          simp [scale, q]

end BrownianSharp.AlignmentFractionalWeightedGrades
