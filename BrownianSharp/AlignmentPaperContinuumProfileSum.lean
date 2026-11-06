import BrownianSharp.AlignmentPaperContinuumHulls
import BrownianSharp.AlignmentPaperContinuumShellBudgetScale
import BrownianSharp.AlignmentPaperContinuumResidual
import BrownianSharp.ShapeGrowth
import Mathlib.Tactic

/-! Grade definitions and bounds for bounded continuum hull profiles.
The regrouping inequality needed for the final variance bound is not proved
in this module. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperContinuumProfileSum

open BrownianSharp.AlignmentPaperContinuumHulls
open BrownianSharp.AlignmentPaperContinuumGoodRegion
open BrownianSharp.AlignmentPaperContinuumVariance
open BrownianSharp.AlignmentPaperContinuumResidual

def continuumProfileGrade {d : ℕ} (u : Fin d → ℕ) : ℕ :=
  ∑ i : Fin d, u i

/-- The shell contribution of one profile after multiplying its bound by the
exact continuum shell volume. -/
def continuumProfileShellTerm {d n : ℕ} (τ L : ℝ) (u : Fin d → ℕ) : ℝ :=
  if n ≤ continuumProfileGrade u then
    let h := continuumProfileGrade u - n
    τ ^ 2 / 2 * BrownianSharp.shapeOverlapCap d n h L ^ 2 *
      Real.exp (τ * BrownianSharp.shapeOverlapCap d n h L) *
      (1 / 2 : ℝ) ^ (continuumProfileGrade u + d)
  else 0

def continuumGradeEnvelope {d n : ℕ} (τ L : ℝ) (h : ℕ) : ℝ :=
  2 * τ ^ 2 * (L * (Nat.factorial (d - 1) : ℝ) *
      (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)) ^ 2 *
    Real.exp ((Real.log 2 / 2) * ((h : ℝ) + 1))

def continuumGradeShellEnvelope {d n : ℕ} (τ L : ℝ) (h : ℕ) : ℝ :=
  BrownianSharp.hyperbolicCount d (n + h) *
    (1 / 2 : ℝ) ^ (n + h + d) * continuumGradeEnvelope (d := d) (n := n) τ L h

private theorem continuumProfileGrade_lt {d N : ℕ} (hd : 0 < d)
    (u : BoundedHullProfile d N) : continuumProfileGrade u.1 < d * N := by
  unfold continuumProfileGrade
  calc
    (∑ i : Fin d, u.1 i) < ∑ _i : Fin d, N := by
      apply Finset.sum_lt_sum
      · intro i hi
        exact (u.2 i).le
      · exact ⟨⟨0, hd⟩, Finset.mem_univ _, u.2 ⟨0, hd⟩⟩
    _ = d * N := by simp

private theorem profile_term_le_grade_envelope {d n : ℕ} (hd : 2 ≤ d)
    {τ L κ : ℝ} (hτ : 0 ≤ τ) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hτbound : τ ≤ κ * ((n : ℝ) + 1))
    (u : Fin d → ℕ) (hn : n ≤ continuumProfileGrade u) :
    continuumProfileShellTerm (d := d) (n := n) τ L u ≤
      continuumGradeEnvelope (d := d) (n := n) τ L
        (continuumProfileGrade u - n) *
          (1 / 2 : ℝ) ^ (continuumProfileGrade u + d) := by
  let h := continuumProfileGrade u - n
  have hgrade : n + h = continuumProfileGrade u := Nat.add_sub_of_le hn
  have hfact : 0 < (Nat.factorial (d - 1) : ℝ) := by positivity
  have hden : 0 < (n : ℝ) + 1 := by positivity
  let r : ℝ := ((h : ℝ) + 1) / ((n : ℝ) + 1)
  let B : ℝ := L * (Nat.factorial (d - 1) : ℝ) * r ^ (d - 1)
  let A : ℝ := L * (Nat.factorial (d - 1) : ℝ) * r
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hcap0 : 0 ≤ BrownianSharp.shapeOverlapCap d n h L :=
    BrownianSharp.shapeOverlapCap_nonneg (by omega) n h hL.le
  have hcapB : BrownianSharp.shapeOverlapCap d n h L ≤ B := by
    simpa [B, r, div_pow] using
      (BrownianSharp.shapeOverlapCap_le_polynomial (by omega : 1 ≤ d) n h hL.le)
  have hcapA : BrownianSharp.shapeOverlapCap d n h L ≤ A := by
    simpa [A, r] using
      (BrownianSharp.shapeOverlapCap_le_linear hd n h hL.le)
  have hexp : τ * BrownianSharp.shapeOverlapCap d n h L ≤
      (Real.log 2 / 4) * ((h : ℝ) + 1) := by
    have hτA : τ * A ≤ (Real.log 2 / 4) * ((h : ℝ) + 1) := by
      have hκL : κ * (L * (Nat.factorial (d - 1) : ℝ)) ≤ Real.log 2 / 4 :=
        by
          have hκ' := (le_div_iff₀ (by positivity :
            (0 : ℝ) < 4 * L * (Nat.factorial (d - 1) : ℝ))).mp hκ
          nlinarith
      have hmul := mul_le_mul_of_nonneg_right hτbound (by positivity :
        0 ≤ L * (Nat.factorial (d - 1) : ℝ) * r)
      have hcancel : ((n : ℝ) + 1) * r = (h : ℝ) + 1 := by
        dsimp [r]
        field_simp
      dsimp [A]
      calc
        τ * (L * (Nat.factorial (d - 1) : ℝ) * r) ≤
            κ * ((n : ℝ) + 1) *
              (L * (Nat.factorial (d - 1) : ℝ) * r) := hmul
        _ = κ * (L * (Nat.factorial (d - 1) : ℝ)) * ((h : ℝ) + 1) := by
          rw [show κ * ((n : ℝ) + 1) *
              (L * (Nat.factorial (d - 1) : ℝ) * r) =
              κ * (L * (Nat.factorial (d - 1) : ℝ)) * (((n : ℝ) + 1) * r) by ring,
            hcancel]
        _ ≤ (Real.log 2 / 4) * ((h : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hκL (by positivity)
    exact (mul_le_mul_of_nonneg_left hcapA hτ).trans hτA
  have hexp' : Real.exp (τ * BrownianSharp.shapeOverlapCap d n h L) ≤
      Real.exp ((Real.log 2 / 2) * ((h : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hexp, hlog]
  have hcoef : τ ^ 2 / 2 * BrownianSharp.shapeOverlapCap d n h L ^ 2 ≤
      2 * τ ^ 2 * B ^ 2 := by
    have hsquare : BrownianSharp.shapeOverlapCap d n h L ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hcap0 hB0).2 hcapB
    nlinarith [sq_nonneg τ, hτ]
  unfold continuumProfileShellTerm
  rw [if_pos hn]
  change (τ ^ 2 / 2 * BrownianSharp.shapeOverlapCap d n
      (continuumProfileGrade u - n) L ^ 2 *
      Real.exp (τ * BrownianSharp.shapeOverlapCap d n
        (continuumProfileGrade u - n) L)) *
      (1 / 2 : ℝ) ^ (continuumProfileGrade u + d) ≤
    continuumGradeEnvelope (d := d) (n := n) τ L
      (continuumProfileGrade u - n) *
      (1 / 2 : ℝ) ^ (continuumProfileGrade u + d)
  rw [show continuumProfileGrade u - n = h by omega, ← hgrade]
  calc
    (τ ^ 2 / 2 * BrownianSharp.shapeOverlapCap d n h L ^ 2 *
        Real.exp (τ * BrownianSharp.shapeOverlapCap d n h L)) *
        (1 / 2 : ℝ) ^ (n + h + d) ≤
      (2 * τ ^ 2 * B ^ 2 *
        Real.exp ((Real.log 2 / 2) * ((h : ℝ) + 1))) *
        (1 / 2 : ℝ) ^ (n + h + d) := by
          have hprod :
              τ ^ 2 / 2 * BrownianSharp.shapeOverlapCap d n h L ^ 2 *
                  Real.exp (τ * BrownianSharp.shapeOverlapCap d n h L) ≤
                2 * τ ^ 2 * B ^ 2 *
                  Real.exp ((Real.log 2 / 2) * ((h : ℝ) + 1)) := by
            calc
              _ ≤ 2 * τ ^ 2 * B ^ 2 *
                    Real.exp (τ * BrownianSharp.shapeOverlapCap d n h L) :=
                mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
              _ ≤ 2 * τ ^ 2 * B ^ 2 *
                    Real.exp ((Real.log 2 / 2) * ((h : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hexp' (by positivity)
          exact mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = continuumGradeEnvelope (d := d) (n := n) τ L h *
        (1 / 2 : ℝ) ^ (n + h + d) := by
          simp [continuumGradeEnvelope, B, r]

open BrownianSharp.AlignmentPaperContinuumShellBudgetScale

/-- The bounded cutoff profile sum is dominated by the complete weak-
composition grade sum. Each bounded profile is assigned to its excess grade;
within a fixed grade it injects into the unrestricted continuum profiles. -/
theorem boundedProfile_shell_sum_le_grade_envelope
    {d n N : ℕ} (hd : 2 ≤ d) {τ L κ : ℝ}
    (hτ : 0 ≤ τ) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hτbound : τ ≤ κ * ((n : ℝ) + 1)) :
    (∑ u : BoundedHullProfile d N,
      continuumProfileShellTerm (d := d) (n := n) τ L u.1) ≤
      ∑ h ∈ Finset.range (d * N + 1),
        continuumGradeShellEnvelope (d := d) (n := n) τ L h := by
  classical
  let S : Finset (BoundedHullProfile d N) :=
    Finset.univ.filter (fun u => n ≤ continuumProfileGrade u.1)
  let gradeMap (u : BoundedHullProfile d N) : ℕ :=
    continuumProfileGrade u.1 - n
  have hsumFilter :
      (∑ u : BoundedHullProfile d N,
        continuumProfileShellTerm (d := d) (n := n) τ L u.1) =
      ∑ u ∈ S, continuumProfileShellTerm (d := d) (n := n) τ L u.1 := by
    calc
      _ = ∑ u ∈ (Finset.univ : Finset (BoundedHullProfile d N)),
          if n ≤ continuumProfileGrade u.1 then
            continuumProfileShellTerm (d := d) (n := n) τ L u.1 else 0 := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases hn : n ≤ continuumProfileGrade u.1
              · simp [hn]
              · have hzero : continuumProfileShellTerm
                    (d := d) (n := n) τ L u.1 = 0 := by
                  simp [continuumProfileShellTerm, hn]
                simp [hn, hzero]
      _ = ∑ u ∈ (Finset.univ.filter
          (fun u : BoundedHullProfile d N => n ≤ continuumProfileGrade u.1)),
            continuumProfileShellTerm (d := d) (n := n) τ L u.1 := by
              rw [Finset.sum_filter]
      _ = ∑ u ∈ S, continuumProfileShellTerm (d := d) (n := n) τ L u.1 := rfl
  have hmaps : (S : Set (BoundedHullProfile d N)).MapsTo gradeMap
      (Finset.range (d * N + 1)) := by
    intro u hu
    apply Finset.mem_range.mpr
    have hgrade := continuumProfileGrade_lt (by omega : 0 < d) u
    have hlow : n ≤ continuumProfileGrade u.1 := (Finset.mem_filter.mp hu).2
    dsimp [gradeMap]
    omega
  have hfiberwise :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun u : BoundedHullProfile d N =>
        continuumProfileShellTerm (d := d) (n := n) τ L u.1)
  rw [hsumFilter, ← hfiberwise]
  apply Finset.sum_le_sum
  intro h hh
  let F := S.filter (fun u => gradeMap u = h)
  have hgradeFiber (u : BoundedHullProfile d N) (hu : u ∈ F) :
      continuumProfileGrade u.1 = n + h := by
    have hmem := (Finset.mem_filter.mp hu).1
    have hgradeexcess := (Finset.mem_filter.mp hu).2
    have hn := (Finset.mem_filter.mp hmem).2
    dsimp [gradeMap] at hgradeexcess
    omega
  let e : F → ContinuumHullProfile d (n + h) := fun u =>
    ⟨u.1.1, hgradeFiber u.1 u.2⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ContinuumHullProfile d (n + h) => z.1) hab
  have hcard : (F.card : ℝ) ≤ BrownianSharp.hyperbolicCount d (n + h) := by
    have hcard' := Fintype.card_le_of_injective e he
    have hcard'' : F.card ≤ Fintype.card (ContinuumHullProfile d (n + h)) := by
      simpa using hcard'
    calc
      (F.card : ℝ) ≤ Fintype.card (ContinuumHullProfile d (n + h)) := by exact_mod_cast hcard''
      _ = BrownianSharp.hyperbolicCount d (n + h) := by
        rw [continuumHullProfile_card d (n + h) (by omega : 0 < d)]
        simp [BrownianSharp.hyperbolicCount]
  have hterm (u : BoundedHullProfile d N) (hu : u ∈ F) :
      continuumProfileShellTerm (d := d) (n := n) τ L u.1 ≤
        continuumGradeEnvelope (d := d) (n := n) τ L h *
          (1 / 2 : ℝ) ^ (n + h + d) := by
    have hlow : n ≤ continuumProfileGrade u.1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    have hh : continuumProfileGrade u.1 - n = h := by
      have hhgrade := hgradeFiber u hu
      omega
    simpa [hh, hgradeFiber u hu] using
      profile_term_le_grade_envelope hd hτ hL hκ hτbound u.1 hlow
  have hsum :
      (∑ u ∈ F, continuumProfileShellTerm (d := d) (n := n) τ L u.1) ≤
        (F.card : ℝ) *
          (continuumGradeEnvelope (d := d) (n := n) τ L h *
            (1 / 2 : ℝ) ^ (n + h + d)) := by
    calc
      _ ≤ ∑ u ∈ F,
          continuumGradeEnvelope (d := d) (n := n) τ L h *
            (1 / 2 : ℝ) ^ (n + h + d) := by
              apply Finset.sum_le_sum
              intro u hu
              exact hterm u hu
      _ = (F.card : ℝ) *
          (continuumGradeEnvelope (d := d) (n := n) τ L h *
            (1 / 2 : ℝ) ^ (n + h + d)) := by simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ u ∈ F, continuumProfileShellTerm (d := d) (n := n) τ L u.1) ≤
      (F.card : ℝ) *
        (continuumGradeEnvelope (d := d) (n := n) τ L h *
          (1 / 2 : ℝ) ^ (n + h + d)) := hsum
    _ ≤ BrownianSharp.hyperbolicCount d (n + h) *
        (continuumGradeEnvelope (d := d) (n := n) τ L h *
          (1 / 2 : ℝ) ^ (n + h + d)) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (by
        unfold continuumGradeEnvelope
        positivity) (by positivity))
    _ = continuumGradeShellEnvelope (d := d) (n := n) τ L h := by
      simp [continuumGradeShellEnvelope, mul_assoc, mul_comm, mul_left_comm]

/-- The grouped actual bounded-profile shell sum is controlled by the
dimension-only continuum shell budget at the literal layer scale. -/
theorem boundedProfile_shell_sum_le_layer_card
    {d n N : ℕ} (hd : 2 ≤ d) {τ L κ : ℝ}
    (hτ : 0 ≤ τ) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hτbound : τ ≤ κ * ((n : ℝ) + 1)) :
    (∑ u : BoundedHullProfile d N,
      continuumProfileShellTerm (d := d) (n := n) τ L u.1) ≤
      continuumShellConstant d L * τ ^ 2 /
        ((2 : ℝ) ^ n * BrownianSharp.hyperbolicCount d n) := by
  calc
    (∑ u : BoundedHullProfile d N,
      continuumProfileShellTerm (d := d) (n := n) τ L u.1) ≤
        ∑ h ∈ Finset.range (d * N + 1),
          continuumGradeShellEnvelope (d := d) (n := n) τ L h :=
      boundedProfile_shell_sum_le_grade_envelope hd hτ hL hκ hτbound
    _ ≤ continuumShellConstant d L * τ ^ 2 /
        ((2 : ℝ) ^ n * BrownianSharp.hyperbolicCount d n) := by
      convert continuum_grade_partial_sum_le_layer_card (by omega : 1 ≤ d) n (d * N) τ L using 1 <;>
        simp [continuumGradeShellEnvelope, continuumGradeEnvelope,
          continuumShellConstant, mul_assoc, mul_comm, mul_left_comm]

/-- The profile shell sum is exactly the actual weighted remainder shell sum
used by the variance estimate. -/
theorem boundedProfile_actual_shell_sum_eq
    {d n N : ℕ} (τ L : ℝ) :
    (∑ u : BoundedHullProfile d N,
      continuumProfileShellTerm (d := d) (n := n) τ L u.1) =
    (∑ u : BoundedHullProfile d N,
      continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
        (((cubeLebesgue d).prod (cubeLebesgue d)).real
          (spatialPairHullShell u.1))) := by
  classical
  apply Finset.sum_congr rfl
  intro u hu
  have hmeasure : (((cubeLebesgue d).prod (cubeLebesgue d)).real
      (spatialPairHullShell u.1)) =
      (1 / 2 : ℝ) ^ (continuumProfileGrade u.1 + d) := by
    rw [Measure.real_def, spatialPairHullShell_measure,
      tensorOppositeHullShell_measure_eq u.1]
    rw [ENNReal.toReal_ofReal]
    simp [continuumProfileGrade]
    positivity
  simp [continuumProfileShellTerm, continuumShellRemainderBound,
    continuumProfileGrade, hmeasure]

/-- Actual variance-ready shell bound, with the finite cutoff sum grouped by
complete profile grades. -/
theorem boundedProfile_actual_shell_sum_le_layer_card
    {d n N : ℕ} (hd : 2 ≤ d) {τ L κ : ℝ}
    (hτ : 0 ≤ τ) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hτbound : τ ≤ κ * ((n : ℝ) + 1)) :
    (∑ u : BoundedHullProfile d N,
      continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
        (((cubeLebesgue d).prod (cubeLebesgue d)).real
          (spatialPairHullShell u.1))) ≤
      continuumShellConstant d L * τ ^ 2 /
        ((2 : ℝ) ^ n * BrownianSharp.hyperbolicCount d n) := by
  rw [← boundedProfile_actual_shell_sum_eq]
  exact boundedProfile_shell_sum_le_layer_card hd hτ hL hκ hτbound

end BrownianSharp.AlignmentPaperContinuumProfileSum
