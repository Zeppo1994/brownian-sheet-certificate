import BrownianSharp.AlignmentPaperJointGlobalRankProfile
import BrownianSharp.AlignmentPaperGlobalGradeTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A uniform bound for the high-grade radius profile, independent of the
finite window length. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointHighRadiusProfileSum

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperGlobalGradeTail
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-- The high-grade profile is summable uniformly over all finite windows. -/
theorem exists_high_radius_profile_sum_bound {p b : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ,
      (∑ j : Fin W,
        (2 : ℝ) ^ (-((1 - 1 / p) * (j.val + 1 : ℝ))) *
          Real.exp (highProfileEta p * (j.val + 1 : ℝ) / p) *
          (j.val + 2 : ℝ) ^ b) ≤ C := by
  have hp0 : 0 < p := by linarith
  let α : ℝ := 1 - 1 / p
  let η : ℝ := highProfileEta p
  let δ : ℝ := α * Real.log 2 - η / p
  have hα : 0 < α := by
    dsimp [α]
    have hrecip : 1 / p < 1 := (div_lt_one hp0).2 (by linarith)
    linarith
  have hη : η = α / 8 := by
    dsimp [η, α, highProfileEta]
    field_simp
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hloggap : 0 < Real.log 2 - 1 / (8 * p) := by
    have hsmall : 1 / (8 * p) < 1 / 8 := by
      apply (div_lt_iff₀ (by positivity : 0 < 8 * p)).2
      nlinarith
    linarith
  have hδfactor : δ = α * (Real.log 2 - 1 / (8 * p)) := by
    dsimp [δ]
    rw [hη]
    dsimp [α]
    ring
  have hδ : 0 < δ := by rw [hδfactor]; exact mul_pos hα hloggap
  obtain ⟨H, hH, htail⟩ := polynomial_exp_tail_le hδ hb
  let C : ℝ := (2 : ℝ) ^ b * H
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro W
  let g : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ b * Real.exp (-δ * (n : ℝ))
  have hg : Summable g := by
    let k : ℕ := Nat.ceil b
    have hk : b ≤ (k : ℝ) := by dsimp [k]; exact Nat.le_ceil b
    have hmaj : Summable (fun n : ℕ =>
        (n + 1 : ℝ) ^ k * Real.exp (-δ * (n : ℝ))) := by
      simpa [mul_comm, k] using summable_succ_pow_exp (k := k) hδ
    apply Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => ?_) hmaj
    have hbase : 1 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
    have hpoly := Real.rpow_le_rpow_of_exponent_le hbase hk
    calc
      g n = (n + 1 : ℝ)^b * Real.exp (-δ * (n : ℝ)) := rfl
      _ ≤ (n + 1 : ℝ)^(k : ℝ) * Real.exp (-δ * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = (n + 1 : ℝ)^k * Real.exp (-δ * (n : ℝ)) := by
        rw [Real.rpow_natCast]
  have hterm (j : Fin W) :
      (2 : ℝ) ^ (-((1 - 1 / p) * (j.val + 1 : ℝ))) *
          Real.exp (η * (j.val + 1 : ℝ) / p) *
          (j.val + 2 : ℝ) ^ b ≤ (2 : ℝ)^b * g j.val := by
    let m : ℝ := (j.val + 1 : ℝ)
    have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast Nat.le_add_left 1 j.val
    have hpolybase : (j.val + 2 : ℝ) ≤ 2 * m := by
      dsimp [m]
      nlinarith [show 0 ≤ (j.val : ℝ) by positivity]
    have hpoly : (j.val + 2 : ℝ) ^ b ≤ (2 : ℝ) ^ b * m ^ b := by
      calc
        (j.val + 2 : ℝ) ^ b ≤ (2 * m) ^ b := Real.rpow_le_rpow (by positivity) hpolybase hb
        _ = (2 : ℝ) ^ b * m ^ b := by
          rw [Real.mul_rpow (by norm_num) (by positivity : 0 ≤ m)]
    have hpowexp : (2 : ℝ) ^ (- (α * m)) * Real.exp (η * m / p) =
        Real.exp (-δ * m) := by
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
      rw [← Real.exp_add]
      congr 1
      dsimp [δ]
      ring
    have hmplus : (j.val + 2 : ℝ) = m + 1 := by
      dsimp [m]
      ring
    have hexpstep : Real.exp (-δ * m) ≤ Real.exp (-δ * (j.val : ℝ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [m]
      nlinarith [hδ]
    calc
      (2 : ℝ) ^ (-((1 - 1 / p) * (j.val + 1 : ℝ))) *
          Real.exp (η * (j.val + 1 : ℝ) / p) * (j.val + 2 : ℝ)^b =
          Real.exp (-δ * m) * (j.val + 2 : ℝ)^b := by
            dsimp [m, α]
            rw [hpowexp]
      _ ≤ Real.exp (-δ * m) * ((2 : ℝ)^b * m^b) :=
            mul_le_mul_of_nonneg_left (by simpa [hmplus] using hpoly)
              (Real.exp_pos _).le
      _ ≤ (2 : ℝ)^b * (m^b * Real.exp (-δ * (j.val : ℝ))) := by
            calc
              Real.exp (-δ * m) * ((2 : ℝ)^b * m^b) ≤
                  Real.exp (-δ * (j.val : ℝ)) * ((2 : ℝ)^b * m^b) :=
                mul_le_mul_of_nonneg_right hexpstep (by positivity)
              _ = (2 : ℝ)^b * (m^b * Real.exp (-δ * (j.val : ℝ))) := by ring
      _ = (2 : ℝ)^b * g j.val := by dsimp [g, m]
  have hfinite :
      (∑ j : Fin W,
        (2 : ℝ) ^ (-((1 - 1 / p) * (j.val + 1 : ℝ))) *
          Real.exp (η * (j.val + 1 : ℝ) / p) *
          (j.val + 2 : ℝ) ^ b) ≤ (2 : ℝ)^b * ∑ j : Fin W, g j.val := by
    calc
      _ ≤ ∑ j : Fin W, (2 : ℝ)^b * g j.val := Finset.sum_le_sum fun j _ => hterm j
      _ = (2 : ℝ)^b * ∑ j : Fin W, g j.val := by rw [Finset.mul_sum]
  have hsumle : (∑ j : Fin W, g j.val) ≤ ∑' n : ℕ, g n := by
    classical
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => g n)]
    exact hg.sum_le_tsum (Finset.range W) (fun n hn => by positivity)
  have hfull : (∑' n : ℕ, g n) ≤ H := by
    have htail0 := htail 0
    have hrewrite : (∑' n : ℕ,
        if 0 ≤ n then (n + 1 : ℝ)^b * Real.exp (-δ * n) else 0) =
        ∑' n : ℕ, g n := by
      apply tsum_congr
      intro n
      simp [g]
    rw [hrewrite] at htail0
    simpa using htail0
  calc
    _ ≤ (2 : ℝ)^b * ∑ j : Fin W, g j.val := hfinite
    _ ≤ (2 : ℝ)^b * H := mul_le_mul_of_nonneg_left (hsumle.trans hfull) (by positivity)
    _ = C := by dsimp [C]

end BrownianSharp.AlignmentPaperJointHighRadiusProfileSum

end
