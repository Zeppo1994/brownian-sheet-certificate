import BrownianSharp.AlignmentPaperJointGlobalSeries
import BrownianSharp.AlignmentPaperGlobalGradeTail

/-! Exponential terminal-tail control for the actual decoded grade envelope. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointGlobalTail

open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalSeries
open BrownianSharp.AlignmentPaperGlobalGradeTail

theorem gradeSeries_envelope_shift_tail_bound
    {d : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ,
      (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M)) ≤
        K * Real.exp (-((1 - 1 / p) * Real.log 2) * (M : ℝ) / 2) := by
  let δ : ℝ := (1 - 1 / p) * Real.log 2
  let b : ℝ := (d - 1 : ℝ) / p
  let C : ℝ := (2 * (5 : ℝ)^d) * (Real.sqrt ((25 / 4 : ℝ)^d) + 1) * A
  have hp0 : 0 < p := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    apply mul_pos
    · have : 1 / p < 1 := (div_lt_one hp0).2 (by linarith)
      linarith
    · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hb : 0 ≤ b := by
    dsimp [b]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨H, hH, htail⟩ := polynomial_exp_tail_le hδ hb
  have hscale (n : ℕ) : gradeSeriesNormEnvelope d p A n =
      C * ((n + 1 : ℝ)^b * Real.exp (-δ * (n : ℝ))) := by
    unfold gradeSeriesNormEnvelope
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [C, b, δ]
    ring_nf
  refine ⟨C * H, mul_pos hC hH, ?_⟩
  intro M
  let s : Set ℕ := {m | M ≤ m}
  let e : ℕ ≃ s :=
    { toFun := fun n => ⟨n + M, by dsimp [s]; omega⟩
      invFun := fun m => m.1 - M
      left_inv := by intro n; simp
      right_inv := by
        intro m
        apply Subtype.ext
        dsimp [s] at m
        simp [Nat.sub_add_cancel m.2] }
  have hshift :
      (∑' n : ℕ, ((n + M + 1 : ℝ) ^ b * Real.exp (-δ * (n + M : ℝ)))) =
        ∑' m : s, ((m.1 + 1 : ℝ) ^ b * Real.exp (-δ * (m.1 : ℝ))) := by
    convert Equiv.tsum_eq e (fun m : s =>
      ((m.1 + 1 : ℝ) ^ b * Real.exp (-δ * (m.1 : ℝ)))) using 1 <;>
      simp [e, Nat.cast_add, Nat.cast_one]
  have hsubtype :
      (∑' m : s, ((m.1 + 1 : ℝ) ^ b * Real.exp (-δ * (m.1 : ℝ)))) =
        ∑' m : ℕ, (if M ≤ m then (m + 1 : ℝ) ^ b * Real.exp (-δ * (m : ℝ)) else 0) := by
    change (∑' m : ↑s, ((m.1 + 1 : ℝ) ^ b * Real.exp (-δ * (m.1 : ℝ)))) = _
    simpa [s, Set.indicator_apply] using
      (tsum_subtype s (fun m : ℕ => ((m + 1 : ℝ) ^ b * Real.exp (-δ * (m : ℝ)))))
  have hcore :
      (∑' n : ℕ, ((n + M + 1 : ℝ)^b * Real.exp (-δ * (n + M : ℝ)))) ≤
        H * Real.exp (-δ * (M : ℝ) / 2) := by
    rw [hshift, hsubtype]
    exact htail M
  have hsum :
      (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M)) =
        C * ∑' n : ℕ, ((n + M + 1 : ℝ)^b * Real.exp (-δ * (n + M : ℝ))) := by
    simp_rw [hscale]
    rw [tsum_mul_left]
    congr 1
    apply tsum_congr
    intro n
    simp [Nat.cast_add]
  rw [hsum]
  calc
    C * (∑' n : ℕ, ((n + M + 1 : ℝ)^b * Real.exp (-δ * (n + M : ℝ))))
        ≤ C * (H * Real.exp (-δ * (M : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hcore hC.le
    _ = C * H * Real.exp (-((1 - 1 / p) * Real.log 2) * (M : ℝ) / 2) := by
          dsimp [δ]
          ring

theorem gradeSeriesClass_window_decomposition
    {d : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) {f : C(UnitAddTorus (Fin d), ℂ)}
    (hf : f ∈ GradeSeriesClass d p A) (M : ℕ) :
    ∃ v : Fin M → C(UnitAddTorus (Fin d), ℂ), ∃ t,
      (∀ i, v i ∈ decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) ∧
      ‖t‖ ≤ ∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M) ∧
      (List.ofFn v).sum + t = f := by
  rcases hf with ⟨u, hu, rfl⟩
  let hs := gradeSeries_witness_summable hd hp hp2 hA hu
  refine ⟨fun i => u i.val, ∑' n : ℕ, u (n + M), ?_, ?_, ?_⟩
  · intro i
    exact hu i.val
  · exact gradeSeries_norm_tsum_nat_add_le hd hp hp2 hA hu M
  · rw [List.sum_ofFn, Fin.sum_univ_eq_sum_range]
    exact hs.sum_add_tsum_nat_add M

end BrownianSharp.AlignmentPaperJointGlobalTail
