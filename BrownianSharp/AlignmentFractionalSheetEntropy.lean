import BrownianSharp.AlignmentFractionalSheetPositiveSource
import BrownianSharp.AlignmentFractionalAnisotropicEntropy
import BrownianSharp.AlignmentFractionalEntropyTransfer
import BrownianSharp.AlignmentCompactFeatureBall
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalSheetEntropy

open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalSheetPositiveSource
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalSheetPositive
open BrownianSharp.AlignmentFractionalAnisotropicEntropy
open BrownianSharp.AlignmentFractionalEntropyTransfer
open BrownianSharp.AlignmentCompactFeatureBall
open HaarQuarter

/-- The positive-source scale in the actual MvN sheet feature factorization
is strictly positive in every Hurst coordinate. -/
theorem positiveSourceScale_pos {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) :
    0 < ∏ i, Real.Gamma (H i+1/2) *
      ‖mvNFullFeature (H i-1/2) 1
        (mvNFullKernel_memLp (hH i).1 (hH i).2
          (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹ := by
  apply Finset.prod_pos
  intro i hi
  apply mul_pos
  · exact Real.Gamma_pos_of_pos (by linarith [(hH i).1])
  · apply inv_pos.mpr
    exact mvNFullKernel_one_norm_pos (H i-1/2)
      (mvNFullKernel_memLp (hH i).1 (hH i).2
        (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))

/-- The actual fractional-sheet feature ball inherits the anisotropic RL
entropy lower bound through the proved positive-source inclusion. -/
theorem fractionalSheetFeature_entropy_lower
    {d ν : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (hν : 2 ≤ ν)
    (m₀ : ℝ) (hm : Latest.minimumMultiplicity H m₀ ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-(m₀+1/2)) *
        (Real.log (k:ℝ))^((m₀+1/2)*((ν-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureBall (fractionalSheetFeature H hH)) := by
  classical
  let a : Fin d → ℝ := fun i => H i + 1/2
  let r : ℝ := m₀ + 1/2
  have ha : ∀ i, 1/2 < a i := by
    intro i
    dsimp [a]
    linarith [(hH i).1]
  have hr : 1/2 < r := by
    dsimp [r]
    have hcardpos : 0 < (Finset.univ.filter (fun i : Fin d => H i = m₀)).card := by
      rw [hm.2]
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardpos
    have hEq : H i = m₀ := (Finset.mem_filter.mp hi).2
    linarith [(hH i).1, hEq]
  have hm' : Latest.minimumMultiplicity a r ν := by
    change (∀ i, r ≤ a i) ∧ (Finset.univ.filter (fun i : Fin d => a i = r)).card = ν
    constructor
    · intro i
      dsimp [a, r]
      linarith [hm.1 i]
    · have heq : Finset.univ.filter (fun i : Fin d => a i = r) =
          Finset.univ.filter (fun i : Fin d => H i = m₀) := by
        apply Finset.filter_congr
        intro i hi
        dsimp [a, r]
        constructor <;> intro h <;> linarith
      rw [heq]
      exact hm.2
  obtain ⟨c₀, hc₀, k₀, hk₀, hEntropy⟩ :=
    fractional_entropy_lower_general hd a ha r hr hν hm'
  let C : ℝ := ∏ i, Real.Gamma (H i+1/2) *
    ‖mvNFullFeature (H i-1/2) 1
      (mvNFullKernel_memLp (hH i).1 (hH i).2
        (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹
  have hC : 0 < C := by exact positiveSourceScale_pos H hH
  refine ⟨C*c₀, mul_pos hC hc₀, k₀, hk₀, ?_⟩
  intro k hk
  let J := Latest.fractionalIntegrationBall a
  let K := featureBall (fractionalSheetFeature H hH)
  have hJ : ENNReal.ofReal (c₀*(k:ℝ)^(-r) *
        (Real.log (k:ℝ))^(r*((ν-1:ℕ):ℝ)+1/2)) ≤
      HaarQuarter.TheoremD.entropyNumber k J := by
    simpa [J, a, r, mul_assoc] using hEntropy k hk
  have hT : ‖(ContinuousLinearMap.id ℝ (C(BrownianCubeAnchor d,ℝ)))‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_id]
  have hsub : (fun f : C(BrownianCubeAnchor d,ℝ) => C • f) '' J ⊆
      (ContinuousLinearMap.id ℝ (C(BrownianCubeAnchor d,ℝ))) '' K := by
    intro f hf
    rcases hf with ⟨f₀,hf₀,rfl⟩
    have hfactor := scaled_fractionalIntegrationBall_subset_sheetFeatureBall H hH
    have hk' : C • f₀ ∈ K := hfactor ⟨f₀,hf₀,rfl⟩
    exact ⟨C • f₀,hk',by simp⟩
  have htrans := entropyNumber_ge_of_scaled_contractive_image
    (ContinuousLinearMap.id ℝ (C(BrownianCubeAnchor d,ℝ))) hT K J C
    (c₀*(k:ℝ)^(-r)*(Real.log (k:ℝ))^(r*((ν-1:ℕ):ℝ)+1/2)) hC
    (by positivity) hsub k hJ
  simpa [C, r, mul_assoc] using htrans

end BrownianSharp.AlignmentFractionalSheetEntropy
