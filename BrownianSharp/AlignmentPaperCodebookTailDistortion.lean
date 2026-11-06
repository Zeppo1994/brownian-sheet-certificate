import BrownianSharp.AlignmentPaperEmpiricalIntegrals

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperCodebookTailDistortion

open BrownianSharp
open BrownianSharp.AlignmentPaperEmpiricalCellLift

/-- A codebook containing zero has controlled quadratic distortion off a good
set whenever the fourth moment of the ambient norm is controlled. -/
theorem finiteCodebookDistortion_lintegral_le_good_tail
    {X : Type*} [MetricSpace X] [Zero X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (c : Fin m → X) (i₀ : Fin m)
    (hi₀ : c i₀ = 0) (G : Set X) (hG : MeasurableSet G)
    (ρ M4 : ℝ≥0∞)
    (hcover : ∀ x ∈ G, ∃ i : Fin m, edist x (c i) ≤ ρ)
    (hM4 : (∫⁻ x, edist x (0 : X) ^ 4 ∂μ) ≤ M4) :
    (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ) ≤
      ρ ^ 2 * μ G + ennrealSqrt M4 * ennrealSqrt (μ Gᶜ) := by
  let d : X → ℝ≥0∞ := fun x => finiteCodebookDistortion hm c x
  let v : X → ℝ≥0∞ := fun x => edist x (0 : X)
  have hd : Measurable d :=
    AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable hm c
  have hv : Measurable v := by
    exact measurable_id.edist measurable_const
  have hgood (x : X) (hx : x ∈ G) : d x ≤ ρ := by
    rcases hcover x hx with ⟨i, hi⟩
    exact (Finset.inf'_le _ (Finset.mem_univ i)).trans hi
  have hbad (x : X) : d x ≤ v x := by
    unfold d v
    calc
      finiteCodebookDistortion hm c x ≤ edist x (c i₀) :=
        Finset.inf'_le _ (Finset.mem_univ i₀)
      _ = edist x 0 := by rw [hi₀]
  have hsplit :
      (∫⁻ x in G, d x ^ 2 ∂μ) + (∫⁻ x in Gᶜ, d x ^ 2 ∂μ) =
        ∫⁻ x, d x ^ 2 ∂μ := by
    exact lintegral_add_compl (fun x : X => d x ^ 2) hG
  rw [← hsplit]
  have hgoodBound :
      (∫⁻ x in G, d x ^ 2 ∂μ) ≤ ρ ^ 2 * μ G := by
    calc
      (∫⁻ x in G, d x ^ 2 ∂μ) ≤ ∫⁻ x in G, ρ ^ 2 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hG] with x hx
        exact pow_le_pow_left₀ bot_le (hgood x hx) 2
      _ = ρ ^ 2 * μ G := by
        rw [lintegral_const]
        simp [Measure.restrict_apply_univ]
  have htailBound :
      (∫⁻ x in Gᶜ, d x ^ 2 ∂μ) ≤ ennrealSqrt M4 * ennrealSqrt (μ Gᶜ) := by
    calc
      (∫⁻ x in Gᶜ, d x ^ 2 ∂μ) ≤ ∫⁻ x in Gᶜ, v x ^ 2 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hG.compl] with x hx
        exact pow_le_pow_left₀ bot_le (hbad x) 2
      _ ≤ ennrealSqrt M4 * ennrealSqrt (μ Gᶜ) := by
        let μT : Measure X := μ.restrict Gᶜ
        have hholder := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
          (μ := μT) Real.HolderConjugate.two_two
          ((hv.pow_const 2).aemeasurable)
          ((measurable_const : Measurable (fun _ : X => (1 : ℝ≥0∞))).aemeasurable)
        have hmass : μT Set.univ = μ Gᶜ := by
          simp [μT, Measure.restrict_apply_univ]
        have hfourth :
            (∫⁻ x, v x ^ 4 ∂μT) ≤ M4 := by
          calc
            (∫⁻ x, v x ^ 4 ∂μT) ≤ ∫⁻ x, v x ^ 4 ∂μ :=
              lintegral_mono' Measure.restrict_le_self le_rfl
            _ ≤ M4 := hM4
        have hholder' :
            (∫⁻ x, v x ^ 2 ∂μT) ≤
              ennrealSqrt (∫⁻ x, v x ^ 4 ∂μT) * ennrealSqrt (μT Set.univ) := by
          have hpowEq (x : X) : (v x ^ 2) ^ 2 = v x ^ 4 := by
            rw [← pow_mul]
          have hpow := hholder
          simpa [ennrealSqrt, hpowEq] using hpow
        calc
          (∫⁻ x in Gᶜ, v x ^ 2 ∂μ) = ∫⁻ x, v x ^ 2 ∂μT := by
            rfl
          _ ≤ ennrealSqrt M4 * ennrealSqrt (μ Gᶜ) := by
            calc
              (∫⁻ x, v x ^ 2 ∂μT) ≤
                  ennrealSqrt (∫⁻ x, v x ^ 4 ∂μT) * ennrealSqrt (μT Set.univ) := hholder'
              _ ≤ ennrealSqrt M4 * ennrealSqrt (μT Set.univ) := by
                  gcongr
                  exact ENNReal.rpow_le_rpow hfourth (by norm_num)
              _ = ennrealSqrt M4 * ennrealSqrt (μ Gᶜ) := by rw [hmass]
  exact add_le_add hgoodBound htailBound

end BrownianSharp.AlignmentPaperCodebookTailDistortion
