import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentFractionalUnitOrders
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement
import BrownianSharp.AlignmentFractionalTensor
import BrownianSharp.CameronMartinWidthCertified
import BrownianSharp.NativeCameronMartinEntropyUpper
import BrownianSharp.AlignmentPeriodicUpperReduction
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! A literal general-p anchored integration image for the range `1 < p ≤ 2`.
The p-source operator is defined by its rectangular integral. Its image is
restricted to continuous representatives, as required by the manuscript's
uniform-norm target. -/

noncomputable section

open MeasureTheory HaarQuarter
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLp

open BrownianSharp.CameronMartin
open BrownianSharp.Latest

def cubeMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict
    (CameronMartin.unitCubeSet d)

def anchoredLpValue {d : ℕ} (p : ℝ)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (t : BrownianCubeAnchor d) : ℝ :=
  ∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u * g u
    ∂cubeMeasure d

/-- The actual p-source integration image in the continuous uniform-norm
ambient space. The pointwise formula is integration over `[0,t]` against a
cube density in `Lᵖ`; retaining only continuous representatives makes this
exactly the image relevant to the manuscript's target space. -/
def anchoredIntegrationLpImage (d : ℕ) (p : ℝ) :
    Set C(BrownianCubeAnchor d, ℝ) :=
  {f | ∃ g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d), ‖g‖ ≤ 1 ∧
    ∀ t, anchoredLpValue p g t = f t}

private theorem entropyNumber_mono {X : Type*} [PseudoEMetricSpace X]
    {K J : Set X} (hK : K ⊆ J) (k : ℕ) :
    TheoremD.entropyNumber k K ≤ TheoremD.entropyNumber k J := by
  unfold TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ, rfl, hcover⟩
  exact sInf_le ⟨ρ, rfl, (Metric.externalCoveringNumber_mono_set hK).trans hcover⟩

private theorem cubeMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (cubeMeasure d) := by
  haveI : IsProbabilityMeasure
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
  infer_instance

/-- Every L2 anchored path belongs to the actual rectangular-integral image
for `1 < p ≤ 2`. This is the finite-measure inclusion `L² ⊆ Lᵖ`, with the
same density and the same pointwise rectangular integral. -/
theorem KdUnitCube_subset_anchoredIntegrationLpImage
    {d : ℕ} {p : ℝ} (_hp : 1 < p) (hp2 : p ≤ 2) :
    CameronMartin.KdUnitCube d ⊆ anchoredIntegrationLpImage d p := by
  classical
  intro f hf
  rcases hf with ⟨g, hg, hgf⟩
  let μ := cubeMeasure d
  have hprob : IsProbabilityMeasure μ := by
    simpa [μ] using cubeMeasure_probability d
  haveI := hprob
  have hpENN : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hp2
      _ = 2 := by norm_num
  have hmem2 : MemLp (g : (Fin d → ℝ) → ℝ) 2 μ := by
    change MemLp (g : (Fin d → ℝ) → ℝ) 2 (cubeMeasure d)
    exact Lp.memLp g
  have hmemP : MemLp (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) μ := by
    rw [memLp_iff]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpENN).trans_lt hmem2
  let gp : Lp ℝ (ENNReal.ofReal p) μ := hmemP.toLp (g : (Fin d → ℝ) → ℝ)
  have hnormGp : ‖gp‖ ≤ ‖g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    rw [eLpNorm_congr_ae hmemP.coeFn_toLp]
    change (eLpNorm (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (g : (Fin d → ℝ) → ℝ) 2 μ).toReal
    exact ENNReal.toReal_mono hmem2.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hpENN)
  have hnorm : ‖gp‖ ≤ 1 := hnormGp.trans hg
  refine ⟨gp, hnorm, ?_⟩
  intro t
  have hcoe : (gp : (Fin d → ℝ) → ℝ) =ᵐ[μ] (g : (Fin d → ℝ) → ℝ) :=
    hmemP.coeFn_toLp
  have hrect :
      (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u *
          (gp : (Fin d → ℝ) → ℝ) u ∂μ) =
        (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u *
          (g : (Fin d → ℝ) → ℝ) u ∂μ) := by
    apply integral_congr_ae
    filter_upwards [hcoe] with u hu
    rw [hu]
  calc
    anchoredLpValue p gp t =
        (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u *
          (g : (Fin d → ℝ) → ℝ) u ∂μ) := hrect
    _ = unitCubeIntegrationPath g t := by
      exact BrownianSharp.AlignmentFractionalUnitOrders.fractionalIntegrationValue_one g t
    _ = f t := congrArg (fun q : C(BrownianCubeAnchor d, ℝ) => q t) hgf

/-- For finite `p ≥ 2`, the rectangular-integral image is contained in the
L2 anchored image. This is the reverse finite-measure inclusion. -/
theorem anchoredIntegrationLpImage_subset_KdUnitCube
    {d : ℕ} {p : ℝ} (hp2 : 2 ≤ p) :
    anchoredIntegrationLpImage d p ⊆ CameronMartin.KdUnitCube d := by
  classical
  intro f hf
  rcases hf with ⟨g, hg, hgf⟩
  let μ := cubeMeasure d
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using cubeMeasure_probability d
  have hpENN : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    calc
      (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp2
  have hmemP : MemLp (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) μ :=
    Lp.memLp g
  have hmem2 : MemLp (g : (Fin d → ℝ) → ℝ) 2 μ := by
    rw [memLp_iff]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpENN).trans_lt hmemP
  let g2 : UnitCubeL2 d := hmem2.toLp (g : (Fin d → ℝ) → ℝ)
  have hnorm : ‖g2‖ ≤ 1 := by
    change ‖hmem2.toLp (g : (Fin d → ℝ) → ℝ)‖ ≤ 1
    rw [Lp.norm_toLp]
    calc
      (eLpNorm (g : (Fin d → ℝ) → ℝ) 2 μ).toReal ≤
          (eLpNorm (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) μ).toReal :=
        ENNReal.toReal_mono hmemP.eLpNorm_ne_top
          (eLpNorm_le_eLpNorm_of_exponent_le hpENN)
      _ = ‖g‖ := by rw [Lp.norm_def]
      _ ≤ 1 := hg
  refine ⟨g2, hnorm, ?_⟩
  ext t
  have hcoe : (g2 : (Fin d → ℝ) → ℝ) =ᵐ[μ] (g : (Fin d → ℝ) → ℝ) :=
    hmem2.coeFn_toLp
  have hrect :
      (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u *
          (g2 : (Fin d → ℝ) → ℝ) u ∂μ) = anchoredLpValue p g t := by
    unfold anchoredLpValue
    apply integral_congr_ae
    filter_upwards [hcoe] with u hu
    rw [hu]
  calc
    unitCubeIntegrationPath g2 t =
        (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u *
          (g2 : (Fin d → ℝ) → ℝ) u ∂μ) :=
          (BrownianSharp.AlignmentFractionalUnitOrders.fractionalIntegrationValue_one g2 t).symm
    _ = anchoredLpValue p g t := hrect
    _ = f t := hgf t

/-- Entropy upper bound for the actual anchored p-image when `p ≥ 2`,
inherited from the sharp L2 Cameron--Martin entropy upper bound. -/
theorem anchoredIntegrationLp_entropy_upper
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp2 : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      TheoremD.entropyNumber k (anchoredIntegrationLpImage d p) ≤
        ENNReal.ofReal (C * cmIndexRate d k) := by
  obtain ⟨Cup, hCup, m₀, hm₀, hwidth⟩ :=
    BrownianSharp.cameronMartinSharpWidthUpper_certified hd
  obtain ⟨C, hC, k₀, hupper⟩ :=
    BrownianSharp.cameronMartin_entropy_upper_of_sharp_width_upper
      hd Cup hCup m₀ hm₀ hwidth
  refine ⟨C, hC, k₀, fun k hk => ?_⟩
  exact (entropyNumber_mono
    (anchoredIntegrationLpImage_subset_KdUnitCube hp2) k).trans (hupper k hk)

/-- Kolmogorov-width upper bound for the actual anchored p-image when `p≥2`.
The target remains the continuous-function uniform-norm space. -/
theorem anchoredIntegrationLp_width_upper
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp2 : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      TheoremD.Width.kolmogorovWidth (anchoredIntegrationLpImage d p) k ≤
        ENNReal.ofReal (C * cmIndexRate d k) := by
  obtain ⟨C, hC, k₀, hk₀, hwidth⟩ :=
    BrownianSharp.cameronMartinSharpWidthUpper_certified hd
  refine ⟨C, hC, k₀, hk₀, fun k hk => ?_⟩
  exact (BrownianSharp.AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set
    (anchoredIntegrationLpImage_subset_KdUnitCube hp2) k).trans (hwidth k hk)

end BrownianSharp.AlignmentPaperAnchoredLp
