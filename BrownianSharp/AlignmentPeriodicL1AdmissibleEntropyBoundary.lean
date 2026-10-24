import BrownianSharp.AlignmentPeriodicCutoffTransferStatement
import BrownianSharp.AlignmentPeriodicFeatureEntropy

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicFeatureEntropy
open BrownianSharp.Latest
open UnitAddTorus

def sourceMeasure (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)

local instance (d : ℕ) : IsProbabilityMeasure (sourceMeasure d) := by
  dsimp [sourceMeasure]
  infer_instance

private theorem sourceAE_to_global {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[sourceMeasure d] g) : f =ᵐ[volume] g := by
  simpa [sourceMeasure, BrownianSharp.unitAddTorus_volume_eq_productHaar d] using h

def l1CutoffFourierCoeff {d : ℕ} (f : UnitAddTorus (Fin d) → ℝ)
    (k : Fin d → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k

def l1CutoffBlock {d : ℕ} (φ : AdmissibleCutoff) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ) : C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial (SmoothResolution.frequencyBox s)
    (fun k => ((∏ i, scalarBlock φ (s i) (k i : ℝ)) : ℂ) *
      l1CutoffFourierCoeff f k)

def l1CutoffWeightedBlockNorm {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) *
    eLpNorm (l1CutoffBlock φ s f) p
      (sourceMeasure d)

def l1CutoffBesovBall {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞)
    (f : UnitAddTorus (Fin d) → ℝ) : Prop :=
  if θ = ⊤ then ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1 else
    ∑' s : Fin d → ℕ, (l1CutoffWeightedBlockNorm φ p r s f) ^ θ.toReal ≤ 1

def l1CutoffSquareFunctionSquared {d : ℕ} (φ : AdmissibleCutoff)
    (r : ℝ) (f : UnitAddTorus (Fin d) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ≥0∞ :=
  ∑' s : Fin d → ℕ, ENNReal.ofReal
    ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) * ‖l1CutoffBlock φ s f x‖ ^ 2)

def l1CutoffSobolevBall {d : ℕ} (φ : AdmissibleCutoff)
    (p r : ℝ) (f : UnitAddTorus (Fin d) → ℝ) : Prop :=
  (∫⁻ x, (l1CutoffSquareFunctionSquared φ r f x) ^ (p / 2)
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1

def quotientL1BesovBall {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞) : Set (Lp ℝ 1
      (sourceMeasure d)) :=
  {u | l1CutoffBesovBall φ p r θ (fun x => u x)}

def quotientL1NikolskyBall {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) : Set (Lp ℝ 1
      (sourceMeasure d)) :=
  {u | ∀ s, l1CutoffWeightedBlockNorm φ p r s (fun x => u x) ≤ 1}

def quotientL1SobolevBall {d : ℕ} (φ : AdmissibleCutoff)
    (p r : ℝ) : Set (Lp ℝ 1 (sourceMeasure d)) :=
  {u | l1CutoffSobolevBall φ p r (fun x => u x)}

def fullL1BesovImage {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞) :
    Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
  {v | ∃ u : Lp ℝ 1 (sourceMeasure d),
    u ∈ quotientL1BesovBall φ p r θ ∧ (fun x => u x) =ᵐ[volume] fun x => v x}

def fullL1NikolskyImage {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (r : ℝ) :
    Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
  {v | ∃ u : Lp ℝ 1 (sourceMeasure d),
    u ∈ quotientL1NikolskyBall φ p r ∧ (fun x => u x) =ᵐ[volume] fun x => v x}

def fullL1SobolevImage {d : ℕ} (φ : AdmissibleCutoff)
    (p r : ℝ) : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
  {v | ∃ u : Lp ℝ 1 (sourceMeasure d),
    u ∈ quotientL1SobolevBall φ p r ∧ (fun x => u x) =ᵐ[volume] fun x => v x}

private theorem l1CutoffFourierCoeff_toLp {d : ℕ}
    (f : RealPeriodic d) (k : Fin d → ℤ) :
    l1CutoffFourierCoeff
        (fun x => (ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) x) k =
      realPeriodicFourierCoeff f k := by
  unfold l1CutoffFourierCoeff realPeriodicFourierCoeff
  unfold UnitAddTorus.mFourierCoeff
  change (∫ x, mFourier (-k) x •
      ((ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) x : ℂ)
    ∂(sourceMeasure d)) =
    ∫ x, mFourier (-k) x • (f x : ℂ)
      ∂(sourceMeasure d)
  exact integral_congr_ae (by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ)
      (μ := sourceMeasure d) f] with x hx
    exact congrArg (fun z : ℂ => mFourier (-k) x • z) (congrArg Complex.ofReal hx))

private theorem l1CutoffBlock_toLp {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (f : RealPeriodic d) :
    l1CutoffBlock φ s
        (fun x => (ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) x) =
          admissibleBlock φ s f := by
  unfold l1CutoffBlock admissibleBlock
  congr 1
  funext k
  exact congrArg (fun z : ℂ =>
      ((∏ i, scalarBlock φ (s i) (k i : ℝ)) : ℂ) * z)
    (l1CutoffFourierCoeff_toLp f k)

private theorem l1CutoffWeightedBlockNorm_toLp {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (s : Fin d → ℕ) (f : RealPeriodic d) :
    l1CutoffWeightedBlockNorm φ p r s
        (fun x => (ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) x) =
          weightedBlockNorm φ p r s f := by
  unfold l1CutoffWeightedBlockNorm weightedBlockNorm
  rw [l1CutoffBlock_toLp]
  rw [BrownianSharp.unitAddTorus_volume_eq_productHaar d]
  rfl

private theorem continuous_to_quotientBesov {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞)
    (f : RealPeriodic d) (hf : BesovUnitBall φ p r θ f) :
    ContinuousMap.toLp 1 (sourceMeasure d) ℝ f ∈
      quotientL1BesovBall φ p r θ := by
  change l1CutoffBesovBall φ p r θ
    (fun x => (ContinuousMap.toLp 1 (sourceMeasure d)
      ℝ f) x)
  change BesovUnitBall φ p r θ f at hf
  unfold BesovUnitBall at hf
  unfold l1CutoffBesovBall
  by_cases hθ : θ = ⊤
  · simp only [hθ, ↓reduceIte] at hf ⊢
    intro s
    rw [l1CutoffWeightedBlockNorm_toLp]
    exact hf s
  · simp only [hθ, ↓reduceIte] at hf ⊢
    have hterm : ∀ s : Fin d → ℕ,
        l1CutoffWeightedBlockNorm φ p r s
          (fun x => (ContinuousMap.toLp 1
            (sourceMeasure d) ℝ f) x) =
        weightedBlockNorm φ p r s f :=
      fun s => l1CutoffWeightedBlockNorm_toLp φ p r s f
    simpa only [hterm] using hf

private theorem continuous_to_quotientNikolsky {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (f : RealPeriodic d) (hf : NikolskyUnitBall φ p r f) :
    ContinuousMap.toLp 1 (sourceMeasure d) ℝ f ∈
      quotientL1NikolskyBall φ p r := by
  change ∀ s, l1CutoffWeightedBlockNorm φ p r s
    (fun x => (ContinuousMap.toLp 1
      (sourceMeasure d) ℝ f) x) ≤ 1
  intro s
  have h := hf s
  rw [l1CutoffWeightedBlockNorm_toLp]
  exact h

private theorem l1CutoffSobolevBall_toLp {d : ℕ} (φ : AdmissibleCutoff)
    (p r : ℝ) (f : RealPeriodic d) :
    l1CutoffSobolevBall φ p r
      (fun x => (ContinuousMap.toLp 1 (sourceMeasure d)
        ℝ f) x) ↔ SobolevUnitBall φ p r f := by
  unfold l1CutoffSobolevBall SobolevUnitBall
  have hpoint : (fun x => l1CutoffSquareFunctionSquared φ r
      (fun y => (ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) y) x) =
      squareFunctionSquared φ r f := by
    funext x
    unfold l1CutoffSquareFunctionSquared squareFunctionSquared
    congr 1
    funext s
    rw [l1CutoffBlock_toLp]
  have hpoint' : ∀ x, l1CutoffSquareFunctionSquared φ r
      (fun y => (ContinuousMap.toLp 1 (sourceMeasure d) ℝ f) y) x =
        squareFunctionSquared φ r f x := fun x => congrFun hpoint x
  constructor <;> intro h <;> simpa only [hpoint'] using h

private theorem continuous_to_quotientSobolev {d : ℕ}
    (φ : AdmissibleCutoff) (p r : ℝ) (f : RealPeriodic d)
    (hf : SobolevUnitBall φ p r f) :
    ContinuousMap.toLp 1 (sourceMeasure d) ℝ f ∈
      quotientL1SobolevBall φ p r :=
  (l1CutoffSobolevBall_toLp φ p r f).2 hf

theorem continuousBesovImage_subset_fullL1 {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞) :
    (ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
      {f : RealPeriodic d | BesovUnitBall φ p r θ f} ⊆ fullL1BesovImage φ p r θ := by
  rintro v ⟨f, hf, rfl⟩
  refine ⟨ContinuousMap.toLp 1 (sourceMeasure d) ℝ f,
    continuous_to_quotientBesov φ p r θ f hf, ?_⟩
  have h1 := ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ)
    (μ := sourceMeasure d) f
  have h1' := sourceAE_to_global h1
  filter_upwards [h1',
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ) (μ := volume) f] with x h1 htop
  exact h1.trans htop.symm

theorem continuousNikolskyImage_subset_fullL1 {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) :
    (ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
      {f : RealPeriodic d | NikolskyUnitBall φ p r f} ⊆
        fullL1NikolskyImage φ p r := by
  rintro v ⟨f, hf, rfl⟩
  refine ⟨ContinuousMap.toLp 1 (sourceMeasure d) ℝ f,
    continuous_to_quotientNikolsky φ p r f hf, ?_⟩
  have h1 := ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ)
    (μ := sourceMeasure d) f
  have h1' := sourceAE_to_global h1
  filter_upwards [h1',
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ) (μ := volume) f] with x h1 htop
  exact h1.trans htop.symm

theorem continuousSobolevImage_subset_fullL1 {d : ℕ}
    (φ : AdmissibleCutoff) (p r : ℝ) :
    (ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
      {f : RealPeriodic d | SobolevUnitBall φ p r f} ⊆ fullL1SobolevImage φ p r := by
  rintro v ⟨f, hf, rfl⟩
  refine ⟨ContinuousMap.toLp 1 (sourceMeasure d) ℝ f,
    continuous_to_quotientSobolev φ p r f hf, ?_⟩
  have h1 := ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ)
    (μ := sourceMeasure d) f
  have h1' := sourceAE_to_global h1
  filter_upwards [h1',
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ) (μ := volume) f] with x h1 htop
  exact h1.trans htop.symm

def FullL1PeriodicEntropyStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 1 < p → ∀ r : ℝ, p.toReal⁻¹ < r →
      ∀ θ : ℝ≥0∞, 1 ≤ θ →
        ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
          (p ≠ ⊤ → ENNReal.ofReal (c * logarithmicIndexRate r
            (r * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k
              (fullL1SobolevImage (d := d) φ p.toReal r)) ∧
          ENNReal.ofReal (c * logarithmicIndexRate r
            ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k
              (fullL1BesovImage (d := d) φ p r θ) ∧
          ENNReal.ofReal (c * logarithmicIndexRate r
            ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k
              (fullL1NikolskyImage (d := d) φ p r)

theorem fullL1_periodic_entropy_of_cutoff_statement
    (hEntropy : BrownianSharp.AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement) :
    FullL1PeriodicEntropyStatement := by
  unfold FullL1PeriodicEntropyStatement
  intro φ d hd p hp r hpr θ hθ
  obtain ⟨c, hc, k₀, hk₀, hcont⟩ := hEntropy φ d hd p hp r hpr θ hθ
  refine ⟨c, hc, k₀, hk₀, ?_⟩
  intro k hk
  obtain ⟨hsob, hbes, hnik⟩ := hcont k hk
  have hsubSob : Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f} ⊆
      fullL1SobolevImage φ p.toReal r :=
    continuousSobolevImage_subset_fullL1 φ p.toReal r
  have hsubBes : Latest.periodicLInfinityImage
      {f : RealPeriodic d | BesovUnitBall φ p r θ f} ⊆
      fullL1BesovImage φ p r θ :=
    continuousBesovImage_subset_fullL1 φ p r θ
  have hsubNik : Latest.periodicLInfinityImage
      {f : RealPeriodic d | NikolskyUnitBall φ p r f} ⊆
      fullL1NikolskyImage φ p r :=
    continuousNikolskyImage_subset_fullL1 φ p r
  constructor
  · intro hptop
    have h := entropyNumber_mono hsubSob k
    have hsob' : ENNReal.ofReal (c * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f}) := by
      simpa [AlignmentOperatorStatements.periodicEmbeddingEntropy] using hsob hptop
    exact hsob'.trans h
  constructor
  · have h := entropyNumber_mono hsubBes k
    have hbes' : ENNReal.ofReal (c * logarithmicIndexRate r
        ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
          {f : RealPeriodic d | BesovUnitBall φ p r θ f}) := by
      simpa [AlignmentOperatorStatements.periodicEmbeddingEntropy] using hbes
    exact hbes'.trans h
  · have h := entropyNumber_mono hsubNik k
    have hnik' : ENNReal.ofReal (c * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
          {f : RealPeriodic d | NikolskyUnitBall φ p r f}) := by
      simpa [AlignmentOperatorStatements.periodicEmbeddingEntropy] using hnik
    exact hnik'.trans h

end BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
