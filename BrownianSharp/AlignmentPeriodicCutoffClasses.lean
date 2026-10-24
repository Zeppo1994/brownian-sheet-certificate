import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import BrownianSharp.AlignmentPeriodicP2BesovIdentity
import BrownianSharp.AlignmentSquareEnergyExponent

/-! Literal mixed norms for every cutoff allowed by the manuscript.
The concrete certified resolution is recovered definitionally. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

def weightedBlockNorm {d : ℕ} (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (s : Fin d → ℕ) (f : RealPeriodic d) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) *
    eLpNorm (fun x => admissibleBlock φ s f x) p
      (volume : Measure (UnitAddTorus (Fin d)))

def BesovUnitBall {d : ℕ} (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (θ : ℝ≥0∞) (f : RealPeriodic d) : Prop :=
  if θ = ⊤ then ∀ s, weightedBlockNorm φ p r s f ≤ 1 else
    ∑' s, (weightedBlockNorm φ p r s f) ^ θ.toReal ≤ 1

def squareFunctionSquared {d : ℕ} (φ : AdmissibleCutoff) (r : ℝ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) : ℝ≥0∞ :=
  ∑' s : Fin d → ℕ, ENNReal.ofReal
    ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) * ‖admissibleBlock φ s f x‖ ^ 2)

def SobolevUnitBall {d : ℕ} (φ : AdmissibleCutoff) (p r : ℝ)
    (f : RealPeriodic d) : Prop :=
  (∫⁻ x, (squareFunctionSquared φ r f x) ^ (p / 2)
    ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1

def NikolskyUnitBall {d : ℕ} (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (f : RealPeriodic d) : Prop := BesovUnitBall φ p r ⊤ f

@[simp] theorem admissibleBlock_fixed {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) :
    admissibleBlock smoothResolutionCutoff s f = SmoothResolution.block s f := by
  unfold admissibleBlock SmoothResolution.block SmoothResolution.tensorMultiplier
  simp only [scalarBlock_smoothResolution_eq, Complex.ofReal_prod]

@[simp] theorem weightedBlockNorm_fixed {d : ℕ} (p : ℝ≥0∞) (r : ℝ)
    (s : Fin d → ℕ) (f : RealPeriodic d) :
    weightedBlockNorm smoothResolutionCutoff p r s f =
      SmoothResolution.weightedBlockNorm p r s f := by
  simp only [weightedBlockNorm, SmoothResolution.weightedBlockNorm, admissibleBlock_fixed]

@[simp] theorem BesovUnitBall_fixed {d : ℕ} (p : ℝ≥0∞) (r : ℝ)
    (θ : ℝ≥0∞) (f : RealPeriodic d) :
    BesovUnitBall smoothResolutionCutoff p r θ f ↔
      SmoothResolution.BesovUnitBall p r θ f := by
  simp only [BesovUnitBall, SmoothResolution.BesovUnitBall, weightedBlockNorm_fixed]

@[simp] theorem squareFunctionSquared_fixed {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    squareFunctionSquared smoothResolutionCutoff r f x =
      SmoothResolution.squareFunctionSquared r f x := by
  simp only [squareFunctionSquared, SmoothResolution.squareFunctionSquared, admissibleBlock_fixed]

@[simp] theorem SobolevUnitBall_fixed {d : ℕ} (p r : ℝ) (f : RealPeriodic d) :
    SobolevUnitBall smoothResolutionCutoff p r f ↔
      SmoothResolution.SobolevUnitBall p r f := by
  simp only [SobolevUnitBall, SmoothResolution.SobolevUnitBall, squareFunctionSquared_fixed]

@[simp] theorem NikolskyUnitBall_fixed {d : ℕ} (p : ℝ≥0∞) (r : ℝ)
    (f : RealPeriodic d) :
    NikolskyUnitBall smoothResolutionCutoff p r f ↔
      SmoothResolution.NikolskyUnitBall p r f := by
  simp only [NikolskyUnitBall, SmoothResolution.NikolskyUnitBall, BesovUnitBall_fixed]

theorem measurable_squareFunctionSquared {d : ℕ} (φ : AdmissibleCutoff)
    (r : ℝ) (f : RealPeriodic d) :
    Measurable (squareFunctionSquared φ r f) := by
  apply Measurable.ennreal_tsum
  intro s
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((admissibleBlock φ s f).continuous.measurable.norm.pow_const 2))

end BrownianSharp.AlignmentPeriodicCutoffClasses
