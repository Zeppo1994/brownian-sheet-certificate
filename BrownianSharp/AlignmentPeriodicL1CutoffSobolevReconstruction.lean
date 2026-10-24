import BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction
import BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
import BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
import BrownianSharp.AlignmentPeriodicP2BesovIdentity
import BrownianSharp.AlignmentPeriodicCutoffSobolevWidth
import BrownianSharp.AlignmentPeriodicCutoffNikolskyWidth

/-! Generic admissible-cutoff Sobolev boundary from L¹ to continuous representatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
open BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
open BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.Latest
open UnitAddTorus

private instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
private instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩
private instance sourceProbability (d : ℕ) : IsProbabilityMeasure (sourceMeasure d) := by
  dsimp [sourceMeasure]
  infer_instance

private theorem l1CutoffSobolev_to_nikolsky_two {d : ℕ}
    (φ : AdmissibleCutoff) {p r : ℝ} (hp : 2 ≤ p)
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : l1CutoffSobolevBall φ p r f) :
    ∀ s, l1CutoffWeightedBlockNorm φ 2 r s f ≤ 1 := by
  let S := l1CutoffSquareFunctionSquared φ r f
  have hSmeas : AEMeasurable S (sourceMeasure d) := by
    change AEMeasurable (l1CutoffSquareFunctionSquared φ r f) (sourceMeasure d)
    have hm : Measurable (l1CutoffSquareFunctionSquared φ r f) := by
      unfold l1CutoffSquareFunctionSquared
      apply Measurable.ennreal_tsum
      intro s
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul
          ((l1CutoffBlock φ s f).continuous.measurable.norm.pow_const 2))
    exact hm.aemeasurable
  have hball' : (∫⁻ x, S x ^ (p / 2) ∂(sourceMeasure d)) ≤ 1 := by
    simpa [S, l1CutoffSobolevBall, sourceMeasure,
      BrownianSharp.unitAddTorus_volume_eq_productHaar] using hf
  have hL2 := BrownianSharp.AlignmentSquareEnergyExponent.squareFunction_unit_energy_mono
    S hSmeas (by norm_num : 0 < (2 : ℝ)) hp hball'
  have hL2' : (∫⁻ x, S x ∂(sourceMeasure d)) ≤ 1 := by
    simpa [ENNReal.rpow_one] using hL2
  let w : (Fin d → ℕ) → ℝ := fun s =>
    (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
  let g : (Fin d → ℕ) → UnitAddTorus (Fin d) → ℂ :=
    fun s x => l1CutoffBlock φ s f x
  have hw : ∀ s, 0 ≤ w s := by intro s; dsimp [w]; positivity
  have hg : ∀ s, AEStronglyMeasurable (g s) (sourceMeasure d) := by
    intro s
    dsimp [g]
    exact (l1CutoffBlock φ s f).continuous.aestronglyMeasurable
  have htonelli :=
    BrownianSharp.AlignmentPeriodicP2BesovIdentity.lintegral_tsum_weighted_block_sq_eq_tsum
      (μ := sourceMeasure d) g w hw hg
  have hpow (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
      ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          ‖l1CutoffBlock φ s f x‖ ^ 2) =
      ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) := by
    congr 1
    dsimp [w, g]
    have hpw : ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 =
        (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      ring
    rw [hpw]
  have hpoint : S = fun x => ∑' s : Fin d → ℕ,
      ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) := by
    funext x
    dsimp [S, l1CutoffSquareFunctionSquared]
    apply tsum_congr
    intro s
    exact hpow s x
  have henergy : (∫⁻ x, S x ∂(sourceMeasure d)) =
      ∑' s : Fin d → ℕ,
        (ENNReal.ofReal (w s) * eLpNorm (g s) 2 (sourceMeasure d)) ^ 2 := by
    rw [hpoint, htonelli]
  intro s
  have hterm : (ENNReal.ofReal (w s) * eLpNorm (g s) 2 (sourceMeasure d)) ^ 2 ≤
      ∑' t : Fin d → ℕ,
        (ENNReal.ofReal (w t) * eLpNorm (g t) 2 (sourceMeasure d)) ^ 2 := by
    exact ENNReal.le_tsum (f := fun t : Fin d → ℕ =>
      (ENNReal.ofReal (w t) * eLpNorm (g t) 2 (sourceMeasure d)) ^ 2) s
  have hterm' : (l1CutoffWeightedBlockNorm φ 2 r s f) ^ 2 ≤ 1 := by
    simpa [l1CutoffWeightedBlockNorm, w, g] using
      hterm.trans (henergy.symm ▸ hL2')
  exact (pow_le_one_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hterm'

private theorem sourceAE_to_global {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[sourceMeasure d] g) : f =ᵐ[volume] g := by
  simpa [sourceMeasure, BrownianSharp.unitAddTorus_volume_eq_productHaar] using h

private theorem l1CutoffBlock_eq_continuous_of_ae {d : ℕ}
    (φ : AdmissibleCutoff) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ) (g : RealPeriodic d)
    (hf : f =ᵐ[sourceMeasure d] fun x => g x) :
    l1CutoffBlock φ s f = admissibleBlock φ s g := by
  have hcoeff : ∀ k : Fin d → ℤ,
      l1CutoffFourierCoeff f k = realPeriodicFourierCoeff g k := by
    intro k
    unfold l1CutoffFourierCoeff realPeriodicFourierCoeff UnitAddTorus.mFourierCoeff
    exact integral_congr_ae (by
      filter_upwards [hf] with x hx
      exact congrArg (fun z : ℝ => mFourier (-k) x • (z : ℂ)) hx)
  unfold l1CutoffBlock admissibleBlock
  congr 1
  funext k
  exact congrArg (fun z : ℂ =>
      ((∏ i, scalarBlock φ (s i) (k i : ℝ)) : ℂ) * z) (hcoeff k)

/-- Any integrable L¹ source in the cutoff square-function Sobolev ball has a
continuous representative in that same literal Sobolev ball. -/
theorem l1CutoffSobolev_has_continuous_rep {d : ℕ}
    (φ : AdmissibleCutoff) {p r : ℝ} (hp : 2 ≤ p) (hr : 1 / 2 < r)
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : Integrable f (sourceMeasure d))
    (hball : l1CutoffSobolevBall φ p r f) :
    ∃ g : RealPeriodic d,
      f =ᵐ[sourceMeasure d] (fun x => g x) ∧ SobolevUnitBall φ p r g := by
  obtain ⟨g, hrep, hnik⟩ :=
    l1CutoffNikolsky_has_continuous_rep φ (p := (2 : ℝ≥0∞))
      (by norm_num) r hr f hf (l1CutoffSobolev_to_nikolsky_two φ hp f hball)
  have hblock : ∀ s, l1CutoffBlock φ s f = admissibleBlock φ s g :=
    fun s => l1CutoffBlock_eq_continuous_of_ae φ s f g hrep
  have hpoint : l1CutoffSquareFunctionSquared φ r f =
      squareFunctionSquared φ r g := by
    funext x
    unfold l1CutoffSquareFunctionSquared squareFunctionSquared
    apply tsum_congr
    intro s
    rw [hblock s]
  refine ⟨g, hrep, ?_⟩
  have hprod : (∫⁻ x, (squareFunctionSquared φ r g x) ^ (p / 2)
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1 := by
    calc
      _ = ∫⁻ x, (l1CutoffSquareFunctionSquared φ r f x) ^ (p / 2)
          ∂(volume : Measure (UnitAddTorus (Fin d))) := by
        rw [← hpoint]
      _ ≤ 1 := hball
  exact hprod

/-- The generic cutoff full-L¹ Sobolev image has no additional functions beyond
the continuous Sobolev image, for p≥2 and r>1/2. -/
theorem fullL1SobolevImage_eq_continuous_image {d : ℕ}
    (φ : AdmissibleCutoff) {p r : ℝ} (hp : 2 ≤ p) (hr : 1 / 2 < r) :
    fullL1SobolevImage φ p r =
      (ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
        {g : RealPeriodic d | SobolevUnitBall φ p r g} := by
  ext v
  constructor
  · rintro ⟨u, hu, huv⟩
    change l1CutoffSobolevBall φ p r (fun x => u x) at hu
    have hball := hu
    have hmem : MemLp (fun x => u x) 1 (sourceMeasure d) := Lp.memLp u
    have hint : Integrable (fun x => u x) (sourceMeasure d) :=
      hmem.integrable (by norm_num : (1 : ENNReal) ≤ 1)
    obtain ⟨g, hrep, hsob⟩ := l1CutoffSobolev_has_continuous_rep
      φ hp hr (fun x => u x) hint hball
    refine ⟨g, hsob, ?_⟩
    apply Lp.ext
    have hrep' := sourceAE_to_global hrep
    filter_upwards [huv, hrep',
      ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ)
        (μ := volume) g] with x huv hrep hg
    exact hg.trans (hrep.symm.trans huv)
  · intro hv
    exact continuousSobolevImage_subset_fullL1 φ p r hv

/-- Literal latest periodic width clauses, but with the source class defined
directly on L¹ before passage to the global L-infinity ambient. -/
def FullL1PeriodicWidthStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1 / 2 < r →
      (p ≠ ⊤ → AlignmentOperatorStatements.twoSidedWidthRate
        (fullL1SobolevImage (d := d) φ p.toReal r)
        r (r * (d - 1 : ℕ) + 1 / 2)) ∧
      AlignmentOperatorStatements.twoSidedWidthRate
        (fullL1NikolskyImage (d := d) φ p r)
        r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)

/-- The full-L¹ version of the periodic width theorem follows from the
continuous-class theorem once both source classes have continuous
representatives. -/
theorem fullL1_periodic_width_of_cutoff_statement
    (hWidth : AlignmentPeriodicCutoffTransferStatement.PeriodicWidthStatement) :
    FullL1PeriodicWidthStatement := by
  intro φ d hd p hp r hr
  obtain ⟨hSob, hNik⟩ := hWidth φ d hd p hp r hr
  constructor
  · intro hptop
    have hpReal : (2 : ℝ) ≤ p.toReal := by
      have h := (ENNReal.toReal_le_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hptop).2 hp
      simpa only [ENNReal.toReal_ofNat] using h
    have hcont := hSob hptop
    rw [fullL1SobolevImage_eq_continuous_image φ hpReal hr]
    exact hcont
  · rw [fullL1NikolskyImage_eq_continuous φ p hp r hr]
    exact hNik

end BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction
