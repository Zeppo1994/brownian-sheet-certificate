import BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
import BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction
import BrownianSharp.AlignmentPaperSequenceSplit

/-! The full-L¹ Besov image with p, theta >= 2 and smoothness above one half
has precisely the continuous representatives of the same literal cutoff ball.
The proof reconstructs from the actual L¹ source blocks, then transfers each
block norm back through equality of Fourier coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

private instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
private instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

namespace BrownianSharp.AlignmentPeriodicL1CutoffBesovReconstruction

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
open BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction
open BrownianSharp.AlignmentPaperSequenceSplit

local instance sourceProbability (d : ℕ) : IsProbabilityMeasure (sourceMeasure d) := by
  dsimp [sourceMeasure]
  infer_instance

private theorem sourceAE_to_global {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[sourceMeasure d] g) : f =ᵐ[volume] g := by
  simpa [sourceMeasure, BrownianSharp.unitAddTorus_volume_eq_productHaar d] using h

private theorem l1Block_eq_continuous_of_ae {d : ℕ}
    (φ : AdmissibleCutoff) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ) (g : RealPeriodic d)
    (hf : f =ᵐ[sourceMeasure d] fun x => g x) :
    l1CutoffBlock φ s f = admissibleBlock φ s g := by
  have hcoeff (k : Fin d → ℤ) :
      l1CutoffFourierCoeff f k = realPeriodicFourierCoeff g k := by
    unfold l1CutoffFourierCoeff realPeriodicFourierCoeff UnitAddTorus.mFourierCoeff
    exact integral_congr_ae (by
      filter_upwards [hf] with x hx
      exact congrArg (fun z : ℝ => UnitAddTorus.mFourier (-k) x • (z : ℂ)) hx)
  unfold l1CutoffBlock admissibleBlock
  congr 1
  funext k
  exact congrArg (fun z : ℂ =>
    ((∏ i, scalarBlock φ (s i) (k i : ℝ)) : ℂ) * z) (hcoeff k)

private theorem l1Besov_has_continuous_rep {d : ℕ}
    (φ : AdmissibleCutoff) (p θ : ℝ≥0∞) (hp : 2 ≤ p)
    (hθ : 2 ≤ θ) (r : ℝ) (hr : 1 / 2 < r)
    (f : UnitAddTorus (Fin d) → ℝ) (hf : Integrable f (sourceMeasure d))
    (hball : l1CutoffBesovBall φ p r θ f) :
    ∃ g : RealPeriodic d,
      f =ᵐ[sourceMeasure d] (fun x => g x) ∧ BesovUnitBall φ p r θ g := by
  have hnik : ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1 := by
    by_cases htop : θ = ⊤
    · simpa [l1CutoffBesovBall, htop] using hball
    · have hsum : (∑' s : Fin d → ℕ,
          (l1CutoffWeightedBlockNorm φ p r s f) ^ θ.toReal) ≤ 1 := by
        simpa [l1CutoffBesovBall, htop] using hball
      have hθreal : 0 < θ.toReal := ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
          (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) hθ))) htop
      intro s
      exact term_le_one_of_power_sum_le_one
        (fun t => l1CutoffWeightedBlockNorm φ p r t f) θ.toReal hθreal hsum s
  obtain ⟨g, hrep, hnikRep⟩ := l1CutoffNikolsky_has_continuous_rep
    φ p hp r hr f hf hnik
  have hblock : ∀ s, l1CutoffBlock φ s f = admissibleBlock φ s g :=
    fun s => l1Block_eq_continuous_of_ae φ s f g hrep
  have hnorm (s : Fin d → ℕ) :
      l1CutoffWeightedBlockNorm φ p r s f =
        AlignmentPeriodicCutoffClasses.weightedBlockNorm φ p r s g := by
    unfold l1CutoffWeightedBlockNorm AlignmentPeriodicCutoffClasses.weightedBlockNorm
    rw [hblock s]
    rw [BrownianSharp.unitAddTorus_volume_eq_productHaar d]
    rfl
  refine ⟨g, hrep, ?_⟩
  change AlignmentPeriodicCutoffClasses.BesovUnitBall φ p r θ g
  unfold AlignmentPeriodicCutoffClasses.BesovUnitBall
  by_cases htop : θ = ⊤
  · simp only [htop, ↓reduceIte] at hball ⊢
    intro s
    rw [← hnorm s]
    exact hnik s
  · simp only [htop, ↓reduceIte] at hball ⊢
    have hsum : (∑' s : Fin d → ℕ,
        (AlignmentPeriodicCutoffClasses.weightedBlockNorm φ p r s g) ^ θ.toReal) ≤ 1 := by
      have hball' : (∑' s : Fin d → ℕ,
          (l1CutoffWeightedBlockNorm φ p r s f) ^ θ.toReal) ≤ 1 := by
        simpa [l1CutoffBesovBall, htop] using hball
      simpa only [fun s => hnorm s] using hball'
    exact hsum

/-- Equality of the actual full-L¹ image and the continuous periodic image,
for the parameter range used by the finite-theta upper-bound route. -/
theorem fullL1BesovImage_eq_continuous_image {d : ℕ}
    (φ : AdmissibleCutoff) (p θ : ℝ≥0∞) (hp : 2 ≤ p)
    (hθ : 2 ≤ θ) (r : ℝ) (hr : 1 / 2 < r) :
    fullL1BesovImage φ p r θ =
      (ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
        {g : RealPeriodic d | BesovUnitBall φ p r θ g} := by
  ext v
  constructor
  · rintro ⟨u, hu, huv⟩
    change l1CutoffBesovBall φ p r θ (fun x => u x) at hu
    have hmem : MemLp (fun x => u x) 1 (sourceMeasure d) := Lp.memLp u
    have hint : Integrable (fun x => u x) (sourceMeasure d) :=
      hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    obtain ⟨g, hrep, hbes⟩ := l1Besov_has_continuous_rep
      φ p θ hp hθ r hr (fun x => u x) hint hu
    refine ⟨g, hbes, ?_⟩
    apply Lp.ext
    have hrep' : (fun x => (u x : ℝ)) =ᵐ[volume] fun x => g x :=
      sourceAE_to_global hrep
    filter_upwards [huv, hrep', ContinuousMap.coeFn_toLp (p := ⊤)
      (𝕜 := ℝ) (μ := volume) g] with x huv hrep hg
    exact hg.trans (hrep.symm.trans huv)
  · intro hv
    exact continuousBesovImage_subset_fullL1 φ p r θ hv

end BrownianSharp.AlignmentPeriodicL1CutoffBesovReconstruction
