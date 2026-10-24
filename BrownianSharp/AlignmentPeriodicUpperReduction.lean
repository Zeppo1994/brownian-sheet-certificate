import BrownianSharp.SmoothBesovGeneralMean
import BrownianSharp.UnitTorusMeasure
import BrownianSharp.KolmogorovWidth

/-! Reduce all p>=2 periodic width upper estimates to p=2.
This includes the actual spatial infinity endpoint for Besov/Nikolsky. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPeriodicUpperReduction
open BrownianSharp.SmoothResolution
open HaarQuarter.TheoremD.Width

private instance torusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [unitAddTorus_volume_eq_productHaar]
  infer_instance

theorem weightedBlockNorm_mono_exponent {d : ℕ} {p q : ENNReal}
    (hqp : q≤p) (r : ℝ) (s : Fin d→ℕ) (f : Torus.RealPeriodic d) :
    weightedBlockNorm q r s f ≤ weightedBlockNorm p r s f := by
  unfold weightedBlockNorm
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le hqp

theorem besovUnitBall_mono_exponent {d : ℕ} {p q : ENNReal}
    (hqp : q≤p) (r : ℝ) (θ : ENNReal) (f : Torus.RealPeriodic d)
    (hf : BesovUnitBall p r θ f) : BesovUnitBall q r θ f := by
  unfold BesovUnitBall at *
  split_ifs at * with hθ
  · intro s
    exact (weightedBlockNorm_mono_exponent hqp r s f).trans (hf s)
  · apply le_trans _ hf
    apply ENNReal.tsum_le_tsum
    intro s
    exact ENNReal.rpow_le_rpow (weightedBlockNorm_mono_exponent hqp r s f)
      ENNReal.toReal_nonneg

theorem nikolskyUnitBall_mono_exponent {d : ℕ} {p q : ENNReal}
    (hqp : q≤p) (r : ℝ) (f : Torus.RealPeriodic d)
    (hf : NikolskyUnitBall p r f) : NikolskyUnitBall q r f :=
  besovUnitBall_mono_exponent hqp r ⊤ f hf

theorem squareFunctionSquared_measurable {d : ℕ} (r : ℝ) (f : Torus.RealPeriodic d) :
    Measurable (squareFunctionSquared r f) := by
  unfold squareFunctionSquared
  apply Measurable.tsum
  intro s
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((block s f).continuous.measurable.norm.pow_const (2:ℕ)))

theorem sobolevUnitBall_two_of_two_le {d : ℕ} {p : ℝ} (hp : 2≤p)
    (r : ℝ) (f : Torus.RealPeriodic d)
    (hf : SobolevUnitBall p r f) : SobolevUnitBall 2 r f := by
  by_cases hp2 : p=2
  · simpa [hp2] using hf
  have hpgt : 2<p := lt_of_le_of_ne hp (Ne.symm hp2)
  have hp0 : 0<p := by linarith
  have ha0 : 0<2/p := div_pos (by norm_num) hp0
  have ha1 : 2/p<1 := (div_lt_one hp0).2 hpgt
  let G := fun x => (squareFunctionSquared r f x)^(p/2)
  have hG : Measurable G := (squareFunctionSquared_measurable r f).pow_const _
  have hJ := BrownianSharp.lintegral_rpow_le_rpow_lintegral_of_probability
    (μ := (volume : Measure (UnitAddTorus (Fin d)))) G ha0 ha1 hG.aemeasurable
  have hpoint : (fun x => G x ^ (2/p))=squareFunctionSquared r f := by
    funext x
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    have he : (p/2)*(2/p)=1 := by field_simp
    rw [he,ENNReal.rpow_one]
  rw [hpoint] at hJ
  have hupper : (∫⁻ x, G x ∂(volume : Measure (UnitAddTorus (Fin d))))^(2/p) ≤ 1 := by
    have h := ENNReal.rpow_le_rpow hf ha0.le
    simpa only [ENNReal.one_rpow] using h
  have hout := hJ.trans hupper
  simpa [SobolevUnitBall] using hout

theorem approximationError_mono_set {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {K L : Set X} (hKL : K⊆L) (V : Submodule ℝ X) :
    approximationError K V ≤ approximationError L V := by
  apply iSup_le
  intro x
  exact le_iSup (fun y : L => Metric.infEDist y.val (V:Set X)) ⟨x.val,hKL x.property⟩

theorem kolmogorovWidth_mono_set {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {K L : Set X} (hKL : K⊆L) (m : ℕ) :
    kolmogorovWidth K m ≤ kolmogorovWidth L m := by
  unfold kolmogorovWidth
  exact iInf_mono fun V => approximationError_mono_set hKL V.val

theorem sobolev_width_le_two {d : ℕ} {p : ℝ} (hp : 2≤p) (r : ℝ) (m : ℕ) :
    kolmogorovWidth {f : Torus.RealPeriodic d | SobolevUnitBall p r f} m ≤
    kolmogorovWidth {f : Torus.RealPeriodic d | SobolevUnitBall 2 r f} m :=
  kolmogorovWidth_mono_set (fun f hf => sobolevUnitBall_two_of_two_le hp r f hf) m

theorem nikolsky_width_le_two {d : ℕ} {p : ENNReal} (hp : 2≤p) (r : ℝ) (m : ℕ) :
    kolmogorovWidth {f : Torus.RealPeriodic d | NikolskyUnitBall p r f} m ≤
    kolmogorovWidth {f : Torus.RealPeriodic d | NikolskyUnitBall 2 r f} m :=
  kolmogorovWidth_mono_set (fun f hf => nikolskyUnitBall_mono_exponent hp r f hf) m

end BrownianSharp.AlignmentPeriodicUpperReduction
