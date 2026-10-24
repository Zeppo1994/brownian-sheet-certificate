import BrownianSharp.AlignmentPeriodicWidthUniformUpper
import BrownianSharp.AlignmentLatestPeriodicEntropy
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentWidthRates

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentLatestPeriodicWidths
open BrownianSharp.SmoothResolution BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicUpperReduction
open BrownianSharp.AlignmentAmbientWidth
open BrownianSharp.AlignmentPeriodicWidthUniformUpper
open BrownianSharp.AlignmentAuditPeriodicBoundedness

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := by
  rw [unitAddCircle_volume_eq_haar]
  infer_instance

local instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
local instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

theorem periodic_sobolev_width_upper {d : ℕ} (hd : 2≤d)
    (p r : ℝ) (hp : 2≤p) (hr : 1/2<r) :
    ∃ C : ℝ,0<C ∧ ∃n₀ : ℕ,∀n,n₀≤n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p r f}) n ≤
      ENNReal.ofReal (C*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) n) := by
  obtain ⟨A,hA,B,hB,hdyad⟩ := periodic_sobolev_dyadic_width_upper hd (r:=r) hr
  obtain ⟨C,hC,n₀,_,hupper⟩ :=
    AlignmentEndpointWidthExtraction.all_index_width_rate_of_dyadic_layer_bound hd
      {f : RealPeriodic d | SobolevUnitBall 2 r f} A hA r (1/2) B
      (by linarith) (by norm_num) hB 0 (fun n _ => hdyad n)
  refine ⟨C,hC,n₀,?_⟩
  intro n hn
  have hsub : Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p r f} ⊆
      Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall 2 r f} := by
    rintro y ⟨f,hf,rfl⟩
    exact ⟨f,sobolevUnitBall_two_of_two_le hp r f hf,rfl⟩
  have hmono := kolmogorovWidth_mono_set hsub n
  have hamb := continuous_width_ge_LInfinity_width
    (volume : Measure (UnitAddTorus (Fin d)))
    {f : RealPeriodic d | SobolevUnitBall 2 r f} n
  exact hmono.trans (hamb.trans (hupper n hn))

theorem periodic_sobolev_twoSided_width {d : ℕ} (hd : 2≤d)
    (p r : ℝ) (hp : 2≤p) (hr : 1/2<r) :
    Latest.twoSidedWidthRate
      (Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p r f})
      r (r*(d-1:ℕ)+1/2) := by
  have hp1 : 1<p := by linarith
  have hpinv : p⁻¹≤1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hp
  have hpr : p⁻¹<r := hpinv.trans_lt hr
  obtain ⟨c,hc,k₀,hk₀,hE⟩ := periodicMixedEntropy_certified d hd p r hp1 hpr ⊤ le_top
  have hEntropy : ∃ c' : ℝ,0<c' ∧ ∃n₀ : ℕ,∀n,n₀≤n →
      ENNReal.ofReal (c'*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) n) ≤
      HaarQuarter.TheoremD.entropyNumber n
        (Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p r f}) := by
    refine ⟨c/2,by positivity,k₀,?_⟩
    intro n hn
    have h := AlignmentLatestPeriodicEntropy.periodic_entropy_lower_to_LInfinity
      {f : RealPeriodic d | SobolevUnitBall p r f} n
      (c*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) n) (hE n hn).1
    convert h using 1 <;> congr 1 <;> ring
  exact AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
    _ r (r*(d-1:ℕ)+1/2) (periodicNikolskyRadius d r)
    (by linarith) (by positivity) (periodicNikolsky_radius_nonneg (d:=d) hr)
    (sobolev_linf_width_zero_le_of_exponent hp r hr) hEntropy
    (periodic_sobolev_width_upper hd p r hp hr)


theorem latest_periodic_sobolev_width {d : ℕ} (hd : 2≤d)
    (p : ENNReal) (hp : 2≤p) (r : ℝ) (hr : 1/2<r) (hptop : p≠⊤) :
    Latest.twoSidedWidthRate
      (Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p.toReal r f})
      r (r*(d-1:ℕ)+1/2) := by
  have hpR : (2:ℝ)≤p.toReal := by
    have h := (ENNReal.toReal_le_toReal (by norm_num : (2:ENNReal)≠⊤) hptop).2 hp
    simpa only [ENNReal.toReal_ofNat] using h
  exact periodic_sobolev_twoSided_width hd p.toReal r hpR hr

end BrownianSharp.AlignmentLatestPeriodicWidths
