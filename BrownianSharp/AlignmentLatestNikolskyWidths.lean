import BrownianSharp.AlignmentPeriodicNikolskyRates
import BrownianSharp.AlignmentLatestPeriodicWidths

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentLatestNikolskyWidths
open SmoothResolution Torus AlignmentPeriodicUpperReduction AlignmentAmbientWidth
open AlignmentAuditPeriodicBoundedness

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := by
  rw [unitAddCircle_volume_eq_haar]
  infer_instance
local instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
local instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

private theorem nikolsky_exponent_identity {d : ℕ} (hd : 2≤d) (r : ℝ) :
    r*((d-1:ℕ):ℝ)+(d:ℝ)/2=(r+1/2)*((d-1:ℕ):ℝ)+1/2 := by
  rw [Nat.cast_sub (by omega : 1≤d)]
  push_cast
  ring

theorem periodic_nikolsky_width_upper {d : ℕ} (hd : 2≤d)
    (p : ENNReal) (hp : 2≤p) (r : ℝ) (hr : 1/2<r) :
    ∃C : ℝ,0<C ∧ ∃n₀ : ℕ,∀n,n₀≤n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall p r f}) n≤
      ENNReal.ofReal (C*logarithmicIndexRate r ((r+1/2)*(d-1:ℕ)+1/2) n) := by
  obtain ⟨A,hA,B,hB,hdyad⟩ :=
    AlignmentPeriodicNikolskyRates.periodic_nikolsky_dyadic_width_upper hd hr
  obtain ⟨C,hC,n₀,_,hupper⟩ :=
    AlignmentEndpointWidthExtraction.all_index_width_rate_of_dyadic_layer_bound hd
      {f : RealPeriodic d | NikolskyUnitBall (2:ENNReal) r f}
      A hA r ((d:ℝ)/2) B (by linarith) (by positivity) hB 0
      (fun n _=>hdyad n)
  refine ⟨C,hC,n₀,?_⟩
  intro n hn
  have hsub : Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall p r f}⊆
      Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall 2 r f} := by
    rintro y ⟨f,hf,rfl⟩
    exact ⟨f,nikolskyUnitBall_mono_exponent hp r f hf,rfl⟩
  have hamb := continuous_width_ge_LInfinity_width
    (volume : Measure (UnitAddTorus (Fin d)))
    {f : RealPeriodic d | NikolskyUnitBall (2:ENNReal) r f} n
  have hh := (kolmogorovWidth_mono_set hsub n).trans (hamb.trans (hupper n hn))
  simpa only [nikolsky_exponent_identity hd r] using hh

theorem periodic_nikolsky_twoSided_width {d : ℕ} (hd : 2≤d)
    (p : ENNReal) (hp : 2≤p) (r : ℝ) (hr : 1/2<r) :
    Latest.twoSidedWidthRate
      (Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall p r f})
      r ((r+1/2)*(d-1:ℕ)+1/2) := by
  have hp1 : (1:ENNReal)<p := lt_of_lt_of_le (by norm_num) hp
  have hpinv : p.toReal⁻¹<r := by
    by_cases htop : p=⊤
    · simpa [htop] using (show 0<r by linarith)
    · have hpR : (2:ℝ)≤p.toReal := by
        have h := (ENNReal.toReal_le_toReal (by norm_num : (2:ENNReal)≠⊤) htop).2 hp
        simpa only [ENNReal.toReal_ofNat] using h
      have hh : p.toReal⁻¹≤1/2 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
      exact hh.trans_lt hr
  obtain ⟨c,hc,k₀,hk₀,hE⟩ :=
    AlignmentLatestPeriodicEntropy.latest_periodicMixedEntropy_certified d hd p hp1 r hpinv ⊤ le_top
  have hEntropy : ∃c' : ℝ,0<c' ∧ ∃n₀ : ℕ,∀n,n₀≤n →
      ENNReal.ofReal (c'*logarithmicIndexRate r ((r+1/2)*(d-1:ℕ)+1/2) n)≤
      HaarQuarter.TheoremD.entropyNumber n
        (Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall p r f}) := by
    refine ⟨c/2,by positivity,k₀,?_⟩
    intro n hn
    have hh := AlignmentLatestPeriodicEntropy.periodic_entropy_lower_to_LInfinity
      {f : RealPeriodic d | NikolskyUnitBall p r f} n
      (c*logarithmicIndexRate r ((r+1/2)*(d-1:ℕ)+1/2) n) (hE n hn).2.2
    convert hh using 1 <;> congr 1 <;> ring
  exact AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
    _ r ((r+1/2)*(d-1:ℕ)+1/2) (periodicNikolskyRadius d r)
    (by linarith) (by positivity) (periodicNikolsky_radius_nonneg (d:=d) hr)
    (nikolsky_linf_width_zero_le_of_exponent hp r hr) hEntropy
    (periodic_nikolsky_width_upper hd p hp r hr)

theorem latest_periodicWidth_certified : Latest.PeriodicWidthStatement := by
  intro d hd p hp r hr
  exact ⟨fun hptop=>AlignmentLatestPeriodicWidths.latest_periodic_sobolev_width hd p hp r hr hptop,
    periodic_nikolsky_twoSided_width hd p hp r hr⟩

end BrownianSharp.AlignmentLatestNikolskyWidths
