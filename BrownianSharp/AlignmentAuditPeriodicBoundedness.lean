import BrownianSharp.AlignmentPeriodicReconstruction
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentPeriodicEnergy
import BrownianSharp.AlignmentContinuousLInfinity
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.KolmogorovWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A finite radius for the literal two-smoothness Nikolsky ball, obtained
from its absolutely convergent smooth-block expansion. The same radius gives
the zero-width premise after embedding into L-infinity. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace BrownianSharp.AlignmentAuditPeriodicBoundedness
open BrownianSharp.Torus BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPeriodicReconstruction
open BrownianSharp.AlignmentPeriodicFourierReconstruction
open BrownianSharp.AlignmentPeriodicEnergy
open BrownianSharp.AlignmentAmbientWidth

/-- The geometric majorant of the sup norms of all smooth dyadic blocks. -/
def periodicNikolskyRadius (d : ℕ) (r : ℝ) : ℝ :=
  ∑' s : Fin d → ℕ,
    Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^(∑ i, s i)

theorem periodicNikolsky_majorant_summable {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) :
    Summable (fun s : Fin d → ℕ =>
      Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^(∑ i, s i)) := by
  have hq0 : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  exact (summable_shape_geometric d hq0 hq1).mul_left (Real.sqrt ((5:ℝ)^d))

theorem periodicNikolsky_radius_nonneg {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) : 0 ≤ periodicNikolskyRadius d r := by
  unfold periodicNikolskyRadius
  apply tsum_nonneg
  intro s
  positivity

theorem complexifyContinuous_norm_eq {d : ℕ} (f : RealPeriodic d) :
    ‖complexifyContinuous f‖ = ‖f‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
  apply iSup_congr
  intro x
  simp [complexifyContinuous]

theorem nikolsky_two_sup_norm_le_radius {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f) :
    ‖f‖ ≤ periodicNikolskyRadius d r := by
  have hs := nikolsky_two_blocks_hasSum r hr f hf
  have hmaj := periodicNikolsky_majorant_summable (d:=d) hr
  have hnorm : Summable (fun s : Fin d → ℕ => ‖block s f‖) :=
    Summable.of_norm_bounded hmaj
      (fun s => by simpa using nikolsky_two_block_sup_bound s f r hf)
  have hblocksum : ‖∑' s : Fin d → ℕ, block s f‖ ≤
      ∑' s : Fin d → ℕ, ‖block s f‖ := norm_tsum_le_tsum_norm hnorm
  have hsumle : (∑' s : Fin d → ℕ, ‖block s f‖) ≤ periodicNikolskyRadius d r := by
    unfold periodicNikolskyRadius
    exact Summable.tsum_le_tsum
      (fun s => nikolsky_two_block_sup_bound s f r hf) hnorm hmaj
  calc
    ‖f‖ = ‖complexifyContinuous f‖ := complexifyContinuous_norm_eq f |>.symm
    _ = ‖∑' s : Fin d → ℕ, block s f‖ := by rw [hs.tsum_eq]
    _ ≤ ∑' s : Fin d → ℕ, ‖block s f‖ := hblocksum
    _ ≤ periodicNikolskyRadius d r := hsumle

theorem sobolev_two_sup_norm_le_radius {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    ‖f‖ ≤ periodicNikolskyRadius d r :=
  nikolsky_two_sup_norm_le_radius r hr f
    (sobolev_two_subset_nikolsky_two r f hf)

theorem kolmogorovWidth_zero_le_of_norm_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (R : ℝ)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 ≤ ENNReal.ofReal R := by
  rw [HaarQuarter.TheoremD.Width.kolmogorovWidth_zero_eq_bot]
  unfold HaarQuarter.TheoremD.Width.approximationError
  apply iSup_le
  intro x
  have hx := hbound x.1 x.2
  have hdist : dist x.1 (0:X) ≤ R := by simpa [dist_eq_norm] using hx
  calc
    Metric.infEDist x.1 ((⊥ : Submodule ℝ X) : Set X) ≤ edist x.1 0 :=
      Metric.infEDist_le_edist_of_mem (by simp)
    _ = ENNReal.ofReal (dist x.1 (0:X)) := edist_dist _ _
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hdist

theorem nikolsky_two_linf_radius_bound {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) :
    ∀ f ∈ Latest.periodicLInfinityImage
      {f : RealPeriodic d | NikolskyUnitBall 2 r f},
      ‖f‖ ≤ periodicNikolskyRadius d r := by
  rintro y ⟨f,hf,rfl⟩
  have hnorm := nikolsky_two_sup_norm_le_radius r hr f hf
  have hcont : ‖ContinuousMap.toLp (p:=⊤) volume ℝ f‖ ≤ ‖f‖ := by
    have hop : ‖ContinuousMap.toLp (E:=ℝ) (p:=⊤) (𝕜:=ℝ)
        (volume : Measure (UnitAddTorus (Fin d)))‖ ≤ 1 := by
      simpa using (ContinuousMap.toLp_norm_le (E:=ℝ) (p:=⊤) (𝕜:=ℝ)
        (volume : Measure (UnitAddTorus (Fin d))))
    exact ((ContinuousMap.toLp (p:=⊤) volume ℝ).le_opNorm f).trans
      (by simpa using mul_le_mul_of_nonneg_right hop (norm_nonneg f))
  exact hcont.trans hnorm

theorem sobolev_two_linf_radius_bound {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) :
    ∀ f ∈ Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall 2 r f},
      ‖f‖ ≤ periodicNikolskyRadius d r := by
  rintro y ⟨f,hf,rfl⟩
  exact (nikolsky_two_linf_radius_bound r hr)
    (ContinuousMap.toLp ⊤ volume ℝ f)
    ⟨f, sobolev_two_subset_nikolsky_two r f hf, rfl⟩

theorem nikolsky_two_linf_width_zero_le {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | NikolskyUnitBall 2 r f}) 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) :=
  kolmogorovWidth_zero_le_of_norm_bound _ _ (nikolsky_two_linf_radius_bound r hr)

theorem sobolev_two_linf_width_zero_le {d : ℕ} (r : ℝ)
    (hr : 1/2 < r) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall 2 r f}) 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) :=
  kolmogorovWidth_zero_le_of_norm_bound _ _ (sobolev_two_linf_radius_bound r hr)

theorem nikolsky_linf_width_zero_le_of_exponent {d : ℕ}
    {p : ENNReal} (hp : 2≤p) (r : ℝ) (hr : 1/2<r) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | NikolskyUnitBall p r f}) 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) := by
  have hsub : Latest.periodicLInfinityImage
      {f : RealPeriodic d | NikolskyUnitBall p r f} ⊆
      Latest.periodicLInfinityImage
        {f : RealPeriodic d | NikolskyUnitBall 2 r f} := by
    rintro y ⟨f,hf,rfl⟩
    exact ⟨f,BrownianSharp.AlignmentPeriodicUpperReduction.nikolskyUnitBall_mono_exponent
      hp r f hf,rfl⟩
  apply (BrownianSharp.AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set
    hsub 0).trans
  exact nikolsky_two_linf_width_zero_le r hr

theorem sobolev_linf_width_zero_le_of_exponent {d : ℕ}
    {p : ℝ} (hp : 2≤p) (r : ℝ) (hr : 1/2<r) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall p r f}) 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) := by
  have hsub : Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall p r f} ⊆
      Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall 2 r f} := by
    rintro y ⟨f,hf,rfl⟩
    exact ⟨f,BrownianSharp.AlignmentPeriodicUpperReduction.sobolevUnitBall_two_of_two_le
      hp r f hf,rfl⟩
  apply (BrownianSharp.AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set
    hsub 0).trans
  exact sobolev_two_linf_width_zero_le r hr

end BrownianSharp.AlignmentAuditPeriodicBoundedness

