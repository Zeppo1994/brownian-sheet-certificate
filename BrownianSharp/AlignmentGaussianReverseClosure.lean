import BrownianSharp.AlignmentExponentialReverseInversion
import BrownianSharp.AlignmentExponential
import BrownianSharp.AlignmentLatestStatements

noncomputable section
open MeasureTheory HaarQuarter
namespace BrownianSharp.AlignmentGaussianReverseClosure
open AlignmentExponentialReverseInversion

/-- Radius inversion chooses its constants before the probability profile.
Only monotonicity and a lower probability bound on the dyadic radii enter. -/
theorem uniform_upperLog_of_dyadic_probability_lower
    (d N₀ : ℕ) (hd : 2≤d) (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
      ∀p : ℝ→ℝ,
        (∀x y,0<x → x≤y → p x≤p y) →
        (∀N : ℕ,N₀≤N →
          Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)))≤p (radiusProfile d A N)) →
        ∀ε : ℝ,0<ε → ε≤ε₀ → -Real.log (p ε)≤C*sharpRate d ε := by
  obtain ⟨δ,D,hδ,hD,hindex⟩ := exists_dyadic_radius_index d N₀ hd hA
  let ε₀ := min δ (Real.exp (-1)/2)
  refine ⟨B*D,ε₀,mul_pos hB hD,lt_min hδ (by positivity),?_,?_⟩
  · exact (min_le_right _ _).trans_lt (by have h := Real.exp_pos (-1); linarith)
  intro p hmono hdyadic ε hε hsmall
  obtain ⟨N,hN,hradius,hcost⟩ := hindex ε hε (hsmall.trans (min_le_left _ _))
  have hradpos : 0<radiusProfile d A N := by
    unfold radiusProfile
    positivity
  have hp := (hdyadic N hN).trans (hmono _ _ hradpos hradius)
  have hlog := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlog
  have hbound : -Real.log (p ε)≤B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)) := by linarith
  apply hbound.trans
  have h := mul_le_mul_of_nonneg_left hcost hB.le
  simpa only [sharpRate,mul_assoc] using h

/-- The constructive dyadic probability target used to certify the reverse
Brownian small-ball direction. -/
def DyadicBrownianReverseStatement : Prop :=
  ∀d : ℕ,2≤d → ∃A B : ℝ,0<A ∧ 0<B ∧ ∃N₀ : ℕ,
    ∀(Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : BrownianSheetOnCube d Ω P) (N : ℕ),N₀≤N →
      Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)))≤
        P.real {ω | ‖X.path ω‖≤radiusProfile d A N}

def BrownianUpperLogStatement : Prop :=
  ∀d : ℕ,2≤d → ∃C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀(Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : BrownianSheetOnCube d Ω P) (ε : ℝ),0<ε → ε≤ε₀ →
      -Real.log (P.real {ω | ‖X.path ω‖≤ε})≤C*sharpRate d ε

theorem brownian_upperLog_of_dyadic
    (h : DyadicBrownianReverseStatement) : BrownianUpperLogStatement := by
  intro d hd
  obtain ⟨A,B,hA,hB,N₀,hdyad⟩ := h d hd
  obtain ⟨C,ε₀,hC,hε₀,hsmall,hprofiles⟩ :=
    uniform_upperLog_of_dyadic_probability_lower d N₀ hd A B hA hB
  refine ⟨C,ε₀,hC,hε₀,hsmall,?_⟩
  intro Ω _ P _ X ε hε hεsmall
  exact hprofiles (fun η=>P.real {ω | ‖X.path ω‖≤η})
    (by intro x y hx hxy; exact measureReal_mono (fun ω hω=>hω.trans hxy))
    (fun N hN=>hdyad Ω P X N hN) ε hε hεsmall

/-- Completing the constructive dyadic reverse estimate suffices for the
literal two-sided Brownian clause of the latest manuscript. -/
theorem latest_brownian_twoSided_of_dyadic
    (h : DyadicBrownianReverseStatement) : Latest.BrownianTwoSidedStatement := by
  intro d hd
  obtain ⟨c,δ,hc,hδ,hδsmall,hlower⟩ :=
    AlignmentExponential.uniformSharpLog_of_exponentialAverage d hd
  obtain ⟨C,η,hC,hη,hηsmall,hupper⟩ := brownian_upperLog_of_dyadic h d hd
  refine ⟨c,C,min δ η,hc,hC,lt_min hδ hη,
    (min_le_left _ _).trans_lt hδsmall,?_⟩
  intro Ω _ P _ X ε hε hsmall
  exact ⟨hlower Ω P X ε hε (hsmall.trans (min_le_left _ _)),
    hupper Ω P X ε hε (hsmall.trans (min_le_right _ _))⟩

end BrownianSharp.AlignmentGaussianReverseClosure
