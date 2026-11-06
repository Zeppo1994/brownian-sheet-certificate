import BrownianSharp.AlignmentExponentialContinuousCover
import BrownianSharp.PeriodicSynthesisScale
import BrownianSharp.AlignmentPaperConfinementBridge
import BrownianSharp.NativeClassReindex
import BrownianSharp.NativeScaleCover
import BrownianSharp.PeriodicCoverRate
import Mathlib.Tactic

/-! Compact-domain entropy lower bound from arbitrarily small exponential
Gaussian class-mass exponents. The class mass is compared directly against
the uniform-confinement probability, without a finite shape cutoff. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentExponentialBoxEntropy
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumGenericBump
  AlignmentPaperGenericBumpCertified

/-- Generic compact-domain entropy lower rate from class masses with every
positive exponential rate. This is the useful form when a fixed full-coordinate
Gaussian box has mass `exp(-o(D_n))`. -/
theorem entropy_rate_of_exponentially_large_native_class_mass
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    {d : ℕ} (hd : 2 ≤ d) (K : Set (C(α, ℝ)))
    (r β : ℝ) (hr : 0 < r)
    (synthesis : ∀ n : ℕ,
      (LayerIndex d n → ℝ) →ₗ[ℝ] C(α, ℝ))
    (hsup : ∀ (n : ℕ) (x : LayerIndex d n → ℝ), ∀ s ∈ cubeSet d,
      ∃ y : α, synthesis n x y = bumpSynthesis AdmissibleBump.smoothAtomAdmissible x s)
    (hclass : ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
        ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
          productStandardGaussian (LayerIndex d n)
            {x | (a*periodicSynthesisScale d n r β) • synthesis n x ∈ K}) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  obtain ⟨a₀,b,ha₀,hb,hconf⟩ := AlignmentPaperConfinementBridge.norm_confinement_all_grades hd
    (fun n z => synthesis n z) hsup
  obtain ⟨a,ha,N₀,hclass₀⟩ := hclass (b/4) (by positivity)
  let s : ℕ := max 1 ⌈(4/b)⌉₊
  have hs : 1 ≤ s := le_max_left _ _
  have hceil : 4/b ≤ (s:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 ⌈(4/b)⌉₊)
  have hbs : 2 ≤ (3*b/4)*(s:ℝ) := by
    have h := (div_le_iff₀ hb).1 hceil
    nlinarith
  have htwo : 1 ≤ 2*s := by omega
  obtain ⟨k₀,hk₀,hgrade⟩ :=
    nativeEntropyCrossing_multiple_eventually_ge hd htwo (max N₀ s)
  let η : ℝ := a₀ / 2
  have hη : 0 < η := half_pos ha₀
  have hcover : ∀ (k : ℕ) (hk : k₀ ≤ k),
      ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber
        (NNReal.mk ((a*η)*periodicNativeRadius d
          (nativeEntropyCrossing d ((2*s)*k) (by omega)) r β)
          (mul_pos (mul_pos ha hη) (periodicNativeRadius_pos
            (nativeEntropyCrossing_bracket hd (by nlinarith [hk] : 2≤(2*s)*k)).1)).le) K := by
    intro k hk
    have hk2 : 2 ≤ k := hk₀.trans hk
    let q := nativeEntropyCrossing d ((2*s)*k) (by omega)
    have hsk : 2 ≤ (2*s)*k := by nlinarith
    have hbr := nativeEntropyCrossing_bracket hd hsk
    have hq : 0 < q := hbr.1
    have hqN : N₀ ≤ q := (le_max_left N₀ s).trans (hgrade k hk)
    have hqs : s ≤ q := (le_max_right N₀ s).trans (hgrade k hk)
    let D : ℝ := nativeDimension d (2*q)
    have hDk : (2*(s:ℝ))*(k:ℝ) ≤ D := by
      have h := hbr.2.2.1
      simpa [D, q, Nat.cast_mul] using h
    have hDs : (s:ℝ)*(k:ℝ) ≤ D := by nlinarith [hDk]
    let Q := ENNReal.ofReal (Real.exp (-b*D))
    let T := ENNReal.ofReal (Real.exp (-(b/4)*D))
    have hTpos : 0<T := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    have hgap := CameronMartinRate.dyadic_exponential_mass_lt hk2
      (by positivity : 0 < 3*b/4) hDs hbs
    have hsplit : ENNReal.ofReal (Real.exp (-(3*b/4)*D))*T = Q := by
      dsimp [T, Q]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    have hbudget : ((2^(k-1):ℕ):ℝ≥0∞)*Q < T := by
      have hTtop : T < ⊤ := by dsimp [T]; exact ENNReal.ofReal_lt_top
      have hscaled :
          ((2^(k-1):ℕ):ℝ≥0∞)*Q < (3/4:ℝ≥0∞)*T := by
        calc
          _ = T * (((2^(k-1):ℕ):ℝ≥0∞) * ENNReal.ofReal
              (Real.exp (-(3*b/4)*D))) := by rw [← hsplit]; ac_rfl
          _ < T*(3/4:ℝ≥0∞) :=
            ENNReal.mul_lt_mul_right hTpos.ne' hTtop.ne hgap
          _ = _ := by ac_rfl
      have hthree : (3/4:ℝ≥0∞)<1 := by
        apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
        norm_num
      calc
        _ < (3/4:ℝ≥0∞)*T := hscaled
        _ = T*(3/4:ℝ≥0∞) := by ac_rfl
        _ < T*1 := ENNReal.mul_lt_mul_right hTpos.ne' hTtop.ne hthree
        _ = 1*T := by ac_rfl
        _ = T := by simp
    let A : ℝ := a*periodicSynthesisScale d (2*q) r β
    let ε₀ : ℝ := a₀*Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))
    let ρ : ℝ := (a*η)*periodicNativeRadius d q r β
    have hA : 0 < A := mul_pos ha (periodicSynthesisScale_pos (by omega) r β)
    have hρ : 0 < ρ := mul_pos (mul_pos ha hη) (periodicNativeRadius_pos hq)
    have hρε : 2 * ρ ≤ A*ε₀ := by
      refine le_of_eq ?_
      have heq := periodicSynthesisScale_mul_confinement (d:=d) (q:=q) (by omega) a η r β
      have h2 : 2 * η = a₀ := by dsimp [η]; ring
      calc 2 * ρ = A * ((2 * η) * Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))) := by
            rw [show ρ = A * (η * Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))) from heq.symm]
            ring
        _ = A*ε₀ := by rw [h2]
    have hconfQ : productStandardGaussian (LayerIndex d (2*q))
        {x | ‖synthesis (2*q) x‖ ≤ ε₀} ≤ Q := by
      have h := ENNReal.ofReal_le_ofReal (hconf (2*q) (by omega))
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
      exact h
    have hmassE : T ≤ productStandardGaussian (LayerIndex d (2*q))
        {x | A • synthesis (2*q) x ∈ K} := by
      simpa [T, D, A] using hclass₀ (2*q) (by omega)
    have : Nonempty (LayerIndex d (2*q)) := nativeLayerIndex_nonempty d (2*q) (by omega)
    exact AlignmentPaperConfinementBridge.scaled_externalCover_gt (synthesis (2*q)) hA
      ⟨ρ, hρ.le⟩ hρε {x | A • synthesis (2*q) x ∈ K} K Q _ (fun x hx => hx) hconfQ
      (hbudget.trans_le hmassE)
  obtain ⟨c,hc,hentropy⟩ := periodic_entropy_rate_of_cover_at_multiple K hd htwo hk₀
    r β (a*η) hr (mul_pos ha hη) hcover
  exact ⟨c,hc,k₀,hk₀,hentropy⟩

end BrownianSharp.AlignmentExponentialBoxEntropy
