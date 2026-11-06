import BrownianSharp.AlignmentExponentialContinuousCover
import BrownianSharp.PeriodicSynthesisScale
import BrownianSharp.AlignmentPaperConfinementBridge
import BrownianSharp.NativeScaleCover
import BrownianSharp.PeriodicCoverRate
import Mathlib.Tactic

/-! Compact-domain version of the native entropy lower bound. The only
synthesis-specific premise is that every value of the smooth cube synthesis is
a value of the given synthesis; the confinement input is Theorem 2.1. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentExponentialNativeEntropy
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumGenericBump
  AlignmentPaperGenericBumpCertified

/-- Generic compact-domain entropy lower rate from a class-mass bound for a
finite Gaussian synthesis family. -/
theorem entropy_rate_of_scaled_native_class_mass
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    {d : ℕ} (hd : 2 ≤ d) (K : Set (C(α, ℝ)))
    (r β a : ℝ) (hr : 0 < r) (ha : 0 < a) (N₀ : ℕ)
    (synthesis : ∀ n : ℕ,
      (LayerIndex d n → ℝ) →ₗ[ℝ] C(α, ℝ))
    (hsup : ∀ (n : ℕ) (x : LayerIndex d n → ℝ), ∀ s ∈ cubeSet d,
      ∃ y : α, synthesis n x y = bumpSynthesis AdmissibleBump.smoothAtomAdmissible x s)
    (hclass : ∀ n : ℕ, N₀ ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r β) • synthesis n x ∈ K}) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  obtain ⟨a₀,b,ha₀,hb,hconf⟩ := AlignmentPaperConfinementBridge.norm_confinement_all_grades hd
    (fun n z => synthesis n z) hsup
  let s : ℕ := max 1 ⌈(2/b)⌉₊
  have hs : 1 ≤ s := le_max_left _ _
  have hceil : 2/b ≤ (s:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 ⌈(2/b)⌉₊)
  have hbs : 2 ≤ b*(s:ℝ) := by
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
    let S : ℕ := Nat.choose (2*q+d-1) (d-1)
    let D : ℝ := nativeDimension d (2*q)
    have hS : 0 < S := Nat.choose_pos (by omega)
    have hDk : (2*(s:ℝ))*(k:ℝ) ≤ D := by
      have h := hbr.2.2.1
      simpa [D, q, Nat.cast_mul] using h
    have hDS : (2*(s:ℝ))*(S:ℝ) ≤ D := by
      have hnat : 2*s ≤ 2^(2*q) :=
        (Nat.mul_le_mul_left 2 hqs).trans (Nat.le_of_lt (2*q).lt_two_pow_self)
      have hreal : 2*(s:ℝ) ≤ (2:ℝ)^(2*q) := by exact_mod_cast hnat
      change (2*(s:ℝ))*(S:ℝ) ≤ (2:ℝ)^(2*q)*hyperbolicCount d (2*q)
      have hSid : (S:ℝ) = hyperbolicCount d (2*q) := rfl
      rw [← hSid]
      exact mul_le_mul_of_nonneg_right hreal (Nat.cast_nonneg _)
    have hbudget := dyadic_exponential_mass_lt_shape_cutoff hk2 hb hbs hDk hDS
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
    let Q := ENNReal.ofReal (Real.exp (-b*D))
    have hconfQ : productStandardGaussian (LayerIndex d (2*q))
        {x | ‖synthesis (2*q) x‖ ≤ ε₀} ≤ Q := by
      have h := ENNReal.ofReal_le_ofReal (hconf (2*q) (by omega))
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
      exact h
    have : Nonempty (LayerIndex d (2*q)) := nativeLayerIndex_nonempty d (2*q) (by omega)
    exact AlignmentPaperConfinementBridge.scaled_externalCover_gt (synthesis (2*q)) hA
      ⟨ρ, hρ.le⟩ hρε {x | A • synthesis (2*q) x ∈ K} K Q _ (fun x hx => hx) hconfQ
      (hbudget.trans_le (hclass (2*q) (by omega)))
  obtain ⟨c,hc,hentropy⟩ := periodic_entropy_rate_of_cover_at_multiple K hd htwo hk₀
    r β (a*η) hr (mul_pos ha hη) hcover
  exact ⟨c,hc,k₀,hk₀,hentropy⟩

end BrownianSharp.AlignmentExponentialNativeEntropy
