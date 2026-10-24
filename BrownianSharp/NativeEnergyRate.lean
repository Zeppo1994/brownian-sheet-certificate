import BrownianSharp.NativeClassReindex
import BrownianSharp.SmoothEnergyNormalization
import BrownianSharp.PeriodicNativeEntropy

/-! Literal smooth Gaussian energy rates imply entropy bounds at the exact
native normalization. These application lemmas expose only the energy
estimate; all event, scaling, confinement and index steps are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace BrownianSharp
open Torus PeriodicCover SmoothResolution

def nativeClassNormScale (d n : ℕ) (r γ : ℝ) : ℝ :=
  (2:ℝ)^(r*(n:ℝ)) * (hyperbolicCount d n)^γ

theorem nativeClassNormScale_pos {d n : ℕ} (hd : 1 ≤ d) (r γ : ℝ) :
    0 < nativeClassNormScale d n r γ := by
  unfold nativeClassNormScale
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos (hyperbolicCount_pos hd) _)

theorem periodicSynthesisScale_eq_inverseNormScale {d n : ℕ}
    (r β : ℝ) : periodicSynthesisScale d n r β =
      (nativeClassNormScale d n r (1/2-β))⁻¹ := by
  unfold periodicSynthesisScale nativeClassNormScale
  have htwo : -r*(n:ℝ) = -(r*(n:ℝ)) := by ring
  have hbeta : β-1/2 = -(1/2-β) := by ring
  rw [htwo,hbeta,Real.rpow_neg (by norm_num),Real.rpow_neg
    (show 0 ≤ hyperbolicCount d n by unfold hyperbolicCount; positivity),mul_inv_rev]
  ring

/-- Exact Sobolev entropy from a proved expected-energy family with its
sharp square-root shell normalization. -/
theorem periodicSobolev_entropy_of_native_expected_energy_rate
    {d : ℕ} (hd : 2 ≤ d) (p r C : ℝ) (hp : 0 < p)
    (hr : 0 < r) (hC : 0 < C)
    (hmean : ∀ n : ℕ,
      (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
        (∫⁻ x : UnitAddTorus (Fin d),
          (squareFunctionSquared r (gaussianSynthesis (nativeFinAtoms d n) z) x)^(p/2))
        ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (C*(nativeClassNormScale d n r (1/2))^p)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+1/2)) ≤ HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | SobolevUnitBall p r f} := by
  obtain ⟨a,ha,hnormalize⟩ := exists_smooth_energy_normalizer p C hp hC
  have hclass : ∀ n : ℕ, 0 ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r 0) • periodicNativeSynthesisLinear x ∈
            {f : RealPeriodic d | SobolevUnitBall p r f}} := by
    intro n hn
    let L := nativeClassNormScale d n r (1/2)
    have hL : 0 < L := nativeClassNormScale_pos (by omega) r (1/2)
    have hA : 0 < a*periodicSynthesisScale d n r 0 :=
      mul_pos ha (periodicSynthesisScale_pos (by omega) r 0)
    have hscale : ENNReal.ofReal ((a*periodicSynthesisScale d n r 0)^p)*
        (2*ENNReal.ofReal (C*L^p)) ≤ 1 := by
      have heq : a*periodicSynthesisScale d n r 0 = a/L := by
        rw [periodicSynthesisScale_eq_inverseNormScale]
        simp only [sub_zero, div_eq_mul_inv]
        rfl
      rw [heq]
      exact hnormalize L hL
    exact (shapeCutoff_le_half (by omega)).trans
      (nativeSobolev_scaled_unitBall_mass_of_mean p r hp.le hA
        (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top (hmean n) hscale)
  obtain ⟨c,hc,k₀,hk₀,hent⟩ := periodic_entropy_rate_of_scaled_native_class_mass hd
    {f : RealPeriodic d | SobolevUnitBall p r f} r 0 a hr ha 0 hclass
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  simpa using hent k hk

/-- Finite-theta Besov entropy from the exact native expected-energy rate. -/
theorem periodicBesov_entropy_of_native_expected_energy_rate
    {d : ℕ} (hd : 2 ≤ d) (p theta r C : ℝ) (hp : 0 < p)
    (htheta : 1 ≤ theta) (hr : 0 < r) (hC : 0 < C)
    (hmean : ∀ n : ℕ,
      (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
        smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
          (gaussianSynthesis (nativeFinAtoms d n) z)
        ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (C*(nativeClassNormScale d n r theta⁻¹)^theta)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        ((r+1/2-theta⁻¹)*((d-1:ℕ):ℝ)+1/2)) ≤ HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r (ENNReal.ofReal theta) f} := by
  have hthetap : 0 < theta := by linarith
  obtain ⟨a,ha,hnormalize⟩ := exists_smooth_energy_normalizer theta C hthetap hC
  let beta : ℝ := 1/2-theta⁻¹
  have hclass : ∀ n : ℕ, 0 ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r beta) • periodicNativeSynthesisLinear x ∈
            {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r (ENNReal.ofReal theta) f}} := by
    intro n hn
    let L := nativeClassNormScale d n r theta⁻¹
    have hL : 0 < L := nativeClassNormScale_pos (by omega) r theta⁻¹
    have hA : 0 < a*periodicSynthesisScale d n r beta :=
      mul_pos ha (periodicSynthesisScale_pos (by omega) r beta)
    have heq : a*periodicSynthesisScale d n r beta = a/L := by
      rw [periodicSynthesisScale_eq_inverseNormScale]
      have hb : 1/2-beta = theta⁻¹ := by dsimp [beta]; ring
      rw [hb]
      rfl
    have hscale : ENNReal.ofReal ((a*periodicSynthesisScale d n r beta)^
        (ENNReal.ofReal theta).toReal) * (2*ENNReal.ofReal (C*L^theta)) ≤ 1 := by
      rw [ENNReal.toReal_ofReal hthetap.le, heq]
      exact hnormalize L hL
    exact (shapeCutoff_le_half (by omega)).trans
      (nativeBesov_scaled_unitBall_mass_of_mean (ENNReal.ofReal p)
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top r ENNReal.ofReal_ne_top hA
        (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top (hmean n) hscale)
  obtain ⟨c,hc,k₀,hk₀,hent⟩ := periodic_entropy_rate_of_scaled_native_class_mass hd
    {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r (ENNReal.ofReal theta) f}
    r beta a hr ha 0 hclass
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  have heq : r*((d-1:ℕ):ℝ)+(1/2+beta*((d-1:ℕ):ℝ)) =
      (r+1/2-theta⁻¹)*((d-1:ℕ):ℝ)+1/2 := by dsimp [beta]; ring
  simpa only [heq] using hent k hk

end BrownianSharp
