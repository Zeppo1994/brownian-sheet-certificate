import BrownianSharp.AlignmentFourierLipschitz
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentTorusSampling
open BrownianSharp.AlignmentPeriodicWidthRealification

def samplingGridSize (d K L M : ℕ) : ℕ := K*2^((d+2)*L+M)

theorem samplingGridSize_pos {d K L M : ℕ} (hK : 0<K) :
    0 < samplingGridSize d K L M := by
  unfold samplingGridSize
  positivity

theorem grid_log_card_bound (d K E N : ℕ)
    (hN : N+1 ≤ (K+1)*2^E) :
    Real.log (2*(Fintype.card (Fin d → Fin (N+1)):ℝ)+2) ≤
      Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+(d:ℝ)*(E:ℝ)*Real.log 2 := by
  have hcard : (Fintype.card (Fin d → Fin (N+1)):ℝ) ≤
      (((K:ℝ)+1)*(2:ℝ)^E)^d := by
    rw [torus_grid_card]
    exact_mod_cast Nat.pow_le_pow_left hN d
  have hone : (1:ℝ) ≤ (((K:ℝ)+1)*(2:ℝ)^E)^d := by
    have hp : (1:ℝ) ≤ (2:ℝ)^E := one_le_pow₀ (by norm_num)
    apply one_le_pow₀
    nlinarith
  have harg : 2*(Fintype.card (Fin d → Fin (N+1)):ℝ)+2 ≤
      4*((((K:ℝ)+1)*(2:ℝ)^E)^d) := by linarith
  have hpos : (0:ℝ) < ((K:ℝ)+1)*(2:ℝ)^E := by positivity
  calc
    _ ≤ Real.log (4*((((K:ℝ)+1)*(2:ℝ)^E)^d)) :=
      Real.log_le_log (by positivity) harg
    _ = _ := by
      rw [Real.log_mul (by norm_num) (pow_pos hpos _).ne',
        Real.log_pow,Real.log_mul (by positivity) (pow_pos (by norm_num : (0:ℝ)<2) E).ne',
        Real.log_pow]
      ring

theorem samplingGridSize_log_card (d K L M : ℕ) :
    Real.log (2*(Fintype.card (Fin d → Fin (samplingGridSize d K L M+1)):ℝ)+2) ≤
      Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
        (d:ℝ)*(((d+2)*L+M:ℕ):ℝ)*Real.log 2 := by
  apply grid_log_card_bound
  unfold samplingGridSize
  have hp : 1 ≤ 2^((d+2)*L+M) := one_le_pow₀ (by norm_num)
  nlinarith

theorem periodic_sampling_grid {d L : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (hr : 0≤r) (hS : ∀ s∈S, ∑ j,s j ≤ L)
    (K M : ℕ) (hK : 0<K) (hKC : 2*samplingConstant d ≤ (K:ℝ)) :
    ∃ φ : (Fin d → Fin (samplingGridSize d K L M+1)) →
        C(UnitAddTorus (Fin d),ℝ),
      (∀ j t, 0≤φ j t) ∧ (∀ t, ∑ j,φ j t=1) ∧
      (∀ j t, φ j t ≠ 0 →
        ‖periodicFeatureVector S r t-
          periodicFeatureVector S r (torusGridPoint j)‖ ≤ ((2:ℝ)^M)⁻¹) := by
  let N := samplingGridSize d K L M
  have hN := samplingGridSize_pos (d:=d) (L:=L) (M:=M) hK
  obtain ⟨φ,hφ,hsum,hosc⟩ := periodic_grid_partition S r N hN
  refine ⟨φ,hφ,hsum,?_⟩
  intro j t ht
  apply (hosc j t ht).trans
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hscale : 2*periodicFeatureLipschitzConstant S r*(2:ℝ)^M ≤ (N:ℝ) := by
    calc
      _ ≤ 2*(samplingConstant d*(2:ℝ)^((d+2)*L))*(2:ℝ)^M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (periodicFeatureLipschitzConstant_exp_bound S r hr hS)
            (by norm_num)) (by positivity)
      _ = (2*samplingConstant d)*(2:ℝ)^((d+2)*L+M) := by rw [pow_add]; ring
      _ ≤ (K:ℝ)*(2:ℝ)^((d+2)*L+M) :=
        mul_le_mul_of_nonneg_right hKC (by positivity)
      _ = _ := by simp only [N,samplingGridSize,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← one_div, ← mul_div_assoc]
  apply (div_le_div_iff₀ hNr (pow_pos (by norm_num : (0:ℝ)<2) M)).2
  simpa only [one_mul,mul_assoc,mul_comm,mul_left_comm] using hscale

theorem exists_sampling_integer (d : ℕ) :
    ∃ K : ℕ, 0<K ∧ 2*samplingConstant d ≤ (K:ℝ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (2*samplingConstant d)
  refine ⟨K,?_,hK.le⟩
  have hc := samplingConstant_ge_one d
  by_contra h
  have hzero : K=0 := by omega
  simp only [hzero,Nat.cast_zero] at hK
  linarith

end BrownianSharp.AlignmentTorusSampling
