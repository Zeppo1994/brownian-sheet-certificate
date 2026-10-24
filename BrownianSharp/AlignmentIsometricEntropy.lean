import BrownianSharp.AlignmentLatestStatements
import Mathlib.Topology.MetricSpace.CoveringNumbers

noncomputable section
open scoped ENNReal NNReal
open HaarQuarter.TheoremD
namespace BrownianSharp.AlignmentIsometricEntropy

theorem external_cover_under_isometry {X Y : Type*} [EMetricSpace X] [PseudoEMetricSpace Y]
    (f : X→Y) (hf : Isometry f) (K : Set X) (ρ : ℝ≥0) :
    Metric.externalCoveringNumber (2*ρ) K ≤ Metric.externalCoveringNumber ρ (f '' K) := by
  calc
    _ ≤ Metric.coveringNumber (2*ρ) K := Metric.externalCoveringNumber_le_coveringNumber _ _
    _ = Metric.coveringNumber (2*ρ) (f '' K) := (hf.coveringNumber_image).symm
    _ ≤ _ := Metric.coveringNumber_two_mul_le_externalCoveringNumber ρ _

/-- External centers can cost at most a factor two when an isometric image
is placed in a larger ambient space. -/
theorem entropy_lower_under_isometry {X Y : Type*} [EMetricSpace X] [PseudoEMetricSpace Y]
    (f : X→Y) (hf : Isometry f) (K : Set X) (k : ℕ) (u : ℝ)
    (hu : ENNReal.ofReal u ≤ entropyNumber k K) :
    ENNReal.ofReal (u/2) ≤ entropyNumber k (f '' K) := by
  unfold entropyNumber at *
  apply le_sInf
  intro r hr
  obtain ⟨ρ,rfl,hρ⟩ := hr
  have hcover : Metric.externalCoveringNumber (2*ρ) K ≤ ((2^(k-1):ℕ):ℕ∞) :=
    (external_cover_under_isometry f hf K ρ).trans hρ
  have hsmall : sInf {r : ENNReal | ∃ δ : ℝ≥0,
      r = δ ∧ Metric.externalCoveringNumber δ K ≤ ((2^(k-1):ℕ):ℕ∞)} ≤
      ((2*ρ:ℝ≥0):ENNReal) := sInf_le ⟨2*ρ,rfl,hcover⟩
  have hreal : u ≤ (2*ρ:ℝ≥0) := ENNReal.ofReal_le_coe.mp (hu.trans hsmall)
  apply ENNReal.ofReal_le_coe.mpr
  have : u ≤ 2*(ρ:ℝ) := by simpa using hreal
  linarith


theorem entropyNumber_antitone {X : Type*} [PseudoEMetricSpace X]
    (K : Set X) {m n : ℕ} (hmn : m≤n) :
    entropyNumber n K ≤ entropyNumber m K := by
  unfold entropyNumber
  apply le_sInf
  intro r hr
  obtain ⟨ρ,rfl,hρ⟩ := hr
  apply sInf_le
  refine ⟨ρ,rfl,hρ.trans ?_⟩
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<2) (Nat.sub_le_sub_right hmn 1)

/-- A finite initial segment only changes the constant of a positive entropy
rate. This supplies the all-index premise in the Carl width comparison. -/
theorem entropy_lower_uniformize {X : Type*} [PseudoEMetricSpace X]
    (K : Set X) (rate : ℕ→ℝ)
    (hRate : ∀ n, 0≤rate n) (hRatePos : ∀ n, 2≤n → 0<rate n)
    (c : ℝ) (hc : 0<c) (n₀ : ℕ)
    (h : ∀ n, n₀≤n → ENNReal.ofReal (c*rate n) ≤ entropyNumber n K) :
    ∃ c' : ℝ, 0<c' ∧ ∀ n, 2≤n →
      ENNReal.ofReal (c'*rate n) ≤ entropyNumber n K := by
  classical
  let N := max 2 n₀
  let A : ℝ := 1+∑ j∈Finset.range N,rate j
  have hA : 0<A := by
    dsimp [A]
    have hs : 0≤∑ j∈Finset.range N,rate j := Finset.sum_nonneg (fun j _ => hRate j)
    linarith
  have hN2 : 2≤N := le_max_left _ _
  have hN₀ : n₀≤N := le_max_right _ _
  let c' := min c (c*rate N/A)
  have hc' : 0<c' := lt_min hc (div_pos (mul_pos hc (hRatePos N hN2)) hA)
  have hc'c : c'≤c := min_le_left _ _
  have hc'A : c'*A≤c*rate N := (le_div_iff₀ hA).mp (min_le_right _ _)
  refine ⟨c',hc',?_⟩
  intro n hn
  by_cases hlarge : N≤n
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hc'c (hRate n))).trans (h n (hN₀.trans hlarge))
  · have hnN : n<N := by omega
    have hnA : rate n≤A := by
      have hterm : rate n≤∑ j∈Finset.range N,rate j :=
        Finset.single_le_sum (fun j _ => hRate j) (Finset.mem_range.mpr hnN)
      dsimp [A]
      linarith
    have hvalue : c'*rate n≤c*rate N :=
      (mul_le_mul_of_nonneg_left hnA hc'.le).trans hc'A
    exact (ENNReal.ofReal_le_ofReal hvalue).trans
      ((h N hN₀).trans (entropyNumber_antitone K hnN.le))

end BrownianSharp.AlignmentIsometricEntropy
