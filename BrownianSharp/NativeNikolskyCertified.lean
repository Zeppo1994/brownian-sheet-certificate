import BrownianSharp.NativeNikolskyEndpoint
import BrownianSharp.NativeNikolskyProductRoot
import BrownianSharp.NativeNikolskyENNRealProfile
import Mathlib.Tactic

/-! The unconditional native Nikolsky block bound and entropy endpoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

private theorem real_dyadic_rpow_gap (a : ℝ) (m : ℕ) :
    (2 : ℝ) ^ (-a * (m : ℝ)) = ((2 : ℝ) ^ (-a)) ^ m := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

private theorem native_real_profile_eq {d : ℕ}
    (s t : Fin d → ℕ) (r : ℝ) (K : ℕ) :
    nativeNikolskyRealShapeWeight t ((2 : ℝ)^(-r))
        ((2 : ℝ)^(-((K:ℝ)-r))) s =
      nativeNikolskyShapeWeightReal s t r K := by
  unfold nativeNikolskyRealShapeWeight nativeNikolskyShapeWeightReal
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : t i ≤ s i
  · simp only [h, ↓reduceIte]
    rw [← real_dyadic_rpow_gap]
  · simp only [h, ↓reduceIte]
    rw [← real_dyadic_rpow_gap]

private theorem ofReal_twoSidedGeometricFactor {d : ℕ} (r K : ℝ)
    (hr : 0 < r) (hKr : r < K) :
    (((1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
      ENNReal.ofReal ((2:ℝ)^(-(K-r))) *
        (1 - ENNReal.ofReal ((2:ℝ)^(-(K-r))))⁻¹)^d) =
      ENNReal.ofReal (((1 - (2:ℝ)^(-r))⁻¹ +
        (2:ℝ)^(-(K-r)) * (1 - (2:ℝ)^(-(K-r)))⁻¹)^d) := by
  have hlow : (2:ℝ)^(-r) < 1 :=
    (real_dyadic_profile_bases_lt_one hr hKr).1
  have hhigh : (2:ℝ)^(-(K-r)) < 1 :=
    (real_dyadic_profile_bases_lt_one hr hKr).2
  have hlow0 : 0 ≤ (2:ℝ)^(-r) := by positivity
  have hhigh0 : 0 ≤ (2:ℝ)^(-(K-r)) := by positivity
  have hInvLow :
      (1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ =
        ENNReal.ofReal ((1-(2:ℝ)^(-r))⁻¹) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (1:ℝ) hlow0,
      ← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 1-(2:ℝ)^(-r))]
  have hInvHigh :
      (1 - ENNReal.ofReal ((2:ℝ)^(-(K-r))))⁻¹ =
        ENNReal.ofReal ((1-(2:ℝ)^(-(K-r)))⁻¹) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (1:ℝ) hhigh0,
      ← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 1-(2:ℝ)^(-(K-r)))]
  rw [hInvLow, hInvHigh, ← ENNReal.ofReal_mul hhigh0,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_pow (by positivity : 0 ≤
      (1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-(K-r))*(1-(2:ℝ)^(-(K-r)))⁻¹)]

/-- Uniform block bound for the actual native synthesis on the simultaneous
coefficient event. The dimension-only geometric factor is absorbed into `C`. -/
theorem periodicNative_uniformNikolskyBlockBound
    {d : ℕ} (hd : 2 ≤ d) (p r : ℝ) (hp : 1 < p) (hr : 0 < r)
    (K : ℕ) (hK : Even K) (hKpos : 0 < K) (hKr : r < (K:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      x ∈ smoothShapeJointGoodEvent p Finset.univ → ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (periodicNativeSynthesisLinear x) ≤
          ENNReal.ofReal (C * (2:ℝ)^(r*(n:ℝ))) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ls0,Lp0,Cd0,hLs0,hLp0,hCd0,hscalar0,hprofile0,hderiv0⟩ :=
    exists_fixedShapeBlock_nativeDecay_constants hK hKpos
  let Ls : ℝ := Ls0+1
  let Lp : ℝ := Lp0+1
  let Cd : ℝ := Cd0+1
  let G : ℝ := 1+gaussianAbsoluteMoment p
  have hLs : 0 < Ls := by dsimp [Ls]; linarith
  have hLp : 0 < Lp := by dsimp [Lp]; linarith
  have hCd : 0 < Cd := by dsimp [Cd]; linarith
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have hm := gaussianAbsoluteMoment_nonneg p
    linarith
  have hG : 0 < G := by dsimp [G]; have hm := gaussianAbsoluteMoment_nonneg p; linarith
  have hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Ls := by
    intro q
    have h := hscalar0 q
    dsimp [Ls]
    linarith
  have hprofile : ∀ (q : ℕ), 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lp := by
    intro q hq
    have h := hprofile0 q hq
    dsimp [Lp]
    calc
      _ ≤ ‖inverseProfileScale q K‖ * Lp0 := h
      _ ≤ ‖inverseProfileScale q K‖ * (Lp0+1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have hderiv : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ Cd := by
    intro y
    have h := hderiv0 y
    dsimp [Cd]
    linarith
  let qlR : ℝ := (2:ℝ)^(-r)
  let qhR : ℝ := (2:ℝ)^(-((K:ℝ) - r))
  let ql : ℝ≥0∞ := ENNReal.ofReal qlR
  let qh : ℝ≥0∞ := ENNReal.ofReal qhR
  have hqRlow : 0 ≤ qlR := by dsimp [qlR]; positivity
  have hqRhigh : 0 ≤ qhR := by dsimp [qhR]; positivity
  have hq : ql < 1 ∧ qh < 1 := by
    have h := ennreal_dyadic_profile_bases_lt_one hr hKr
    exact ⟨by simpa [ql, qlR] using h.1, by simpa [qh, qhR] using h.2⟩
  let C₀ : ℝ := (2*G)^(1/p) * (Ls+Lp)^d * (1+Cd)^d
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have : 0 < 1/p := by positivity
    positivity
  let F : ℝ := ((1-qlR)⁻¹ + qhR*(1- qhR)⁻¹)^d
  have hF : 0 < F := by
    dsimp [F]
    have hlow : qlR < 1 := (real_dyadic_profile_bases_lt_one hr hKr).1
    have hhigh : qhR < 1 := (real_dyadic_profile_bases_lt_one hr hKr).2
    have hlow0 : 0 ≤ qlR := hqRlow
    have hhigh0 : 0 ≤ qhR := hqRhigh
    positivity
  let C : ℝ := C₀*F
  have hC : 0 < C := by dsimp [C]; exact mul_pos hC₀ hF
  have hLsNonneg : 0 ≤ Ls := by dsimp [Ls]; linarith [hLs0]
  have hLpNonneg : 0 ≤ Lp := by dsimp [Lp]; linarith [hLp0]
  have hCdNonneg : 0 ≤ Cd := by dsimp [Cd]; linarith [hCd0]
  refine ⟨C,hC,?_⟩
  intro n x hx t
  have hshape : ∀ s : Shape d n,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) ≤
        ENNReal.ofReal (C₀*(2:ℝ)^(r*(n:ℝ))) *
          nativeNikolskyShapeWeight t ql qh (fun i => s.1 i) := by
    intro s
    have hsum : ∑ i, s.1 i = n := by
      have hh := (Finset.mem_finsuppAntidiag'.mp s.2).1
      simpa [Finsupp.sum_fintype] using hh
    let c : DyadicShapeCell d (fun i => s.1 i) → ℝ := fun j => x ⟨s,j⟩
    let c : DyadicShapeCell d (fun i => s.1 i) → ℝ := fun j => x ⟨s,j⟩
    have hcoeff :
        (∑ j : DyadicShapeCell d (fun i => s.1 i),
          |c j|^p) ≤ 2*(2:ℝ)^n*G := by
      have h := smoothShapeCoefficientEnergy_le_on_joint_event p hp0 hx s
      simpa [smoothShapeCoefficientEnergy, G, c] using h
    have hroot := fixedShape_weightedBlockNorm_le_nikolskyShape
      (fun i => s.1 i) t c p r (le_of_lt hp) K hK hKpos
      Ls Lp Cd G hLsNonneg hLpNonneg hCdNonneg hG0
      hscalar hprofile hderiv hsum hcoeff
    have hrealprofile :
        nativeNikolskyRealShapeWeight t qlR qhR (fun i => s.1 i) =
          nativeNikolskyShapeWeightReal (fun i => s.1 i) t r K := by
      simpa [qlR, qhR] using
        native_real_profile_eq (fun i => s.1 i) t r K
    have hprofileENN :
        nativeNikolskyShapeWeight t ql qh (fun i => s.1 i) =
          ENNReal.ofReal (nativeNikolskyShapeWeightReal (fun i => s.1 i) t r K) := by
      calc
        _ = nativeNikolskyENNRealShapeWeight t (ENNReal.ofReal qlR)
              (ENNReal.ofReal qhR) (fun i => s.1 i) := by rfl
        _ = ENNReal.ofReal
              (nativeNikolskyRealShapeWeight t qlR qhR (fun i => s.1 i)) :=
            nativeNikolskyShapeWeight_eq_ofReal_real t qlR qhR hqRlow hqRhigh
              (fun i => s.1 i)
        _ = _ := by rw [hrealprofile]
    have hcoefPos : 0 ≤ C₀*(2:ℝ)^(r*(n:ℝ)) := by positivity
    have hrealPos : 0 ≤ nativeNikolskyShapeWeightReal (fun i => s.1 i) t r K := by
      unfold nativeNikolskyShapeWeightReal
      exact Finset.prod_nonneg fun i hi => by split_ifs <;> positivity
    have hfactor :
        ENNReal.ofReal (C₀*(2:ℝ)^(r*(n:ℝ))) *
          nativeNikolskyShapeWeight t ql qh (fun i => s.1 i) =
        ENNReal.ofReal (C₀*(2:ℝ)^(r*(n:ℝ)) *
          nativeNikolskyShapeWeightReal (fun i => s.1 i) t r K) := by
      rw [hprofileENN, ← ENNReal.ofReal_mul hcoefPos]
    rw [hfactor]
    exact hroot
  have hagg := periodicNative_weightedBlockNorm_le_of_shapeEnvelope_uniform
    x p r C₀ (le_of_lt hp) ql qh t hq.1 hq.2 hshape
  have hfactor :
      (((1-ql)⁻¹ + qh*(1-qh)⁻¹)^d) = ENNReal.ofReal F := by
    simpa [ql, qh, qlR, qhR, F] using
      ofReal_twoSidedGeometricFactor r (K:ℝ) hr hKr
  rw [hfactor] at hagg
  have hmul : ENNReal.ofReal (C₀*(2:ℝ)^(r*(n:ℝ))) * ENNReal.ofReal F =
      ENNReal.ofReal (C*(2:ℝ)^(r*(n:ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C₀*(2:ℝ)^(r*(n:ℝ)))]
    apply congrArg ENNReal.ofReal
    dsimp [C]
    ring
  rw [hmul] at hagg
  exact hagg

/-- The finite-p Nikolsky entropy lower bound, now with the deterministic
native block estimate discharged from the actual coefficient cutoff event. -/
theorem periodicNikolsky_entropy_of_native_good_event
    {d : ℕ} (hd : 2 ≤ d) (p r : ℝ) (hp : 1 < p) (hr : 0 < r)
    (K : ℕ) (hK : Even K) (hKpos : 0 < K) (hKr : r < (K:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        ((r+1/2)*((d-1:ℕ):ℝ)+1/2)) ≤
          HaarQuarter.TheoremD.entropyNumber k
          {f : Torus.RealPeriodic d | SmoothResolution.NikolskyUnitBall
              (ENNReal.ofReal p) r f} := by
  obtain ⟨C,hC,hbound⟩ := periodicNative_uniformNikolskyBlockBound
    hd p r hp hr K hK hKpos hKr
  exact periodicNikolsky_entropy_of_native_uniform_block_bound
    hd p r C hp hr hC hbound

end BrownianSharp
