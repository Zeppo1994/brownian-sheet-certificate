import BrownianSharp.AlignmentPaperMultivariateFaceInverse
import BrownianSharp.AlignmentPaperFiniteFaceMixedLp
import BrownianSharp.AlignmentPaperAnchoredLpFacePartition
import BrownianSharp.AlignmentPaperJointSamplingBudget
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
import BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
import BrownianSharp.AlignmentPaperAnchoredLpParityFourier
import BrownianSharp.AlignmentPaperAnchoredLp
import BrownianSharp.AlignmentPeriodicFourierReconstruction

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpGradeBudget

open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpParityFourier
open BrownianSharp.AlignmentPaperAnchoredLpFacePartition
open BrownianSharp.AlignmentPaperMultivariateFaceInverse
open BrownianSharp.AlignmentPaperInverseDerivativeNeighbor
open BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity
open BrownianSharp.ScalarAtomVariance
open BrownianSharp.AlignmentPaperFiniteFaceMixedLp
open BrownianSharp.AlignmentPaperJointSamplingBudget
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

local instance gradeBudgetTorusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [BrownianSharp.unitAddTorus_volume_eq_productHaar]
  infer_instance

/-- The actual mixed grade norm, before its final `p`th power. -/
def gradeLpEnergy {α S : Type*} [MeasurableSpace α] [Fintype S]
    (p : ℝ) (μ : Measure α) (u : S → α → ℂ) : ℝ :=
  (∑ s : S, (∫ x, ‖u s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ)

/-- The source Lp norm appearing in the finite-face inverse contract. -/
def sourceLpNorm {d : ℕ} (p : ℝ) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) : ℝ :=
  (∫ x : UnitAddTorus (Fin d),
    ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (1 / p)

/-- Convert the proved ENNReal parity-source bound into the ordinary Lp
norm used by the actual finite-face/shape-space triangle inequality. -/
theorem sourceLpNorm_le {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d)) (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    sourceLpNorm p J g ≤ (2:ℝ)^J.card * ‖g‖ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpEn : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hp0
  have hmem := memLp_complex_anchoredFaceSource hp J g
  have hsrcFormula :
      eLpNorm (fun x : UnitAddTorus (Fin d) =>
        (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) =
        ENNReal.ofReal (sourceLpNorm p J g) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top hmem]
    simp [sourceLpNorm, ENNReal.toReal_ofReal hp0.le]
  have hgFormula :
      eLpNorm (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) (cubeMeasure d) =
        ENNReal.ofReal ‖g‖ := by
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g), Lp.norm_def]
  have hbound := complex_anchoredFaceSource_eLpNorm_le hp J g
  have hfac : 0 ≤ (2:ℝ)^J.card := by positivity
  rw [hsrcFormula, hgFormula, ← ENNReal.ofReal_mul hfac] at hbound
  have hnorm : 0 ≤ (‖g‖ : ℝ) := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_nonneg
  have hnonneg : 0 ≤ (2:ℝ)^J.card * ‖g‖ := mul_nonneg hfac hnorm
  exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hbound

/-- The aggregate Lp cost of all actual parity sources is bounded by a fixed
dimension factor. -/
theorem sum_sourceLpNorm_le {d : ℕ} {p : ℝ} (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    (∑ J ∈ (Finset.univ : Finset (Fin d)).powerset, sourceLpNorm p J g) ≤
      4^d * ‖g‖ := by
  classical
  calc
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        (2:ℝ)^J.card * ‖g‖ := by
      apply Finset.sum_le_sum
      intro J hJ
      exact sourceLpNorm_le hp J g
    _ = (∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
          (2:ℝ)^J.card) * ‖g‖ := by rw [Finset.sum_mul]
    _ ≤ 4^d * ‖g‖ := by
      exact mul_le_mul_of_nonneg_right (sum_faceParityCosts_le_four_pow d)
        (by
          have hnorm : 0 ≤ (‖g‖ : ℝ) := by
            rw [Lp.norm_def]
            exact ENNReal.toReal_nonneg
          exact hnorm)

/-- Extending a finite torus Fourier polynomial's index set is exact when
all newly added coefficients vanish. -/
private theorem torusFourierPolynomial_extend_support {d : ℕ}
    (A B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (hAB : A ⊆ B)
    (hzero : ∀ k ∈ B, k ∉ A → c k = 0) :
    torusFourierPolynomial A c = torusFourierPolynomial B c := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [torusFourierPolynomial, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_subset hAB]
  · intro k hk hkA
    rw [hzero k hk hkA]
    simp

private theorem smoothFrequencyBox_subset_faceBox {d : ℕ}
    (s : Fin d → ℕ) :
    SmoothResolution.frequencyBox s ⊆ faceBlockFrequencyBox s := by
  classical
  intro k hk
  have hk' : ∀ i, k i ∈ BrownianSharp.ScalarAtomVariance.scalarFrequencyBox (s i) := by
    simpa [SmoothResolution.frequencyBox,
      BrownianSharp.ScalarAtomVariance.scalarFrequencyBox,
      Fintype.mem_piFinset] using hk
  simp only [faceBlockFrequencyBox, Fintype.mem_piFinset]
  intro i
  have hscale : s i ∈ neighborScales (s i) := by
    simp [neighborScales]
  exact Finset.mem_biUnion.mpr ⟨s i, hscale, hk' i⟩

/-- The finite support-face targets partition the actual `SmoothResolution.block`
of the periodic anchored path. The only extension step is the vanishing of the
actual smooth multiplier outside its frequency box. -/
theorem sum_faceBlockTarget_eq_actualBlock {d : ℕ}
    (s : Fin d → ℕ) (f : RealPeriodic d) :
    (∑ J : Finset (Fin d), faceBlockTarget J s
      (fun x => ((f x : ℝ) : ℂ))) = SmoothResolution.block s f := by
  classical
  let faces : Finset (Finset (Fin d)) :=
    (Finset.univ : Finset (Fin d)).powerset
  have hfaces : (Finset.univ : Finset (Finset (Fin d))) = faces := by
    ext J
    simp [faces]
  have hsum := BrownianSharp.AlignmentPaperMultivariateFaceInverse.sum_faceBlockTarget_eq_torusFourierPolynomial
    s (fun x => ((f x : ℝ) : ℂ))
  have hczero : ∀ k ∈ faceBlockFrequencyBox s,
      k ∉ SmoothResolution.frequencyBox s → faceBlockSymbol s k = 0 := by
    intro k hkbox hk
    have hreal :=
      BrownianSharp.AlignmentPeriodicFourierReconstruction.tensorMultiplier_eq_zero_outside_box
        s k hk
    simpa [faceBlockSymbol, SmoothResolution.tensorMultiplier, Complex.ofReal_prod] using
      congrArg (fun r : ℝ => (r : ℂ)) hreal
  have hpoly := torusFourierPolynomial_extend_support
    (SmoothResolution.frequencyBox s) (faceBlockFrequencyBox s)
    (fun k => faceBlockSymbol s k *
      UnitAddTorus.mFourierCoeff (fun x => ((f x : ℝ) : ℂ)) k)
    (smoothFrequencyBox_subset_faceBox s) (by
      intro k hkbox hk
      rw [hczero k hkbox hk]
      simp)
  calc
    _ = ∑ J ∈ faces, faceBlockTarget J s
        (fun x => ((f x : ℝ) : ℂ)) := by rw [hfaces]
    _ = torusFourierPolynomial (faceBlockFrequencyBox s)
        (fun k => faceBlockSymbol s k *
          UnitAddTorus.mFourierCoeff (fun x => ((f x : ℝ) : ℂ)) k) := by
          simpa [faces] using hsum
    _ = torusFourierPolynomial (SmoothResolution.frequencyBox s)
        (fun k => faceBlockSymbol s k *
          UnitAddTorus.mFourierCoeff (fun x => ((f x : ℝ) : ℂ)) k) := hpoly.symm
    _ = SmoothResolution.block s f := by
          unfold SmoothResolution.block
          have hcoeff (k : Fin d → ℤ) :
              faceBlockSymbol s k * UnitAddTorus.mFourierCoeff
                  (fun x => ((f x : ℝ) : ℂ)) k =
                (SmoothResolution.tensorMultiplier s k : ℂ) *
                  BrownianSharp.Torus.realPeriodicFourierCoeff f k := by
            have hm : faceBlockSymbol s k =
                (SmoothResolution.tensorMultiplier s k : ℂ) := by
              simp [faceBlockSymbol, SmoothResolution.tensorMultiplier,
                Complex.ofReal_prod]
            have hf : UnitAddTorus.mFourierCoeff
                (fun x => ((f x : ℝ) : ℂ)) k =
                BrownianSharp.Torus.realPeriodicFourierCoeff f k := rfl
            rw [hm, hf]
          have hcoeffFun :
              (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff
                (fun x => ((f x : ℝ) : ℂ)) k) =
              (fun k => (SmoothResolution.tensorMultiplier s k : ℂ) *
                BrownianSharp.Torus.realPeriodicFourierCoeff f k) := funext hcoeff
          calc
            _ = torusFourierPolynomial (SmoothResolution.frequencyBox s)
                  (fun k => (SmoothResolution.tensorMultiplier s k : ℂ) *
                    BrownianSharp.Torus.realPeriodicFourierCoeff f k) := by rw [hcoeffFun]

/-- Conditional actual grade consumer. The face functions are the finite Fourier
blocks `faceBlockTarget`; `hdecomp` is their exact finite partition of the actual
smooth-resolution block, and `hface` is the per-face inverse-kernel plus signed
square-function estimate. This consumer performs only the finite shape/face
aggregation and uses the proved arbitrary-Lp source budget. -/
theorem actualGradeLpEnergy_le_of_face_contract {d n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (hg : ‖g‖ ≤ 1)
    (Cface : ℝ) (hCface : 0 ≤ Cface)
    (hface : ∀ J : Finset (Fin d),
      gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
        (fun s : Shape d n => faceBlockTarget J s.1
          (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))) ≤
        Cface * (2:ℝ)^(-(n:ℝ)) * sourceLpNorm p J g) :
    gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
      (fun s : Shape d n => block s.1 (periodicFoldExtension (integrationPath p hp g))) ≤
      Cface * 4^d * (2:ℝ)^(-(n:ℝ)) := by
  let S := (Finset.univ : Finset (Fin d)).powerset
  have hmem : ∀ J : Finset (Fin d), ∀ s : Shape d n,
      MemLp (fun x : UnitAddTorus (Fin d) =>
        faceBlockTarget J s.1
          (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) x)
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
    intro J s
    have hcont := (faceBlockTarget J s.1
      (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))).continuous
    have hc : IsCompact ((fun x : UnitAddTorus (Fin d) =>
        ‖faceBlockTarget J s.1
          (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) x‖) '' Set.univ) :=
      isCompact_univ.image hcont.norm
    rcases hc.bddAbove with ⟨M, hM⟩
    apply MemLp.of_bound hcont.aestronglyMeasurable M
    filter_upwards with x
    exact hM ⟨x, Set.mem_univ x, rfl⟩
  have htriangle := finite_face_mixed_lp_triangle
    (X := UnitAddTorus (Fin d)) (J := Finset (Fin d)) (S := Shape d n)
    (μ := volume) (lt_trans zero_lt_one hp) (by linarith)
    (fun (J : Finset (Fin d)) (s : Shape d n) x =>
      faceBlockTarget J s.1
        (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) x)
    (fun (J : Finset (Fin d)) (s : Shape d n) => hmem J s)
  have hdecomp' : ∀ s : Shape d n, ∀ x : UnitAddTorus (Fin d),
      block s.1 (periodicFoldExtension (integrationPath p hp g)) x =
        ∑ J : Finset (Fin d),
          faceBlockTarget J s.1
            (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) x := by
    intro s x
    have heq := sum_faceBlockTarget_eq_actualBlock s.1
      (periodicFoldExtension (integrationPath p hp g))
    simpa only [ContinuousMap.coe_sum, Finset.sum_apply] using
      (congrArg (fun h : C(UnitAddTorus (Fin d), ℂ) => h x) heq).symm
  have htriangle' :
      gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
        (fun s : Shape d n => block s.1 (periodicFoldExtension (integrationPath p hp g))) ≤
        ∑ J : Finset (Fin d),
          gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
            (fun s : Shape d n => faceBlockTarget J s.1
              (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))) := by
    unfold gradeLpEnergy
    simp_rw [hdecomp']
    exact htriangle
  calc
    _ ≤ ∑ J : Finset (Fin d),
          gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
            (fun s : Shape d n => faceBlockTarget J s.1
              (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))) := htriangle'
    _ ≤ ∑ J : Finset (Fin d),
          Cface * (2:ℝ)^(-(n:ℝ)) * sourceLpNorm p J g := by
            apply Finset.sum_le_sum
            intro J _
            exact hface J
    _ = Cface * (2:ℝ)^(-(n:ℝ)) *
          ∑ J : Finset (Fin d), sourceLpNorm p J g := by
            simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ Cface * (2:ℝ)^(-(n:ℝ)) * (4^d * ‖g‖) := by
          have hfaces : (Finset.univ : Finset (Finset (Fin d))) =
              (Finset.univ : Finset (Fin d)).powerset := by
            ext J
            simp
          have hsourceAll :
              (∑ J : Finset (Fin d), sourceLpNorm p J g) ≤ 4^d * ‖g‖ := by
            change (∑ J ∈ (Finset.univ : Finset (Finset (Fin d))),
              sourceLpNorm p J g) ≤ 4^d * ‖g‖
            rw [hfaces]
            exact sum_sourceLpNorm_le hp g
          exact mul_le_mul_of_nonneg_left hsourceAll (by positivity)
    _ ≤ Cface * 4^d * (2:ℝ)^(-(n:ℝ)) := by
          have hcoeff : 0 ≤ Cface * (4:ℝ)^d * (2:ℝ)^(-(n:ℝ)) := by positivity
          calc
            Cface * (2:ℝ)^(-(n:ℝ)) * ((4:ℝ)^d * ‖g‖) =
                (Cface * (4:ℝ)^d * (2:ℝ)^(-(n:ℝ))) * ‖g‖ := by ring
            _ ≤ Cface * (4:ℝ)^d * (2:ℝ)^(-(n:ℝ)) := by
                simpa using mul_le_mul_of_nonneg_left hg hcoeff
            _ = Cface * 4^d * (2:ℝ)^(-(n:ℝ)) := by ring

/-- The sampling budget uses the pth power of the mixed grade norm. This
converts the actual finite-face aggregation estimate to that exact quantity. -/
theorem actualGradeLpCost_le_of_face_contract {d n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (hg : ‖g‖ ≤ 1)
    (Cface : ℝ) (hCface : 0 ≤ Cface)
    (hface : ∀ J : Finset (Fin d),
      gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
        (fun s : Shape d n => faceBlockTarget J s.1
          (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))) ≤
        Cface * (2:ℝ)^(-(n:ℝ)) * sourceLpNorm p J g) :
    (∑ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d),
        ‖block s.1 (periodicFoldExtension (integrationPath p hp g)) x‖ ^ p
        ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2 / p)) ^ (p / 2) ≤
      (Cface * 4^d)^p * (2:ℝ)^(-(p * n)) := by
  have hE := actualGradeLpEnergy_le_of_face_contract hp hp2 g hg Cface hCface hface
  have hsum_nonneg : 0 ≤ ∑ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d),
        ‖block s.1 (periodicFoldExtension (integrationPath p hp g)) x‖ ^ p
        ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2 / p) := by
    apply Finset.sum_nonneg
    intro s hs
    apply Real.rpow_nonneg
    exact integral_nonneg fun x => by positivity
  have hconvert :
      (∑ s : Shape d n,
        (∫ x : UnitAddTorus (Fin d),
          ‖block s.1 (periodicFoldExtension (integrationPath p hp g)) x‖ ^ p
          ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2 / p)) ^ (p / 2) =
        gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
          (fun s : Shape d n => block s.1
            (periodicFoldExtension (integrationPath p hp g))) ^ p := by
    unfold gradeLpEnergy
    rw [← Real.rpow_mul hsum_nonneg (1 / 2 : ℝ) p]
    congr 1
    ring
  have hE_nonneg : 0 ≤ gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
      (fun s : Shape d n => block s.1
        (periodicFoldExtension (integrationPath p hp g))) := by
    unfold gradeLpEnergy
    apply Real.rpow_nonneg
    apply Finset.sum_nonneg
    intro s hs
    apply Real.rpow_nonneg
    exact integral_nonneg fun x => by positivity
  have hD_nonneg : 0 ≤ Cface * 4^d * (2:ℝ)^(-(n:ℝ)) := by positivity
  have hpower := Real.rpow_le_rpow hE_nonneg hE (le_of_lt (lt_trans zero_lt_one hp))
  have hscale : (Cface * 4^d * (2:ℝ)^(-(n:ℝ))) ^ p =
      (Cface * 4^d)^p * (2:ℝ)^(-(p * n)) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(n:ℝ)) p]
    congr 1
    ring
  calc
    _ = gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
          (fun s : Shape d n => block s.1
            (periodicFoldExtension (integrationPath p hp g))) ^ p := hconvert
    _ ≤ (Cface * 4^d * (2:ℝ)^(-(n:ℝ))) ^ p := hpower
    _ = (Cface * 4^d)^p * (2:ℝ)^(-(p * n)) := hscale

end BrownianSharp.AlignmentPaperAnchoredLpGradeBudget
