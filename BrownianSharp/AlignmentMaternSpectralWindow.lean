import BrownianSharp.AlignmentMaternSpectralFeature
import BrownianSharp.AlignmentMaternScalarFeature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
Finite spectral-window calculations for the one-dimensional Matérn feature.
The feature phase convention is `(cos (2π ξ t), sin (2π ξ t))`, so windows
are centered at integer frequencies.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentMaternSpectralWindow

def window (k : ℤ) (a : ℝ) : Set ℝ := Set.Icc ((k : ℝ) - a / 2) ((k : ℝ) + a / 2)

theorem window_disjoint_of_integer_centers (k l : ℤ) (a : ℝ)
    (ha : a < 1) (hne : k ≠ l) : Disjoint (window k a) (window l a) := by
  rw [Set.disjoint_left]
  intro ξ hk hl
  have hsepZ : 1 ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hne)
  have hsep : 1 ≤ |(k : ℝ) - (l : ℝ)| := by
    exact_mod_cast hsepZ
  have hdist : |(k : ℝ) - (l : ℝ)| ≤ a := by
    have hkabs : |ξ - (k : ℝ)| ≤ a / 2 := by
      rw [abs_le]
      constructor <;> linarith [hk.1, hk.2]
    have hlabs : |ξ - (l : ℝ)| ≤ a / 2 := by
      rw [abs_le]
      constructor <;> linarith [hl.1, hl.2]
    calc
      |(k : ℝ) - (l : ℝ)| = |((k : ℝ) - ξ) + (ξ - (l : ℝ))| := by congr 1; ring
      _ ≤ |(k : ℝ) - ξ| + |ξ - (l : ℝ)| := abs_add_le _ _
      _ = |ξ - (k : ℝ)| + |ξ - (l : ℝ)| := by rw [abs_sub_comm]
      _ ≤ a := by linarith [hkabs, hlabs]
  linarith

def windowMultiplier (a t : ℝ) : ℝ :=
  if t = 0 then a else Real.sin (Real.pi * a * t) / (Real.pi * t)

noncomputable def sourceField (κ h : ℝ) (k : ℤ) (aWidth c s : ℝ) (ξ : ℝ) :
    EuclideanSpace ℝ (Fin 2) := by
  classical
  exact if ξ ∈ window k aWidth then
    WithLp.toLp 2 (![c / AlignmentMaternSpectralFeature.density κ h ξ,
      s / AlignmentMaternSpectralFeature.density κ h ξ])
  else 0

theorem sourceField_measurable (κ h : ℝ) (k : ℤ) (aWidth c s : ℝ)
    (hκ : 0 < κ) : Measurable (sourceField κ h k aWidth c s) := by
  unfold sourceField
  have hd : Continuous (AlignmentMaternSpectralFeature.density κ h) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    unfold AlignmentMaternSpectralFeature.density
    have hb : ContinuousAt (fun x : ℝ => κ ^ 2 + x ^ 2) ξ := by fun_prop
    exact hb.rpow_const (Or.inl (ne_of_gt (by positivity)))
  have hc : Continuous (fun ξ : ℝ => c / AlignmentMaternSpectralFeature.density κ h ξ) :=
    continuous_const.div₀ hd (fun ξ => (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).ne')
  have hs : Continuous (fun ξ : ℝ => s / AlignmentMaternSpectralFeature.density κ h ξ) :=
    continuous_const.div₀ hd (fun ξ => (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).ne')
  classical
  have hv : Continuous (fun ξ : ℝ => WithLp.toLp 2
      (![c / AlignmentMaternSpectralFeature.density κ h ξ,
        s / AlignmentMaternSpectralFeature.density κ h ξ] : Fin 2 → ℝ)) := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => by
      fin_cases i <;> simp [hc, hs])
  exact Measurable.ite measurableSet_Icc hv.measurable measurable_const

theorem sourceField_memLp_of_bound (κ h : ℝ) (k : ℤ) (aWidth c s M : ℝ)
    (hκ : 0 < κ) (hh : 0 < h)
    (hbound : ∀ ξ, ‖sourceField κ h k aWidth c s ξ‖ ≤ M) :
    MemLp (sourceField κ h k aWidth c s) 2
      (AlignmentMaternSpectralFeature.spectralMeasure κ h) := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound
    (sourceField_measurable κ h k aWidth c s hκ).aestronglyMeasurable M
  filter_upwards with ξ
  exact hbound ξ

def sourceL2 (κ h : ℝ) (k : ℤ) (aWidth c s : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (M : ℝ)
    (hbound : ∀ ξ, ‖sourceField κ h k aWidth c s ξ‖ ≤ M) :
    Lp (EuclideanSpace ℝ (Fin 2)) 2
      (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  (sourceField_memLp_of_bound κ h k aWidth c s M hκ hh hbound).toLp
    (sourceField κ h k aWidth c s)

noncomputable def phaseSourcePairing (κ h t : ℝ) (k : ℤ)
    (aWidth c s ξ : ℝ) : ℝ := by
  classical
  exact if ξ ∈ window k aWidth then
    Real.cos (2 * Real.pi * ξ * t) *
        (c / AlignmentMaternSpectralFeature.density κ h ξ) +
      Real.sin (2 * Real.pi * ξ * t) *
        (s / AlignmentMaternSpectralFeature.density κ h ξ)
  else 0

theorem phase_inner_sourceField (κ h t : ℝ) (k : ℤ) (aWidth c s ξ : ℝ)
    (hκ : 0 < κ) :
    inner ℝ (AlignmentMaternSpectralFeature.phase t ξ)
      (sourceField κ h k aWidth c s ξ) =
      phaseSourcePairing κ h t k aWidth c s ξ := by
  classical
  by_cases hx : ξ ∈ window k aWidth
  · simp [phaseSourcePairing, sourceField, hx, AlignmentMaternSpectralFeature.phase,
      EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  · simp [phaseSourcePairing, sourceField, hx, AlignmentMaternSpectralFeature.phase]

/-- Scalar spectral preimage of one real cosine-sine Fourier mode.  The two
windows are centered at `k` and `-k`; their coefficients are chosen so that
the scalar phase `cos + sin` recovers both real Fourier coefficients. -/
noncomputable def scalarWindowSourceField (κ h : ℝ) (k : ℤ)
    (aWidth c s : ℝ) (ξ : ℝ) : ℝ := by
  classical
  exact (if ξ ∈ window k aWidth then
      (c + s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ) else 0) +
    (if ξ ∈ window (-k) aWidth then
      (c - s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ) else 0)

noncomputable def scalarWindowWeightedOutput (t : ℝ) (k : ℤ)
    (aWidth c s : ℝ) (ξ : ℝ) : ℝ := by
  classical
  exact (if ξ ∈ window k aWidth then
      ((c + s) / 2) * AlignmentMaternScalarFeature.scalarPhase t ξ else 0) +
    (if ξ ∈ window (-k) aWidth then
      ((c - s) / 2) * AlignmentMaternScalarFeature.scalarPhase t ξ else 0)

theorem scalarWindowSourceField_measurable (κ h : ℝ) (k : ℤ)
    (aWidth c s : ℝ) (hκ : 0 < κ) :
    Measurable (scalarWindowSourceField κ h k aWidth c s) := by
  have hd : Continuous (AlignmentMaternSpectralFeature.density κ h) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    unfold AlignmentMaternSpectralFeature.density
    have hb : ContinuousAt (fun x : ℝ => κ ^ 2 + x ^ 2) ξ := by fun_prop
    exact hb.rpow_const (Or.inl (ne_of_gt (by positivity)))
  have hc : Continuous (fun ξ : ℝ => (c + s) /
      (2 * AlignmentMaternSpectralFeature.density κ h ξ)) := by
    apply continuous_const.div₀
    · exact continuous_const.mul hd
    · intro ξ
      exact mul_ne_zero (by norm_num) (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).ne'
  have hs : Continuous (fun ξ : ℝ => (c - s) /
      (2 * AlignmentMaternSpectralFeature.density κ h ξ)) := by
    apply continuous_const.div₀
    · exact continuous_const.mul hd
    · intro ξ
      exact mul_ne_zero (by norm_num) (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ).ne'
  classical
  unfold scalarWindowSourceField
  exact (Measurable.ite measurableSet_Icc hc.measurable measurable_const).add
    (Measurable.ite measurableSet_Icc hs.measurable measurable_const)

theorem scalarWindowSourceField_memLp_of_bound (κ h : ℝ) (k : ℤ)
    (aWidth c s M : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k aWidth c s ξ| ≤ M) :
    MemLp (scalarWindowSourceField κ h k aWidth c s) 2
      (AlignmentMaternSpectralFeature.spectralMeasure κ h) := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound
    (scalarWindowSourceField_measurable κ h k aWidth c s hκ).aestronglyMeasurable M
  filter_upwards with ξ
  exact hbound ξ

def scalarWindowSourceL2 (κ h : ℝ) (k : ℤ) (aWidth c s M : ℝ)
    (hκ : 0 < κ) (hh : 0 < h)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k aWidth c s ξ| ≤ M) :
    Lp ℝ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  (scalarWindowSourceField_memLp_of_bound κ h k aWidth c s M hκ hh hbound).toLp
    (scalarWindowSourceField κ h k aWidth c s)

theorem abs_frequency_le_window (k : ℤ) (a ξ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hξ : ξ ∈ window k a) :
    |ξ| ≤ |(k : ℝ)| + 1 := by
  have hd : |ξ - (k : ℝ)| ≤ a / 2 := by
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  calc
    |ξ| = |(ξ - (k : ℝ)) + (k : ℝ)| := by congr 1; ring
    _ ≤ |ξ - (k : ℝ)| + |(k : ℝ)| := abs_add_le _ _
    _ ≤ a / 2 + |(k : ℝ)| := by linarith [hd]
    _ ≤ |(k : ℝ)| + 1 := by linarith

theorem density_inv_le_window_bound (κ h : ℝ) (k : ℤ) (a ξ : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hξ : ξ ∈ window k a) :
    (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ ≤
      Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
  let s := h + 1 / 2
  let K := κ ^ 2 + (|(k : ℝ)| + 1) ^ 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  have hfreq := abs_frequency_le_window k a ξ ha0 ha1 hξ
  have hsq : |ξ| ^ 2 ≤ (|(k : ℝ)| + 1) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg ξ) (by positivity)).2 hfreq
  have hbasele : κ ^ 2 + ξ ^ 2 ≤ K := by
    dsimp [K]
    simpa [sq_abs] using add_le_add_left hsq (κ ^ 2)
  have hinv : (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ =
      Real.rpow (κ ^ 2 + ξ ^ 2) s := by
    rw [AlignmentMaternSpectralFeature.density]
    change ((κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)))⁻¹ = _
    have hr : (κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)) =
        ((κ ^ 2 + ξ ^ 2).rpow (h + 1 / 2))⁻¹ :=
      Real.rpow_neg (by positivity) (h + 1 / 2)
    rw [hr, inv_inv]
  rw [hinv]
  exact Real.rpow_le_rpow (by positivity) hbasele (by linarith)

theorem scalarWindowSourceField_abs_bound (κ h : ℝ) (k : ℤ)
    (aWidth c s : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ aWidth) (ha1 : aWidth ≤ 1) (ξ : ℝ) :
    |scalarWindowSourceField κ h k aWidth c s ξ| ≤
      (|c| + |s|) * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
  classical
  have hρ : 0 < AlignmentMaternSpectralFeature.density κ h ξ :=
    AlignmentMaternSpectralFeature.density_pos κ h ξ hκ
  have hInv (j : ℤ) (hj : ξ ∈ window j aWidth)
      (hjk : |(j : ℝ)| ≤ |(k : ℝ)|) :
      (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ ≤
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
    have hcoord := abs_frequency_le_window j aWidth ξ ha0 ha1 hj
    have hcoord' : |ξ| ≤ |(k : ℝ)| + 1 := hcoord.trans (by linarith)
    have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
    have hsq : |ξ| ^ 2 ≤ (|(k : ℝ)| + 1) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg ξ) (by positivity)).2 hcoord'
    have hbasele : κ ^ 2 + ξ ^ 2 ≤ κ ^ 2 + (|(k : ℝ)| + 1) ^ 2 := by
      simpa [sq_abs] using add_le_add_left hsq (κ ^ 2)
    rw [AlignmentMaternSpectralFeature.density]
    change ((κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)))⁻¹ ≤ _
    have hr : (κ ^ 2 + ξ ^ 2).rpow (-(h + 1 / 2)) =
        ((κ ^ 2 + ξ ^ 2).rpow (h + 1 / 2))⁻¹ :=
      Real.rpow_neg (by positivity) (h + 1 / 2)
    rw [hr, inv_inv]
    exact Real.rpow_le_rpow (by positivity) hbasele (by linarith)
  have hcoef (u : ℝ) (hu : |u| ≤ |c| + |s|)
      (hinv : (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ ≤
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) :
      |u / (2 * AlignmentMaternSpectralFeature.density κ h ξ)| ≤
        ((|c| + |s|) / 2) *
          Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hρ)]
    calc
      |u| / (2 * AlignmentMaternSpectralFeature.density κ h ξ) =
          (|u| / 2) * (AlignmentMaternSpectralFeature.density κ h ξ)⁻¹ := by field_simp
      _ ≤ ((|c| + |s|) / 2) *
          Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
        mul_le_mul (by nlinarith [hu]) hinv (by positivity) (by positivity)
  by_cases h₁ : ξ ∈ window k aWidth
  · by_cases h₂ : ξ ∈ window (-k) aWidth
    · have hu₁ : |c + s| ≤ |c| + |s| := abs_add_le c s
      have hu₂ : |c - s| ≤ |c| + |s| := by
        simpa [sub_eq_add_neg, abs_neg] using (abs_add_le c (-s))
      have h₁b := hcoef (c + s) hu₁ (hInv k h₁ le_rfl)
      have h₂b := hcoef (c - s) hu₂ (hInv (-k) h₂ (by simp))
      calc
        |scalarWindowSourceField κ h k aWidth c s ξ| ≤
            |(c + s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ)| +
              |(c - s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ)| := by
                simpa [scalarWindowSourceField, h₁, h₂] using
                  (abs_add_le ((c + s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ))
                    ((c - s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ)))
        _ ≤ ((|c| + |s|) / 2) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) +
            ((|c| + |s|) / 2) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := add_le_add h₁b h₂b
        _ = (|c| + |s|) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by ring
    · have hu₁ : |c + s| ≤ |c| + |s| := abs_add_le c s
      have hb := hcoef (c + s) hu₁ (hInv k h₁ le_rfl)
      have hpow : 0 ≤ Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
        (Real.rpow_pos_of_pos (by positivity) _).le
      have hA : 0 ≤ |c| + |s| := add_nonneg (abs_nonneg c) (abs_nonneg s)
      calc
        |scalarWindowSourceField κ h k aWidth c s ξ| =
            |(c + s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ)| := by
              simp [scalarWindowSourceField, h₁, h₂]
        _ ≤ ((|c| + |s|) / 2) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := hb
        _ ≤ (|c| + |s|) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
                nlinarith [mul_nonneg hA hpow]
  · by_cases h₂ : ξ ∈ window (-k) aWidth
    · have hu₂ : |c - s| ≤ |c| + |s| := by
        simpa [sub_eq_add_neg, abs_neg] using (abs_add_le c (-s))
      have hb := hcoef (c - s) hu₂ (hInv (-k) h₂ (by simp))
      have hpow : 0 ≤ Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
        (Real.rpow_pos_of_pos (by positivity) _).le
      have hA : 0 ≤ |c| + |s| := add_nonneg (abs_nonneg c) (abs_nonneg s)
      calc
        |scalarWindowSourceField κ h k aWidth c s ξ| =
            |(c - s) / (2 * AlignmentMaternSpectralFeature.density κ h ξ)| := by
              simp [scalarWindowSourceField, h₁, h₂]
        _ ≤ ((|c| + |s|) / 2) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := hb
        _ ≤ (|c| + |s|) *
              Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) := by
                nlinarith [mul_nonneg hA hpow]
    · simp [scalarWindowSourceField, h₁, h₂]
      positivity

/-- Uniform polynomial tail of the Matérn density on a short window.  This
is the measure-side estimate needed to turn the pointwise source envelope
into the sharp Sobolev-frequency L² cost. -/
theorem density_le_frequency_tail_on_window (κ h : ℝ) (k : ℤ) (a ξ : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hξ : ξ ∈ window k a) :
    AlignmentMaternSpectralFeature.density κ h ξ ≤
      Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) := by
  let s := h + 1 / 2
  let m := min 1 (κ ^ 2)
  have hs : 0 < s := by dsimp [s]; linarith
  have hm0 : 0 < m := by
    dsimp [m]
    exact lt_min (by norm_num) (sq_pos_of_pos hκ)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmk : m ≤ κ ^ 2 := min_le_right _ _
  have hd : |ξ - (k : ℝ)| ≤ a / 2 := by
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  have hfreq : |(k : ℝ)| ≤ |ξ| + 1 / 2 := by
    calc
      |(k : ℝ)| = |((k : ℝ) - ξ) + ξ| := by congr 1; ring
      _ ≤ |(k : ℝ) - ξ| + |ξ| := abs_add_le _ _
      _ = |ξ - (k : ℝ)| + |ξ| := by rw [abs_sub_comm]
      _ ≤ a / 2 + |ξ| := by linarith [hd]
      _ ≤ |ξ| + 1 / 2 := by linarith
  have hksq : (k : ℝ) ^ 2 ≤ 2 * ξ ^ 2 + 1 / 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (k : ℝ)) (by positivity)).2 hfreq
    nlinarith [sq_abs ξ, sq_abs (k : ℝ), sq_nonneg (|ξ| - 1 / 2)]
  have hmkxi : m * ξ ^ 2 ≤ ξ ^ 2 := by
    calc
      m * ξ ^ 2 ≤ 1 * ξ ^ 2 := mul_le_mul_of_nonneg_right hm1 (sq_nonneg ξ)
      _ = ξ ^ 2 := by ring
  have hlow : m / 2 * (1 + (k : ℝ) ^ 2) ≤ κ ^ 2 + ξ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hksq hm0.le, hmkxi, hmk]
  have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  have hsmall : 0 < m / 2 * (1 + (k : ℝ) ^ 2) := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hsmall hlow (by linarith : -s ≤ 0)
  have hfactor : Real.rpow (m / 2 * (1 + (k : ℝ) ^ 2)) (-s) =
      Real.rpow (m / 2) (-s) * Real.rpow (1 + (k : ℝ) ^ 2) (-s) :=
    Real.mul_rpow (le_of_lt (by positivity)) (by positivity)
  rw [AlignmentMaternSpectralFeature.density]
  change Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤ _
  calc
    Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤
        Real.rpow (m / 2 * (1 + (k : ℝ) ^ 2)) (-s) := hpow
    _ = Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) := by
          simpa [s, m] using hfactor

theorem spectralMeasure_window_le (κ h : ℝ) (k : ℤ) (a : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a) ≤
      ENNReal.ofReal (a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) := by
  let D := Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
      Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDξ (ξ : ℝ) (hξ : ξ ∈ window k a) :
      ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ) ≤ ENNReal.ofReal D := by
    apply ENNReal.ofReal_le_ofReal
    simpa [D] using density_le_frequency_tail_on_window κ h k a ξ hκ hh ha0 ha1 hξ
  have hs : MeasurableSet (window k a) := measurableSet_Icc
  rw [show AlignmentMaternSpectralFeature.spectralMeasure κ h =
      volume.withDensity (fun ξ => ENNReal.ofReal
        (AlignmentMaternSpectralFeature.density κ h ξ)) by rfl]
  rw [withDensity_apply _ hs]
  calc
    ∫⁻ ξ in window k a, ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ)
        ∂volume = ∫⁻ ξ, (window k a).indicator
          (fun ξ => ENNReal.ofReal (AlignmentMaternSpectralFeature.density κ h ξ)) ξ ∂volume := by
          rw [lintegral_indicator hs]
    _ ≤ ∫⁻ ξ, (window k a).indicator (fun _ : ℝ => ENNReal.ofReal D) ξ ∂volume := by
          apply lintegral_mono
          intro ξ
          by_cases hx : ξ ∈ window k a
          · simpa [hx] using hDξ ξ hx
          · simp [hx]
    _ = ENNReal.ofReal D * volume (window k a) := by
          rw [lintegral_indicator_const hs]
    _ = ENNReal.ofReal (D * a) := by
          rw [window, Real.volume_Icc]
          rw [← ENNReal.ofReal_mul hD]
          congr 1
          ring
    _ = ENNReal.ofReal (a * D) := by rw [mul_comm]
    _ = _ := by rfl

def scalarWindowSupport (k : ℤ) (a : ℝ) : Set ℝ := window k a ∪ window (-k) a

theorem scalarWindowSupport_disjoint_of_positive_ne (n m : ℕ) (a : ℝ)
    (ha : a < 1) (hnm : n ≠ m) :
    Disjoint (scalarWindowSupport (Int.ofNat (n + 1)) a)
      (scalarWindowSupport (Int.ofNat (m + 1)) a) := by
  rw [Set.disjoint_left]
  intro ξ hx hy
  have hpos : 0 < Int.ofNat (n + 1) := by
    simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ n))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hkl : Int.ofNat (n + 1) ≠ Int.ofNat (m + 1) := by
      intro heq
      apply hnm
      have hnat : n + 1 = m + 1 := Int.ofNat_inj.mp heq
      omega
    exact (Set.disjoint_left.mp
      (window_disjoint_of_integer_centers (Int.ofNat (n + 1))
        (Int.ofNat (m + 1)) a ha hkl)) hx hy
  · have hkl : Int.ofNat (n + 1) ≠ -Int.ofNat (m + 1) := by
      intro heq
      have hp : 0 < Int.ofNat (n + 1) := by
        simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ n))
      have hn : 0 < Int.ofNat (m + 1) := by
        simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ m))
      omega
    exact (Set.disjoint_left.mp
      (window_disjoint_of_integer_centers (Int.ofNat (n + 1))
        (-Int.ofNat (m + 1)) a ha hkl)) hx hy
  · have hkl : -Int.ofNat (n + 1) ≠ Int.ofNat (m + 1) := by
      intro heq
      have hp : 0 < Int.ofNat (n + 1) := by
        simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ n))
      have hn : 0 < Int.ofNat (m + 1) := by
        simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ m))
      omega
    exact (Set.disjoint_left.mp
      (window_disjoint_of_integer_centers (-Int.ofNat (n + 1))
        (Int.ofNat (m + 1)) a ha hkl)) hx hy
  · have hkl : -Int.ofNat (n + 1) ≠ -Int.ofNat (m + 1) := by
      intro heq
      apply hnm
      have hnat : n + 1 = m + 1 := Int.ofNat_inj.mp (Int.neg_inj.mp heq)
      omega
    exact (Set.disjoint_left.mp
      (window_disjoint_of_integer_centers (-Int.ofNat (n + 1))
        (-Int.ofNat (m + 1)) a ha hkl)) hx hy

theorem scalarWindowSupport_zero_disjoint_of_positive (n : ℕ) (a : ℝ)
    (ha : a < 1) :
    Disjoint (scalarWindowSupport 0 a) (scalarWindowSupport (Int.ofNat (n + 1)) a) := by
  have hpos : 0 < Int.ofNat (n + 1) := by
    simpa using (Int.natCast_pos.mpr (Nat.zero_lt_succ n))
  have hneg : -Int.ofNat (n + 1) < 0 := neg_neg_of_pos hpos
  rw [Set.disjoint_left]
  intro ξ hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.mp (window_disjoint_of_integer_centers 0
      (Int.ofNat (n + 1)) a ha (Ne.symm (ne_of_gt hpos))) hx hy
  · exact Set.disjoint_left.mp (window_disjoint_of_integer_centers 0
      (-Int.ofNat (n + 1)) a ha (Ne.symm (ne_of_lt hneg))) hx hy
  · simpa using Set.disjoint_left.mp (window_disjoint_of_integer_centers 0
      (Int.ofNat (n + 1)) a ha (Ne.symm (ne_of_gt hpos))) hx hy
  · simpa using Set.disjoint_left.mp (window_disjoint_of_integer_centers 0
      (-Int.ofNat (n + 1)) a ha (Ne.symm (ne_of_lt hneg))) hx hy

theorem scalarWindowSource_zero_of_not_mem_support (κ h : ℝ) (k : ℤ)
    (a c s ξ : ℝ) (hξ : ξ ∉ scalarWindowSupport k a) :
    scalarWindowSourceField κ h k a c s ξ = 0 := by
  simp only [scalarWindowSupport, Set.mem_union, not_or] at hξ
  simp [scalarWindowSourceField, hξ.1, hξ.2]

theorem scalarWindowSourceL2_inner_zero_of_disjoint (κ h : ℝ) (k l : ℤ)
    (a c₁ s₁ c₂ s₂ M₁ M₂ : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hbound₁ : ∀ ξ, |scalarWindowSourceField κ h k a c₁ s₁ ξ| ≤ M₁)
    (hbound₂ : ∀ ξ, |scalarWindowSourceField κ h l a c₂ s₂ ξ| ≤ M₂)
    (hdis : Disjoint (scalarWindowSupport k a) (scalarWindowSupport l a)) :
    inner ℝ (scalarWindowSourceL2 κ h k a c₁ s₁ M₁ hκ hh hbound₁)
      (scalarWindowSourceL2 κ h l a c₂ s₂ M₂ hκ hh hbound₂) = 0 := by
  let μ := AlignmentMaternSpectralFeature.spectralMeasure κ h
  letI : IsFiniteMeasure μ := AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  have hmem₁ := scalarWindowSourceField_memLp_of_bound κ h k a c₁ s₁ M₁ hκ hh hbound₁
  have hmem₂ := scalarWindowSourceField_memLp_of_bound κ h l a c₂ s₂ M₂ hκ hh hbound₂
  have hcoe₁ := hmem₁.coeFn_toLp
  have hcoe₂ := hmem₂.coeFn_toLp
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hcoe₁, hcoe₂] with ξ hξ₁ hξ₂
  change scalarWindowSourceL2 κ h k a c₁ s₁ M₁ hκ hh hbound₁ ξ =
      scalarWindowSourceField κ h k a c₁ s₁ ξ at hξ₁
  change scalarWindowSourceL2 κ h l a c₂ s₂ M₂ hκ hh hbound₂ ξ =
      scalarWindowSourceField κ h l a c₂ s₂ ξ at hξ₂
  rw [hξ₁, hξ₂, Real.inner_apply]
  by_cases hξ : ξ ∈ scalarWindowSupport k a
  · have hξ' : ξ ∉ scalarWindowSupport l a := by
      intro hmem
      exact (Set.disjoint_left.mp hdis) hξ hmem
    rw [scalarWindowSource_zero_of_not_mem_support κ h l a c₂ s₂ ξ hξ']
    simp
  · rw [scalarWindowSource_zero_of_not_mem_support κ h k a c₁ s₁ ξ hξ]
    simp

theorem spectralMeasure_scalarWindowSupport_le (κ h : ℝ) (k : ℤ) (a : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    AlignmentMaternSpectralFeature.spectralMeasure κ h (scalarWindowSupport k a) ≤
      ENNReal.ofReal (2 * a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) := by
  unfold scalarWindowSupport
  calc
    AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a ∪ window (-k) a) ≤
        AlignmentMaternSpectralFeature.spectralMeasure κ h (window k a) +
          AlignmentMaternSpectralFeature.spectralMeasure κ h (window (-k) a) :=
      by exact measure_union_le (window k a) (window (-k) a)
    _ ≤ ENNReal.ofReal (a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) +
        ENNReal.ofReal (a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + ((-k : ℤ) : ℝ) ^ 2) (-(h + 1 / 2)))) :=
      add_le_add (spectralMeasure_window_le κ h k a hκ hh ha0 ha1)
        (spectralMeasure_window_le κ h (-k) a hκ hh ha0 ha1)
    _ = ENNReal.ofReal (2 * a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) := by
      rw [show ((-k : ℤ) : ℝ) ^ 2 = (k : ℝ) ^ 2 by simp]
      have hterm : 0 ≤ a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) := by
        apply mul_nonneg ha0
        exact mul_nonneg
          (Real.rpow_pos_of_pos (by positivity : 0 < min 1 (κ ^ 2) / 2) _).le
          (Real.rpow_pos_of_pos (by positivity : 0 < 1 + (k : ℝ) ^ 2) _).le
      rw [← ENNReal.ofReal_add hterm hterm]
      congr 1
      ring

theorem scalarWindowSource_eLpNorm_le (κ h : ℝ) (k : ℤ)
    (a c s M : ℝ) (hκ : 0 < κ) (hh : 0 < h) (hM : 0 ≤ M)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k a c s ξ| ≤ M) :
    eLpNorm (scalarWindowSourceField κ h k a c s) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      ENNReal.ofReal M *
        (AlignmentMaternSpectralFeature.spectralMeasure κ h (scalarWindowSupport k a)) ^ (1 / 2 : ℝ) := by
  have hset : MeasurableSet (scalarWindowSupport k a) := by
    unfold scalarWindowSupport
    exact measurableSet_Icc.union measurableSet_Icc
  have hdom (ξ : ℝ) :
      ‖scalarWindowSourceField κ h k a c s ξ‖ₑ ≤
        ‖(scalarWindowSupport k a).indicator (fun _ : ℝ => M) ξ‖ₑ := by
    by_cases hξ : ξ ∈ scalarWindowSupport k a
    · simp only [Set.indicator_of_mem hξ]
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_trans (hbound ξ) (le_abs_self M))
    · rw [scalarWindowSource_zero_of_not_mem_support κ h k a c s ξ hξ]
      simp [Set.indicator_apply, hξ]
  calc
    eLpNorm (scalarWindowSourceField κ h k a c s) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      eLpNorm ((scalarWindowSupport k a).indicator (fun _ : ℝ => M)) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
      eLpNorm_mono_enorm
        (scalarWindowSourceField_measurable κ h k a c s hκ).aestronglyMeasurable hdom
    _ = ENNReal.ofReal M *
        (AlignmentMaternSpectralFeature.spectralMeasure κ h (scalarWindowSupport k a)) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_indicator_const hset.nullMeasurableSet (by norm_num) (by norm_num)]
      rw [show (2 : ENNReal).toReal = 2 by norm_num]
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hM]

theorem scalarWindowSource_eLpNorm_frequency_bound (κ h : ℝ) (k : ℤ)
    (a c s : ℝ) (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    eLpNorm (scalarWindowSourceField κ h k a c s) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      ENNReal.ofReal ((|c| + |s|) *
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) *
      (ENNReal.ofReal (2 * a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) : ENNReal) ^ (1 / 2 : ℝ) := by
  let M := (|c| + |s|) *
    Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)
  let V := 2 * a *
    (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
      Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbound (ξ : ℝ) : |scalarWindowSourceField κ h k a c s ξ| ≤ M := by
    exact scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ
  have hmass := spectralMeasure_scalarWindowSupport_le κ h k a hκ hh ha0 ha1
  calc
    eLpNorm (scalarWindowSourceField κ h k a c s) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h) ≤
      ENNReal.ofReal M *
        (AlignmentMaternSpectralFeature.spectralMeasure κ h (scalarWindowSupport k a)) ^ (1 / 2 : ℝ) :=
      scalarWindowSource_eLpNorm_le κ h k a c s M hκ hh hM hbound
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal V) ^ (1 / 2 : ℝ) := by
      gcongr
    _ = ENNReal.ofReal ((|c| + |s|) *
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) *
      (ENNReal.ofReal (2 * a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) : ENNReal) ^ (1 / 2 : ℝ) := by
        simp [M, V]

theorem scalarWindowSourceL2_norm_frequency_bound (κ h : ℝ) (k : ℤ)
    (a c s : ℝ) (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖scalarWindowSourceL2 κ h k a c s
        ((|c| + |s|) * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2))
        hκ hh (fun ξ => scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ)‖ ≤
      ((|c| + |s|) * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)) *
        Real.rpow (2 * a *
          (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) : ℝ) (1 / 2 : ℝ) := by
  let M := (|c| + |s|) *
    Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)
  let V := 2 * a *
    (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
      Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbound (ξ : ℝ) : |scalarWindowSourceField κ h k a c s ξ| ≤ M := by
    exact scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ
  have hmem := scalarWindowSourceField_memLp_of_bound κ h k a c s M hκ hh hbound
  have hnorm : ‖scalarWindowSourceL2 κ h k a c s M hκ hh hbound‖ =
      ENNReal.toReal (eLpNorm (scalarWindowSourceField κ h k a c s) 2
        (AlignmentMaternSpectralFeature.spectralMeasure κ h)) := by
    rw [scalarWindowSourceL2, Lp.norm_toLp _ hmem]
  have hboundEnn := scalarWindowSource_eLpNorm_frequency_bound κ h k a c s hκ hh ha0 ha1
  have hfinite : (ENNReal.ofReal M * (ENNReal.ofReal V) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hfinite hboundEnn
  rw [← hnorm] at hreal
  have hconvert : ENNReal.toReal
      (ENNReal.ofReal M * (ENNReal.ofReal V) ^ (1 / 2 : ℝ)) = M * Real.rpow V (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hV]
    rfl
  rw [hconvert] at hreal
  simpa [M, V] using hreal

/-- A scalar Fourier mode has an actual Matérn spectral preimage whose L²
cost is bounded by its Sobolev-frequency weight.  The coefficient norm is
the Euclidean norm of the cosine/sine pair. -/
theorem scalarWindowSourceL2_norm_sobolev_bound (κ h : ℝ) (k : ℤ)
    (a c s : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖scalarWindowSourceL2 κ h k a c s
        ((|c| + |s|) * Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2))
        hκ hh (fun ξ => scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ)‖ ≤
      2 * Real.sqrt (c ^ 2 + s ^ 2) *
        Real.rpow (κ ^ 2 + 2) (h + 1 / 2) *
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) *
            Real.rpow (2 * a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
              Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) (1 / 2 : ℝ) := by
  have hbase : 0 < 1 + (k : ℝ) ^ 2 := by positivity
  have hcompbase : κ ^ 2 + (|(k : ℝ)| + 1) ^ 2 ≤
      (κ ^ 2 + 2) * (1 + (k : ℝ) ^ 2) := by
    have hk : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(k : ℝ)| - 1)]
  have hs : 0 < h + 1 / 2 := by linarith
  have hfrequency := scalarWindowSourceL2_norm_frequency_bound κ h k a c s
    hκ hh ha0 ha1
  have hcoeff : |c| + |s| ≤ 2 * Real.sqrt (c ^ 2 + s ^ 2) := by
    have hc : |c| ≤ Real.sqrt (c ^ 2 + s ^ 2) := by
      apply (Real.le_sqrt (abs_nonneg c) (by positivity)).2
      nlinarith [sq_abs c, sq_nonneg s]
    have hss : |s| ≤ Real.sqrt (c ^ 2 + s ^ 2) := by
      apply (Real.le_sqrt (abs_nonneg s) (by positivity)).2
      nlinarith [sq_abs s, sq_nonneg c]
    linarith
  have hpowcomp :
      Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) ≤
        Real.rpow (κ ^ 2 + 2) (h + 1 / 2) *
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2) := by
    calc
      _ ≤ Real.rpow ((κ ^ 2 + 2) * (1 + (k : ℝ) ^ 2)) (h + 1 / 2) :=
        Real.rpow_le_rpow (by positivity) hcompbase hs.le
      _ = _ := Real.mul_rpow (by positivity) hbase.le
  have hsqrtprod :
      Real.sqrt (2 * a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) =
        Real.sqrt (2 * a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2))) *
          Real.sqrt (Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) := by
    have hmin : 0 < min 1 (κ ^ 2) / 2 := by positivity
    have hrad : 0 ≤ 2 * a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) :=
      mul_nonneg (mul_nonneg (by norm_num) ha0) (Real.rpow_nonneg hmin.le _)
    rw [show 2 * a *
        (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) =
        (2 * a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2))) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)) by ring,
      Real.sqrt_mul hrad]
  calc
    _ ≤ (|c| + |s|) *
        Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) *
        Real.rpow (2 * a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) (1 / 2 : ℝ) := by
          simpa only [Real.sqrt_eq_rpow] using hfrequency
    _ ≤ (2 * Real.sqrt (c ^ 2 + s ^ 2)) *
        (Real.rpow (κ ^ 2 + 2) (h + 1 / 2) *
          Real.rpow (1 + (k : ℝ) ^ 2) (h + 1 / 2)) *
        (Real.rpow (2 * a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
          Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) (1 / 2 : ℝ)) := by
        have hcoefnonneg : 0 ≤ |c| + |s| := by positivity
        have hbasepow : 0 ≤ Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2) :=
          Real.rpow_nonneg (by positivity) _
        have hmin : 0 < min 1 (κ ^ 2) / 2 := by positivity
        have hrad : 0 ≤ 2 * a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
            Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2))) :=
          mul_nonneg (mul_nonneg (by norm_num) ha0)
            (mul_nonneg (Real.rpow_nonneg hmin.le _) (Real.rpow_nonneg hbase.le _))
        have hradpow : 0 ≤ Real.rpow
            (2 * a * (Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
              Real.rpow (1 + (k : ℝ) ^ 2) (-(h + 1 / 2)))) (1 / 2 : ℝ) :=
          Real.rpow_nonneg hrad _
        gcongr <;> try assumption <;> positivity
    _ = _ := by ring

theorem scalarWindowFeature_inner_source (κ h t : ℝ) (k : ℤ)
    (aWidth c s M : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k aWidth c s ξ| ≤ M) :
    inner ℝ (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh)
      (scalarWindowSourceL2 κ h k aWidth c s M hκ hh hbound) =
      ∫ ξ, AlignmentMaternSpectralFeature.density κ h ξ *
        (AlignmentMaternScalarFeature.scalarPhase t ξ *
          scalarWindowSourceField κ h k aWidth c s ξ) := by
  letI : IsFiniteMeasure (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
    AlignmentMaternSpectralFeature.spectralMeasure_isFinite κ h hκ hh
  rw [L2.inner_def]
  have hfeature := (AlignmentMaternScalarFeature.scalarPhaseMemLp κ h t hκ hh).coeFn_toLp
  have hsource :=
    (scalarWindowSourceField_memLp_of_bound κ h k aWidth c s M hκ hh hbound).coeFn_toLp
  calc
    (∫ ξ, inner ℝ
        (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh ξ)
        (scalarWindowSourceL2 κ h k aWidth c s M hκ hh hbound ξ)
        ∂AlignmentMaternSpectralFeature.spectralMeasure κ h) =
      ∫ ξ, AlignmentMaternScalarFeature.scalarPhase t ξ *
        scalarWindowSourceField κ h k aWidth c s ξ
        ∂AlignmentMaternSpectralFeature.spectralMeasure κ h := by
          apply integral_congr_ae
          filter_upwards [hfeature, hsource] with ξ hf hs
          change AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh ξ =
            AlignmentMaternScalarFeature.scalarPhase t ξ at hf
          change scalarWindowSourceL2 κ h k aWidth c s M hκ hh hbound ξ =
            scalarWindowSourceField κ h k aWidth c s ξ at hs
          rw [hf, hs, Real.inner_apply]
    _ = ∫ ξ, AlignmentMaternSpectralFeature.density κ h ξ *
        (AlignmentMaternScalarFeature.scalarPhase t ξ *
          scalarWindowSourceField κ h k aWidth c s ξ) :=
      AlignmentMaternScalarFeature.integral_spectral_eq_weighted κ h hκ _

theorem scalarWindow_weighted_source_eq (κ h t : ℝ) (k : ℤ)
    (aWidth c s ξ : ℝ) (hκ : 0 < κ) :
    AlignmentMaternSpectralFeature.density κ h ξ *
        (AlignmentMaternScalarFeature.scalarPhase t ξ *
          scalarWindowSourceField κ h k aWidth c s ξ) =
      scalarWindowWeightedOutput t k aWidth c s ξ := by
  classical
  unfold scalarWindowSourceField scalarWindowWeightedOutput
  by_cases h₁ : ξ ∈ window k aWidth <;>
    by_cases h₂ : ξ ∈ window (-k) aWidth <;>
    simp [h₁, h₂] <;>
    field_simp [ne_of_gt (AlignmentMaternSpectralFeature.density_pos κ h ξ hκ)] <;> ring_nf

theorem scalarWindowFeature_inner_eq_weightedOutput (κ h t : ℝ) (k : ℤ)
    (aWidth c s M : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k aWidth c s ξ| ≤ M) :
    inner ℝ (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh)
      (scalarWindowSourceL2 κ h k aWidth c s M hκ hh hbound) =
      ∫ ξ, scalarWindowWeightedOutput t k aWidth c s ξ := by
  rw [scalarWindowFeature_inner_source κ h t k aWidth c s M hκ hh hbound]
  apply integral_congr_ae
  filter_upwards with ξ
  exact scalarWindow_weighted_source_eq κ h t k aWidth c s ξ hκ

theorem integral_cos_window (k : ℤ) (a t : ℝ) (ht : t ≠ 0) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Real.cos (2 * Real.pi * ξ * t)) =
      windowMultiplier a t * Real.cos (2 * Real.pi * (k : ℝ) * t) := by
  have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (by positivity) ht
  have hcomp := intervalIntegral.integral_comp_mul_left (f := Real.cos)
    (a := (k : ℝ) - a / 2) (b := (k : ℝ) + a / 2)
    (c := 2 * Real.pi * t) hc
  have hrewrite :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        Real.cos (2 * Real.pi * ξ * t)) =
        (2 * Real.pi * t)⁻¹ *
          (∫ x in (2 * Real.pi * t) * ((k : ℝ) - a / 2)..
            (2 * Real.pi * t) * ((k : ℝ) + a / 2), Real.cos x) := by
    have hf : (fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * t)) =
        fun ξ => Real.cos ((2 * Real.pi * t) * ξ) := by
      funext ξ
      congr 1
      ring
    rw [hf]
    simpa only [smul_eq_mul] using hcomp
  rw [hrewrite, integral_cos]
  unfold windowMultiplier
  rw [if_neg ht]
  have hs1 :
      Real.sin (2 * Real.pi * t * ((k : ℝ) + a / 2)) =
        Real.sin (2 * Real.pi * (k : ℝ) * t + Real.pi * a * t) := by ring_nf
  have hs2 :
      Real.sin (2 * Real.pi * t * ((k : ℝ) - a / 2)) =
        Real.sin (2 * Real.pi * (k : ℝ) * t - Real.pi * a * t) := by ring_nf
  rw [hs1, hs2, Real.sin_add, Real.sin_sub]
  have hmul : (2 * Real.pi * t)⁻¹ *
      (2 * Real.cos (2 * Real.pi * (k : ℝ) * t) * Real.sin (Real.pi * a * t)) =
      (Real.sin (Real.pi * a * t) / (Real.pi * t)) *
        Real.cos (2 * Real.pi * (k : ℝ) * t) := by
    field_simp
  convert hmul using 1 <;> ring_nf

theorem integral_sin_window (k : ℤ) (a t : ℝ) (ht : t ≠ 0) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      Real.sin (2 * Real.pi * ξ * t)) =
      windowMultiplier a t * Real.sin (2 * Real.pi * (k : ℝ) * t) := by
  have hc : 2 * Real.pi * t ≠ 0 := mul_ne_zero (by positivity) ht
  have hcomp := intervalIntegral.integral_comp_mul_left (f := Real.sin)
    (a := (k : ℝ) - a / 2) (b := (k : ℝ) + a / 2)
    (c := 2 * Real.pi * t) hc
  have hrewrite :
      (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        Real.sin (2 * Real.pi * ξ * t)) =
        (2 * Real.pi * t)⁻¹ *
          (∫ x in (2 * Real.pi * t) * ((k : ℝ) - a / 2)..
            (2 * Real.pi * t) * ((k : ℝ) + a / 2), Real.sin x) := by
    have hf : (fun ξ : ℝ => Real.sin (2 * Real.pi * ξ * t)) =
        fun ξ => Real.sin ((2 * Real.pi * t) * ξ) := by
      funext ξ
      congr 1
      ring
    rw [hf]
    simpa only [smul_eq_mul] using hcomp
  rw [hrewrite, integral_sin]
  unfold windowMultiplier
  rw [if_neg ht]
  have hc1 :
      Real.cos (2 * Real.pi * t * ((k : ℝ) - a / 2)) =
        Real.cos (2 * Real.pi * (k : ℝ) * t - Real.pi * a * t) := by ring_nf
  have hc2 :
      Real.cos (2 * Real.pi * t * ((k : ℝ) + a / 2)) =
        Real.cos (2 * Real.pi * (k : ℝ) * t + Real.pi * a * t) := by ring_nf
  rw [hc1, hc2, Real.cos_sub, Real.cos_add]
  have hmul : (2 * Real.pi * t)⁻¹ *
      (2 * Real.sin (2 * Real.pi * (k : ℝ) * t) * Real.sin (Real.pi * a * t)) =
      (Real.sin (Real.pi * a * t) / (Real.pi * t)) *
        Real.sin (2 * Real.pi * (k : ℝ) * t) := by
    field_simp
  convert hmul using 1 <;> ring_nf

theorem integral_scalarPhase_window (k : ℤ) (a t : ℝ) :
    (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      AlignmentMaternScalarFeature.scalarPhase t ξ) =
      windowMultiplier a t * AlignmentMaternScalarFeature.scalarPhase t (k : ℝ) := by
  by_cases ht : t = 0
  · simp [AlignmentMaternScalarFeature.scalarPhase, windowMultiplier, ht,
      intervalIntegral.integral_const]
  · change (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
      (Real.cos (2 * Real.pi * ξ * t) + Real.sin (2 * Real.pi * ξ * t))) = _
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      integral_cos_window k a t ht, integral_sin_window k a t ht]
    simp [AlignmentMaternScalarFeature.scalarPhase, windowMultiplier, ht]
    ring

theorem integral_window_indicator_phase (k : ℤ) (a t c : ℝ) (ha : 0 ≤ a) :
    (∫ ξ, Set.indicator (window k a)
      (fun ξ => c * AlignmentMaternScalarFeature.scalarPhase t ξ) ξ) =
      c * (∫ ξ in ((k : ℝ) - a / 2)..((k : ℝ) + a / 2),
        AlignmentMaternScalarFeature.scalarPhase t ξ) := by
  have hcompact : IsCompact (window k a) := by exact isCompact_Icc
  have hcont : Continuous (fun ξ : ℝ => c * AlignmentMaternScalarFeature.scalarPhase t ξ) := by
    unfold AlignmentMaternScalarFeature.scalarPhase
    fun_prop
  have hmeas : MeasurableSet (window k a) := hcompact.measurableSet
  have hI : Integrable (Set.indicator (window k a)
      (fun ξ => c * AlignmentMaternScalarFeature.scalarPhase t ξ)) volume :=
    (hcont.continuousOn.integrableOn_compact hcompact).integrable_indicator hmeas
  rw [integral_indicator hmeas]
  simp only [window]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith :
    (k : ℝ) - a / 2 ≤ (k : ℝ) + a / 2)]
  rw [intervalIntegral.integral_const_mul]

theorem scalarWindowWeightedOutput_integral (k : ℤ) (aWidth t c s : ℝ)
    (haWidth : 0 ≤ aWidth) :
    (∫ ξ, scalarWindowWeightedOutput t k aWidth c s ξ) =
      ((c + s) / 2) *
          (∫ ξ in ((k : ℝ) - aWidth / 2)..((k : ℝ) + aWidth / 2),
            AlignmentMaternScalarFeature.scalarPhase t ξ) +
        ((c - s) / 2) *
          (∫ ξ in ((-k : ℝ) - aWidth / 2)..((-k : ℝ) + aWidth / 2),
            AlignmentMaternScalarFeature.scalarPhase t ξ) := by
  classical
  let f₁ : ℝ → ℝ := fun ξ => ((c + s) / 2) * AlignmentMaternScalarFeature.scalarPhase t ξ
  let f₂ : ℝ → ℝ := fun ξ => ((c - s) / 2) * AlignmentMaternScalarFeature.scalarPhase t ξ
  have hcompact₁ : IsCompact (window k aWidth) := by exact isCompact_Icc
  have hcompact₂ : IsCompact (window (-k) aWidth) := by exact isCompact_Icc
  have hc₁ : Continuous f₁ := by dsimp [f₁]; unfold AlignmentMaternScalarFeature.scalarPhase; fun_prop
  have hc₂ : Continuous f₂ := by dsimp [f₂]; unfold AlignmentMaternScalarFeature.scalarPhase; fun_prop
  have hi₁ : Integrable (Set.indicator (window k aWidth) f₁) volume :=
    (hc₁.continuousOn.integrableOn_compact hcompact₁).integrable_indicator hcompact₁.measurableSet
  have hi₂ : Integrable (Set.indicator (window (-k) aWidth) f₂) volume :=
    (hc₂.continuousOn.integrableOn_compact hcompact₂).integrable_indicator hcompact₂.measurableSet
  have hfun : scalarWindowWeightedOutput t k aWidth c s =
      Set.indicator (window k aWidth) f₁ + Set.indicator (window (-k) aWidth) f₂ := by
    funext ξ
    simp [scalarWindowWeightedOutput, f₁, f₂, Set.indicator]
  rw [hfun]
  change (∫ ξ, Set.indicator (window k aWidth) f₁ ξ +
      Set.indicator (window (-k) aWidth) f₂ ξ) = _
  rw [integral_add hi₁ hi₂,
    integral_window_indicator_phase k aWidth t ((c + s) / 2) haWidth,
    integral_window_indicator_phase (-k) aWidth t ((c - s) / 2) haWidth]
  simp

theorem scalarWindowFeature_inner_eq_mode (κ h t : ℝ) (k : ℤ)
    (aWidth c s M : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (haWidth : 0 ≤ aWidth)
    (hbound : ∀ ξ, |scalarWindowSourceField κ h k aWidth c s ξ| ≤ M) :
    inner ℝ (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh)
      (scalarWindowSourceL2 κ h k aWidth c s M hκ hh hbound) =
      windowMultiplier aWidth t *
        (c * Real.cos (2 * Real.pi * (k : ℝ) * t) +
          s * Real.sin (2 * Real.pi * (k : ℝ) * t)) := by
  rw [scalarWindowFeature_inner_eq_weightedOutput κ h t k aWidth c s M hκ hh hbound,
    scalarWindowWeightedOutput_integral k aWidth t c s haWidth]
  rw [integral_scalarPhase_window k aWidth t]
  have hneg :
      (∫ ξ in (- (k : ℝ) - aWidth / 2)..(- (k : ℝ) + aWidth / 2),
        AlignmentMaternScalarFeature.scalarPhase t ξ) =
        windowMultiplier aWidth t * AlignmentMaternScalarFeature.scalarPhase t (-k : ℝ) := by
    simpa only [Int.cast_neg] using integral_scalarPhase_window (-k) aWidth t
  rw [hneg]
  have hphase : AlignmentMaternScalarFeature.scalarPhase t (- (k : ℝ)) =
      Real.cos (2 * Real.pi * (k : ℝ) * t) -
        Real.sin (2 * Real.pi * (k : ℝ) * t) := by
    unfold AlignmentMaternScalarFeature.scalarPhase
    rw [show 2 * Real.pi * (- (k : ℝ)) * t = -(2 * Real.pi * (k : ℝ) * t) by ring,
      Real.cos_neg, Real.sin_neg]
    ring
  rw [hphase]
  by_cases ht : t = 0
  · simp [windowMultiplier, ht, AlignmentMaternScalarFeature.scalarPhase]
    ring
  · simp [windowMultiplier, ht, AlignmentMaternScalarFeature.scalarPhase]
    ring

/-- The L² source representing one finite trigonometric mode. -/
noncomputable def scalarModeSource (κ h : ℝ) (a : ℝ) (k : ℤ)
    (coeff : ℤ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Lp ℝ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) := by
  let c := (coeff k).1
  let s := (coeff k).2
  let M := (|c| + |s|) *
    Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)
  exact scalarWindowSourceL2 κ h k a c s M hκ hh
    (fun ξ => scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ)

/-- Finite Fourier data has an actual spectral preimage whose feature is the
same trigonometric polynomial multiplied by one positive window multiplier. -/
noncomputable def finiteFourierWindowSource (κ h : ℝ) (a : ℝ)
    (F : Finset ℤ) (coeff : ℤ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Lp ℝ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  ∑ k ∈ F, scalarModeSource κ h a k coeff hκ hh ha0 ha1

theorem scalarFeature_inner_finiteFourierWindowSource (κ h t a : ℝ)
    (F : Finset ℤ) (coeff : ℤ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    inner ℝ (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh)
      (finiteFourierWindowSource κ h a F coeff hκ hh ha0 ha1) =
      ∑ k ∈ F, windowMultiplier a t *
        ((coeff k).1 * Real.cos (2 * Real.pi * (k : ℝ) * t) +
          (coeff k).2 * Real.sin (2 * Real.pi * (k : ℝ) * t)) := by
  classical
  unfold finiteFourierWindowSource
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold scalarModeSource
  let c := (coeff k).1
  let s := (coeff k).2
  let M := (|c| + |s|) *
    Real.rpow (κ ^ 2 + (|(k : ℝ)| + 1) ^ 2) (h + 1 / 2)
  simpa [c, s, M] using
    scalarWindowFeature_inner_eq_mode κ h t k a c s M hκ hh ha0
      (fun ξ => scalarWindowSourceField_abs_bound κ h k a c s hκ hh ha0 ha1 ξ)

theorem finiteFourierWindowSource_norm_le_sum (κ h : ℝ) (a : ℝ)
    (F : Finset ℤ) (coeff : ℤ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖finiteFourierWindowSource κ h a F coeff hκ hh ha0 ha1‖ ≤
      ∑ k ∈ F, ‖scalarModeSource κ h a k coeff hκ hh ha0 ha1‖ := by
  classical
  simp [finiteFourierWindowSource, norm_sum_le]

theorem scalarModeSource_inner_zero_of_ne (κ h a : ℝ) (n m : ℕ)
    (coeff : ℤ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haLt : a < 1) (hnm : n ≠ m) :
    inner ℝ (scalarModeSource κ h a (Int.ofNat (n + 1)) coeff hκ hh ha0 ha1)
      (scalarModeSource κ h a (Int.ofNat (m + 1)) coeff hκ hh ha0 ha1) = 0 := by
  let kn : ℤ := Int.ofNat (n + 1)
  let km : ℤ := Int.ofNat (m + 1)
  let cn := (coeff kn).1
  let sn := (coeff kn).2
  let cm := (coeff km).1
  let sm := (coeff km).2
  let Mn := (|cn| + |sn|) * Real.rpow (κ ^ 2 + (|((kn : ℤ) : ℝ)| + 1) ^ 2) (h + 1 / 2)
  let Mm := (|cm| + |sm|) * Real.rpow (κ ^ 2 + (|((km : ℤ) : ℝ)| + 1) ^ 2) (h + 1 / 2)
  have hboundn (ξ : ℝ) : |scalarWindowSourceField κ h kn a cn sn ξ| ≤ Mn := by
    exact scalarWindowSourceField_abs_bound κ h kn a cn sn hκ hh ha0 ha1 ξ
  have hboundm (ξ : ℝ) : |scalarWindowSourceField κ h km a cm sm ξ| ≤ Mm := by
    exact scalarWindowSourceField_abs_bound κ h km a cm sm hκ hh ha0 ha1 ξ
  have hdis := scalarWindowSupport_disjoint_of_positive_ne n m a haLt hnm
  simpa [scalarModeSource, kn, km, cn, sn, cm, sm, Mn, Mm] using
    scalarWindowSourceL2_inner_zero_of_disjoint κ h kn km a cn sn cm sm Mn Mm hκ hh
      hboundn hboundm hdis

noncomputable def finitePositiveFourierWindowSource (κ h : ℝ) (a : ℝ)
    (F : Finset ℕ) (coeff : ℕ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Lp ℝ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  ∑ n ∈ F, scalarModeSource κ h a (Int.ofNat (n + 1))
    (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0)) hκ hh ha0 ha1

/-- The zero-frequency coefficient has an actual spectral source supported on
the window centered at zero.  Its sine coefficient is set to zero, as expected
for the constant Fourier mode. -/
noncomputable def scalarZeroFrequencySource (κ h a c : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Lp ℝ 2 (AlignmentMaternSpectralFeature.spectralMeasure κ h) :=
  scalarModeSource κ h a 0 (fun _ => (c, 0)) hκ hh ha0 ha1

theorem scalarFeature_inner_zeroFrequencySource (κ h a t c : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    inner ℝ (AlignmentMaternScalarFeature.scalarFeature κ h t hκ hh)
      (scalarZeroFrequencySource κ h a c hκ hh ha0 ha1) =
      windowMultiplier a t * c := by
  unfold scalarZeroFrequencySource scalarModeSource
  let M := |c| * Real.rpow (κ ^ 2 + 1) (h + 1 / 2)
  have hbound (ξ : ℝ) : |scalarWindowSourceField κ h 0 a c 0 ξ| ≤ M := by
    simpa [M] using scalarWindowSourceField_abs_bound κ h 0 a c 0 hκ hh ha0 ha1 ξ
  simpa [M] using scalarWindowFeature_inner_eq_mode κ h t 0 a c 0 M hκ hh ha0
    hbound

theorem scalarZeroFrequencySource_inner_zero_positive (κ h a : ℝ) (n : ℕ)
    (coeff : ℕ → ℝ × ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haLt : a < 1) :
    inner ℝ (scalarZeroFrequencySource κ h a (coeff n).1 hκ hh ha0 ha1)
      (scalarModeSource κ h a (Int.ofNat (n + 1))
        (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0))
        hκ hh ha0 ha1) = 0 := by
  let M0 := |(coeff n).1| * Real.rpow (κ ^ 2 + 1) (h + 1 / 2)
  let Mp := (|(coeff n).1| + |(coeff n).2|) *
    Real.rpow (κ ^ 2 + (|(Int.ofNat (n + 1) : ℝ)| + 1) ^ 2) (h + 1 / 2)
  have hbound0 (ξ : ℝ) :
      |scalarWindowSourceField κ h 0 a (coeff n).1 0 ξ| ≤ M0 := by
    simpa [M0] using scalarWindowSourceField_abs_bound κ h 0 a (coeff n).1 0
      hκ hh ha0 ha1 ξ
  have hboundp (ξ : ℝ) :
      |scalarWindowSourceField κ h (Int.ofNat (n + 1)) a (coeff n).1 (coeff n).2 ξ| ≤ Mp := by
    simpa [Mp] using scalarWindowSourceField_abs_bound κ h (Int.ofNat (n + 1)) a
      (coeff n).1 (coeff n).2 hκ hh ha0 ha1 ξ
  have horth := scalarWindowSourceL2_inner_zero_of_disjoint κ h 0
    (Int.ofNat (n + 1)) a (coeff n).1 0 (coeff n).1 (coeff n).2 M0 Mp hκ hh
    hbound0 hboundp (scalarWindowSupport_zero_disjoint_of_positive n a haLt)
  simpa [scalarZeroFrequencySource, scalarModeSource, M0, Mp] using horth

theorem finitePositiveFourierWindowSource_inner_orthogonal_sum_sq
    (κ h a : ℝ) (F : Finset ℕ) (coeff : ℕ → ℝ × ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haLt : a < 1) :
    ‖finitePositiveFourierWindowSource κ h a F coeff hκ hh ha0 ha1‖ ^ 2 =
      ∑ n ∈ F, ‖scalarModeSource κ h a (Int.ofNat (n + 1))
        (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0))
        hκ hh ha0 ha1‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, finitePositiveFourierWindowSource]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single n]
  · simp [real_inner_self_eq_norm_sq]
  · intro m hm hmn
    let cf : ℤ → ℝ × ℝ := fun k =>
      if k = Int.ofNat (n + 1) then coeff n
      else if k = Int.ofNat (m + 1) then coeff m else (0,0)
    have hzero := scalarModeSource_inner_zero_of_ne κ h a m n cf
      hκ hh ha0 ha1 haLt hmn
    have hneq : Int.ofNat (n + 1) ≠ Int.ofNat (m + 1) := by
      intro heq
      have hnat : n + 1 = m + 1 := Int.ofNat_inj.mp heq
      omega
    simpa [scalarModeSource, cf, hneq, hneq.symm, hmn, hmn.symm] using hzero
  · intro hnot
    exact (hnot hn).elim

theorem finitePositiveFourierWindowSource_weighted_energy_le
    (κ h a : ℝ) (F : Finset ℕ) (coeff : ℕ → ℝ × ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (haLt : a < 1) :
    ‖finitePositiveFourierWindowSource κ h a F coeff hκ hh ha0 ha1‖ ^ 2 ≤
      (8 * a * Real.rpow (min 1 (κ ^ 2) / 2) (-(h + 1 / 2)) *
        (Real.rpow (κ ^ 2 + 2) (h + 1 / 2)) ^ 2) *
      ∑ n ∈ F, ((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
        Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) (h + 1 / 2) := by
  classical
  rw [finitePositiveFourierWindowSource_inner_orthogonal_sum_sq
    κ h a F coeff hκ hh ha0 ha1 haLt]
  let s := h + 1 / 2
  let B := Real.rpow (min 1 (κ ^ 2) / 2) (-s)
  let A := Real.rpow (κ ^ 2 + 2) s
  have hs : 0 < s := by dsimp [s]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hmode (n : ℕ) :
      ‖scalarModeSource κ h a (Int.ofNat (n + 1))
          (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0))
          hκ hh ha0 ha1‖ ^ 2 ≤
        (8 * a * B * A ^ 2) * ((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
          Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) s := by
    let c := (coeff n).1
    let z := (coeff n).2
    let x := 1 + ((n + 1 : ℕ) : ℝ) ^ 2
    let M := (|c| + |z|) *
      Real.rpow (κ ^ 2 + (|(Int.ofNat (n + 1) : ℝ)| + 1) ^ 2) s
    have hx : 0 < x := by dsimp [x]; positivity
    have hbound (ξ : ℝ) : |scalarWindowSourceField κ h (Int.ofNat (n + 1)) a c z ξ| ≤ M :=
      scalarWindowSourceField_abs_bound κ h (Int.ofNat (n + 1)) a c z hκ hh ha0 ha1 ξ
    have hsrc := scalarWindowSourceL2_norm_sobolev_bound κ h
      (Int.ofNat (n + 1)) a c z hκ hh ha0 ha1
    have hmodeeq : scalarModeSource κ h a (Int.ofNat (n + 1))
        (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0)) hκ hh ha0 ha1 =
        scalarWindowSourceL2 κ h (Int.ofNat (n + 1)) a c z M hκ hh hbound := by
      simp [scalarModeSource, c, z, M, s]
    have hnorm : ‖scalarWindowSourceL2 κ h (Int.ofNat (n + 1)) a c z M hκ hh hbound‖ ≤
        2 * Real.sqrt (c ^ 2 + z ^ 2) * A * Real.rpow x s *
          Real.sqrt (2 * a * B * Real.rpow x (-s)) := by
      simpa [s, B, A, x, M, c, z, Real.sqrt_eq_rpow] using hsrc
    have hy : 0 ≤ 2 * a * B * Real.rpow x (-s) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hB.le)
        (Real.rpow_nonneg hx.le _)
    have hboundSq :
        (2 * Real.sqrt (c ^ 2 + z ^ 2) * A * Real.rpow x s *
          Real.sqrt (2 * a * B * Real.rpow x (-s))) ^ 2 =
        8 * a * B * A ^ 2 * (c ^ 2 + z ^ 2) * Real.rpow x s := by
      have hpowx : (Real.rpow x s) ^ 2 = Real.rpow x (s + s) := by
        calc
          _ = Real.rpow x s * Real.rpow x s := by rw [pow_two]
          _ = _ := (Real.rpow_add hx s s).symm
      have hcancel : Real.rpow x (s + s) * Real.rpow x (-s) = Real.rpow x s := by
        calc
          _ = Real.rpow x ((s + s) + (-s)) := (Real.rpow_add hx _ _).symm
          _ = _ := by congr 1 <;> ring
      calc
        _ = 4 * (c ^ 2 + z ^ 2) * A ^ 2 *
            (Real.rpow x s) ^ 2 * (Real.sqrt (2 * a * B * Real.rpow x (-s))) ^ 2 := by
              calc
                _ = 4 * (Real.sqrt (c ^ 2 + z ^ 2)) ^ 2 * A ^ 2 *
                    (Real.rpow x s) ^ 2 * (Real.sqrt (2 * a * B * Real.rpow x (-s))) ^ 2 := by ring
                _ = _ := by rw [Real.sq_sqrt (by positivity)]
        _ = 4 * (c ^ 2 + z ^ 2) * A ^ 2 *
            Real.rpow x (s + s) * (2 * a * B * Real.rpow x (-s)) := by
              rw [show Real.sqrt (2 * a * B * Real.rpow x (-s)) ^ 2 =
                2 * a * B * Real.rpow x (-s) from Real.sq_sqrt hy]
              rw [hpowx]
        _ = 8 * a * B * A ^ 2 * (c ^ 2 + z ^ 2) * Real.rpow x s := by
              calc
                _ = 8 * a * B * A ^ 2 * (c ^ 2 + z ^ 2) *
                    (Real.rpow x (s + s) * Real.rpow x (-s)) := by ring
                _ = _ := by rw [hcancel]
    have hnormsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _))
      (Real.sqrt_nonneg _))).2 hnorm
    rw [hmodeeq]
    simpa [c, z, x, B, A, s, mul_assoc, mul_left_comm, mul_comm] using
      (hnormsq.trans_eq hboundSq)
  have hsum :
      (∑ n ∈ F, ‖scalarModeSource κ h a (Int.ofNat (n + 1))
        (fun k => if k = Int.ofNat (n + 1) then coeff n else (0,0))
        hκ hh ha0 ha1‖ ^ 2) ≤
      ∑ n ∈ F, (8 * a * B * A ^ 2) *
        ((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
          Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) s := by
    apply Finset.sum_le_sum
    intro n hn
    exact hmode n
  calc
    _ ≤ ∑ n ∈ F, (8 * a * B * A ^ 2) *
        ((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
          Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) s := hsum
    _ = (8 * a * B * A ^ 2) *
        ∑ n ∈ F, ((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
          Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) s := by
            calc
              _ = ∑ n ∈ F, (8 * a * B * A ^ 2) *
                    (((coeff n).1 ^ 2 + (coeff n).2 ^ 2) *
                      Real.rpow (1 + ((n + 1 : ℕ) : ℝ) ^ 2) s) := by
                        apply Finset.sum_congr rfl
                        intro n hn
                        ring
              _ = _ := by rw [Finset.mul_sum]
    _ = _ := by simp [B, A, s] <;> ring

theorem windowMultiplier_pos_on_unit (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < windowMultiplier a t := by
  unfold windowMultiplier
  by_cases ht : t = 0
  · simp [ht, ha0]
  · rw [if_neg ht]
    have harg0 : 0 ≤ Real.pi * a * t := by positivity
    have harg1 : Real.pi * a * t ≤ Real.pi / 2 := by
      calc
        Real.pi * a * t ≤ Real.pi * (1 / 2) * t := by gcongr
        _ ≤ Real.pi * (1 / 2) * 1 := by gcongr
        _ = Real.pi / 2 := by ring
    have hs := Real.mul_le_sin harg0 harg1
    have hsin : 0 < Real.sin (Real.pi * a * t) := by
      have : 0 < (2 / Real.pi) * (Real.pi * a * t) := by positivity
      exact lt_of_lt_of_le this hs
    exact div_pos hsin (mul_pos Real.pi_pos (lt_of_le_of_ne ht0 (Ne.symm ht)))

theorem windowMultiplier_lower_on_unit (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a * (2 / Real.pi) ≤ windowMultiplier a t := by
  unfold windowMultiplier
  by_cases ht : t = 0
  · rw [if_pos ht]
    have htwo : (2 : ℝ) / Real.pi ≤ 1 := (div_le_one₀ Real.pi_pos).2 Real.two_le_pi
    calc
      a * (2 / Real.pi) ≤ a * 1 := mul_le_mul_of_nonneg_left htwo ha0.le
      _ = a := mul_one _
  · rw [if_neg ht]
    have harg0 : 0 ≤ Real.pi * a * t := by positivity
    have harg1 : Real.pi * a * t ≤ Real.pi / 2 := by
      calc
        Real.pi * a * t ≤ Real.pi * (1 / 2) * t := by gcongr
        _ ≤ Real.pi * (1 / 2) * 1 := by gcongr
        _ = Real.pi / 2 := by ring
    have hs := Real.mul_le_sin harg0 harg1
    have hden : 0 < Real.pi * t := mul_pos Real.pi_pos (lt_of_le_of_ne ht0 (Ne.symm ht))
    rw [le_div_iff₀ hden]
    calc
      a * (2 / Real.pi) * (Real.pi * t) = (2 / Real.pi) * (Real.pi * a * t) := by ring
      _ ≤ Real.sin (Real.pi * a * t) := hs

end BrownianSharp.AlignmentMaternSpectralWindow
