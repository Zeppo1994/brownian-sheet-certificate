import BrownianSharp.AlignmentExponentialContinuousCover
import BrownianSharp.PeriodicSynthesisScale
import BrownianSharp.SmoothGridConfinement
import BrownianSharp.NativeScaleCover
import BrownianSharp.PeriodicCoverRate
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement
import Mathlib.Tactic

/-! Compact-domain version of the native entropy lower bound. The only
synthesis-specific premise is exact agreement with the finite good-grid
linear forms at the supplied sample anchors. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentExponentialNativeEntropy

/-- Generic compact-domain entropy lower rate from a class-mass bound for a
finite Gaussian synthesis family. -/
theorem entropy_rate_of_scaled_native_class_mass
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    {d : ℕ} (hd : 2 ≤ d) (K : Set (C(α, ℝ)))
    (r β a : ℝ) (hr : 0 < r) (ha : 0 < a) (N₀ : ℕ)
    (synthesis : ∀ n : ℕ,
      (LayerIndex d n → ℝ) →ₗ[ℝ] C(α, ℝ))
    (hK : MeasurableSet K)
    (anchors : ∀ n : ℕ, SmoothGoodGrid d n → α)
    (hsample : ∀ (n : ℕ) (x : LayerIndex d n → ℝ) (q : SmoothGoodGrid d n),
      synthesis n x (anchors n q) =
        ∑ a₀, smoothLayerAtom smoothAtom q.val a₀ * x a₀)
    (hclass : ∀ n : ℕ, N₀ ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r β) • synthesis n x ∈ K}) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  obtain ⟨b,hb,hconf⟩ :=
    smoothGoodUniform_confinement_all_grades_of_ehrhard
      productGaussianEhrhard_certified hd
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
  let η : ℝ := smoothPeriodicRadiusConstant d (smoothMomentSlope d)
  have hη : 0 < η := smoothPeriodicRadiusConstant_pos d (smoothMomentSlope_pos d)
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
    let ε₀ : ℝ := η*Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))
    let ε : ℝ := A*ε₀
    let ρ : ℝ := (a*η)*periodicNativeRadius d q r β
    have hA : 0 < A := mul_pos ha (periodicSynthesisScale_pos (by omega) r β)
    have hε₀ : 0 < ε₀ := mul_pos hη (Real.sqrt_pos.2
      (mul_pos (by exact_mod_cast (by omega : 0<2*q)) (hyperbolicCount_pos (by omega))))
    have hε : 0 < ε := mul_pos hA hε₀
    have hρ : 0 < ρ := mul_pos (mul_pos ha hη) (periodicNativeRadius_pos hq)
    have hρε : ρ = ε := by
      dsimp [ε, ε₀, A, ρ]
      exact (periodicSynthesisScale_mul_confinement (d:=d) (q:=q)
        (by omega) a η r β).symm
    let Q := ENNReal.ofReal (Real.exp (-b*D))
    have hconfQ : productStandardGaussian (LayerIndex d (2*q))
        (smoothGoodUniformEvent d (2*q) ε₀) ≤ Q := by
      have h := ENNReal.ofReal_le_ofReal (hconf (2*q) (by omega))
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
      exact h
    let coeffEquiv := (Fintype.equivFin (LayerIndex d (2*q))).symm
    let G : (Fin (Fintype.card (LayerIndex d (2*q))) → ℝ) →ₗ[ℝ] C(α, ℝ) :=
      { toFun := fun x => A • synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv x)
        map_add' := by
          intro x y
          ext z
          change A * synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv (x+y)) z = _
          rw [show CameronMartinCover.reindexNative coeffEquiv (x+y) =
            CameronMartinCover.reindexNative coeffEquiv x + CameronMartinCover.reindexNative coeffEquiv y by
              ext a₀; simp [CameronMartinCover.reindexNative]]
          rw [map_add]
          change (A • (synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv x) +
            synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv y))) z = _
          rw [smul_add]
        map_smul' := by
          intro c x
          ext z
          change A * synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv (c • x)) z = _
          rw [show CameronMartinCover.reindexNative coeffEquiv (c • x) =
            c • CameronMartinCover.reindexNative coeffEquiv x by
              ext a₀; simp [CameronMartinCover.reindexNative]]
          rw [map_smul]
          change A * (c * (synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv x)) z) =
            c * (A * (synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv x)) z)
          ring }
    let gridEquiv := Fintype.equivFin (SmoothGoodGrid d (2*q))
    let t : Fin (Fintype.card (SmoothGoodGrid d (2*q))) → α :=
      fun j => anchors (2*q) (gridEquiv.symm j)
    have hrow : ∀ (x : Fin (Fintype.card (LayerIndex d (2*q))) → ℝ)
        (j : Fin (Fintype.card (SmoothGoodGrid d (2*q)))),
        AlignmentExponentialContinuousCover.sampleMap G t x j = A *
          (∑ a₀, smoothLayerAtom smoothAtom (gridEquiv.symm j).val a₀ *
            CameronMartinCover.reindexNative coeffEquiv x a₀) := by
      intro x j
      change (A • synthesis (2*q) (CameronMartinCover.reindexNative coeffEquiv x))
        (anchors (2*q) (gridEquiv.symm j)) = _
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hsample]
    have hset : {x : Fin (Fintype.card (LayerIndex d (2*q))) → ℝ |
        ‖AlignmentExponentialContinuousCover.sampleMap G t x‖ ≤ ε} =
        (CameronMartinCover.reindexNative coeffEquiv) ⁻¹'
          smoothGoodUniformEvent d (2*q) ε₀ := by
      ext x
      change (‖AlignmentExponentialContinuousCover.sampleMap G t x‖ ≤ ε) ↔
        CameronMartinCover.reindexNative coeffEquiv x ∈
          smoothGoodUniformEvent d (2*q) ε₀
      rw [pi_norm_le_iff_of_nonneg (le_of_lt hε)]
      change (∀ j, ‖AlignmentExponentialContinuousCover.sampleMap G t x j‖ ≤ ε) ↔
        (∀ q' : SmoothGoodGrid d (2*q),
          |∑ a₀, smoothLayerAtom smoothAtom q'.val a₀ *
            CameronMartinCover.reindexNative coeffEquiv x a₀| ≤ ε₀)
      simp_rw [Real.norm_eq_abs, hrow, abs_mul, abs_of_pos hA]
      constructor
      · intro h q'
        have hh := h (gridEquiv q')
        exact (mul_le_mul_iff_right₀ hA).mp (by simpa using hh)
      · intro h j
        exact mul_le_mul_of_nonneg_left (h (gridEquiv.symm j)) hA.le
    have hconfQ' : productStandardGaussian (Fin (Fintype.card (LayerIndex d (2*q))))
        {x | ‖AlignmentExponentialContinuousCover.sampleMap G t x‖ ≤ ε} ≤ Q := by
      rw [hset]
      have hEgrid : MeasurableSet (smoothGoodUniformEvent d (2*q) ε₀) := by
        unfold smoothGoodUniformEvent
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter (fun q' => measurableSet_le (by fun_prop) measurable_const)
      rw [(reindexNative_measurePreserving coeffEquiv).measure_preimage
        hEgrid.nullMeasurableSet]
      exact hconfQ
    let E : Set (Fin (Fintype.card (LayerIndex d (2*q))) → ℝ) := {x | G x ∈ K}
    let Eorig : Set (LayerIndex d (2*q) → ℝ) :=
      {x | (A • synthesis (2*q) x) ∈ K}
    have hEorig : MeasurableSet Eorig := by
      apply hK.preimage
      exact (LinearMap.continuous_of_finiteDimensional (synthesis (2*q))).const_smul A |>.measurable
    have hEeq : E = (CameronMartinCover.reindexNative coeffEquiv) ⁻¹' Eorig := by
      ext x
      simp [E, Eorig, G, Set.mem_preimage, CameronMartinCover.reindexNative]
    have hmassFin : (1/2:ℝ≥0∞)^S ≤
        productStandardGaussian (Fin (Fintype.card (LayerIndex d (2*q)))) E := by
      rw [hEeq, (reindexNative_measurePreserving coeffEquiv).measure_preimage
        hEorig.nullMeasurableSet]
      exact hclass (2*q) (by omega)
    have hmass : ((2^(k-1):ℕ):ℝ≥0∞)*Q <
        productStandardGaussian (Fin (Fintype.card (LayerIndex d (2*q)))) E :=
      hbudget.trans_le hmassFin
    have hNfin : 0 < Fintype.card (LayerIndex d (2*q)) :=
      Fintype.card_pos_iff.mpr (nativeLayerIndex_nonempty d (2*q) (by omega))
    have hcover' := AlignmentExponentialContinuousCover.externalCoveringNumber_gt_of_admissible_mass
      hNfin G t E K (NNReal.mk ρ hρ.le) ε hρε.le hε Q (2^(k-1))
      (by intro x hx; exact hx) hconfQ' hmass
    have hrad : (NNReal.mk ρ hρ.le : ℝ) =
        ((a*η)*periodicNativeRadius d q r β) := rfl
    simpa [hrad, ρ] using hcover'
  obtain ⟨c,hc,hentropy⟩ := periodic_entropy_rate_of_cover_at_multiple K hd htwo hk₀
    r β (a*η) hr (mul_pos ha hη) hcover
  exact ⟨c,hc,k₀,hk₀,hentropy⟩

end BrownianSharp.AlignmentExponentialNativeEntropy
