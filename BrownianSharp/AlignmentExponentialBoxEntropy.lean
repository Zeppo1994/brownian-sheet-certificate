import BrownianSharp.AlignmentExponentialContinuousCover
import BrownianSharp.PeriodicSynthesisScale
import BrownianSharp.SmoothGridConfinement
import BrownianSharp.NativeClassReindex
import BrownianSharp.NativeScaleCover
import BrownianSharp.PeriodicCoverRate
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement
import Mathlib.Tactic

/-! Compact-domain entropy lower bound from arbitrarily small exponential
Gaussian class-mass exponents. The class mass is compared directly against
the uniform-confinement probability, without a finite shape cutoff. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentExponentialBoxEntropy

/-- Generic compact-domain entropy lower rate from class masses with every
positive exponential rate. This is the useful form when a fixed full-coordinate
Gaussian box has mass `exp(-o(D_n))`. -/
theorem entropy_rate_of_exponentially_large_native_class_mass
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    {d : ℕ} (hd : 2 ≤ d) (K : Set (C(α, ℝ)))
    (r β : ℝ) (hr : 0 < r)
    (synthesis : ∀ n : ℕ,
      (LayerIndex d n → ℝ) →ₗ[ℝ] C(α, ℝ))
    (anchors : ∀ n : ℕ, SmoothGoodGrid d n → α)
    (hsample : ∀ (n : ℕ) (x : LayerIndex d n → ℝ) (q : SmoothGoodGrid d n),
      synthesis n x (anchors n q) =
        ∑ a₀, smoothLayerAtom smoothAtom q.val a₀ * x a₀)
    (hclass : ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
        ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
          productStandardGaussian (LayerIndex d n)
            {x | (a*periodicSynthesisScale d n r β) • synthesis n x ∈ K}) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  obtain ⟨b,hb,hconf⟩ :=
    smoothGoodUniform_confinement_all_grades_of_ehrhard
      productGaussianEhrhard_certified hd
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
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter (fun q' => measurableSet_le (by fun_prop) measurable_const)
      rw [(reindexNative_measurePreserving coeffEquiv).measure_preimage
        hEgrid.nullMeasurableSet]
      exact hconfQ
    let E : Set (Fin (Fintype.card (LayerIndex d (2*q))) → ℝ) := {x | G x ∈ K}
    let Eorig : Set (LayerIndex d (2*q) → ℝ) :=
      {x | (A • synthesis (2*q) x) ∈ K}
    have hEeq : E = (CameronMartinCover.reindexNative coeffEquiv) ⁻¹' Eorig := by
      ext x
      simp [E, Eorig, G]
    have hmassFin : T ≤
        productStandardGaussian (Fin (Fintype.card (LayerIndex d (2*q)))) E := by
      rw [hEeq, reindexNative_measure_preimage_any coeffEquiv Eorig]
      simpa [T, D, Eorig, A] using hclass₀ (2*q) (by omega)
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

end BrownianSharp.AlignmentExponentialBoxEntropy
