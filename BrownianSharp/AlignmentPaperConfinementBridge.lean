import BrownianSharp.AlignmentPaperGenericBumpCertified
import BrownianSharp.AlignmentPaperContinuumSynthesis
import BrownianSharp.IndependentComparison
import BrownianSharp.ExponentialGlobalization
import BrownianSharp.SmoothGridConfinement
import BrownianSharp.PeriodicNativeCover

/-! Bridge from the manuscript's Theorem 2.1 (the continuum confinement
`eventually_bumpSynthesis_confinement`, here for the smooth atom) to the form
used by the entropy lower bounds: the exponential bound for the sup-norm of
the Gaussian synthesis at all positive grades, and the translated-ball cap
(3.9) obtained from it by the finite-dimensional Anderson inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace BrownianSharp.AlignmentPaperConfinementBridge
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumGenericBump
  AlignmentPaperGenericBumpCertified AlignmentPaperContinuumSynthesis

theorem cubeSup_mass_lt_one {d n : ℕ} (hd : 0 < d) (r : ℝ) :
    (productStandardGaussian (LayerIndex d n)).real
      {z | ∀ x ∈ cubeSet d, |bumpSynthesis AdmissibleBump.smoothAtomAdmissible z x| ≤ r} < 1 := by
  refine lt_of_le_of_lt (measureReal_mono ?_) (smoothGoodUniformEvent_mass_lt_one hd r)
  intro z hz q
  exact hz (nativeMidpointBrownianAnchor q.1).val
    (fun i _ => (nativeMidpointBrownianAnchor q.1).property i)

/-- Theorem 2.1 for the smooth atom, at every positive grade. -/
theorem smoothAtom_confinement_all_grades {d : ℕ} (hd : 2 ≤ d) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ n : ℕ, 0 < n →
      (productStandardGaussian (LayerIndex d n)).real
        {z | ∀ x ∈ cubeSet d, |bumpSynthesis AdmissibleBump.smoothAtomAdmissible z x| ≤
          a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
        Real.exp (-b * nativeDimension d n) := by
  obtain ⟨a, b, ha, hb, N, hN⟩ :=
    eventually_bumpSynthesis_confinement hd AdmissibleBump.smoothAtomAdmissible
  obtain ⟨c, hc, hall⟩ := eventual_exponential_bound_global
    (fun n => (productStandardGaussian (LayerIndex d n)).real
      {z | ∀ x ∈ cubeSet d, |bumpSynthesis AdmissibleBump.smoothAtomAdmissible z x| ≤
        a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)})
    (nativeDimension d) 1 N
    (fun n hn => (by positivity : (0:ℝ) < 2 ^ n).trans_le
      (nativeDimension_ge_dyadic d n (by omega)))
    (fun n hn => cubeSup_mass_lt_one (by omega) _) hb hN
  exact ⟨a, c, ha, hc, fun n hn => hall n hn⟩

/-- Sup-norm form of Theorem 2.1 for any family of continuous functions
whose values contain those of the cube synthesis. -/
theorem norm_confinement_all_grades {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {d : ℕ} (hd : 2 ≤ d) (F : ∀ n : ℕ, (LayerIndex d n → ℝ) → C(α, ℝ))
    (hsup : ∀ n z, ∀ s ∈ cubeSet d,
      ∃ y, F n z y = bumpSynthesis AdmissibleBump.smoothAtomAdmissible z s) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ n : ℕ, 0 < n →
      (productStandardGaussian (LayerIndex d n)).real
        {z | ‖F n z‖ ≤ a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
        Real.exp (-b * nativeDimension d n) := by
  obtain ⟨a, b, ha, hb, h⟩ := smoothAtom_confinement_all_grades hd
  refine ⟨a, b, ha, hb, fun n hn => (measureReal_mono ?_).trans (h n hn)⟩
  intro z hz s hs
  obtain ⟨y, hy⟩ := hsup n z s hs
  rw [← hy]
  exact (Real.norm_eq_abs _ ▸ (F n z).norm_coe_le_norm y).trans hz

theorem periodicNative_cube_eq {d n : ℕ} (z : LayerIndex d n → ℝ)
    (s : Fin d → ℝ) (hs : s ∈ cubeSet d) :
    periodicNativeSynthesisLinear z (realCubeToTorus s) =
      bumpSynthesis AdmissibleBump.smoothAtomAdmissible z s := by
  rw [periodicNativeSynthesisLinear_apply, smoothPeriodicSynthesis_realCubeToTorus z s hs]
  rfl

/-- Anderson's inequality for a finite Gaussian linear synthesis into a normed
space: a ball of radius `ρ` around any centre has at most the mass of the
centered ball of radius `2ρ`. -/
theorem linearSynthesis_ball_mass_le {ι V : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (G : (ι → ℝ) →ₗ[ℝ] V) (f : V) (ρ : ℝ) :
    productStandardGaussian ι {z | ‖G z - f‖ ≤ ρ} ≤
      productStandardGaussian ι {z | ‖G z‖ ≤ 2 * ρ} := by
  classical
  let N := Fintype.card ι
  have hN : 0 < N := Fintype.card_pos
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  let Rl : (Fin N → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.funLeft ℝ ℝ e.symm
  have hmp : MeasurePreserving Rl (productStandardGaussian (Fin N)) (productStandardGaussian ι) := by
    have hf : (Rl : (Fin N → ℝ) → ι → ℝ) = MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e := by
      funext x a
      simp [Rl, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
    rw [hf]
    exact measurePreserving_piCongrLeft (α := fun _ : ι => ℝ) (fun _ => gaussianReal 0 1) e
  let H : (Fin N → ℝ) →ₗ[ℝ] V := G ∘ₗ Rl
  have hcont : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hS : MeasurableSet {z | ‖G z - f‖ ≤ ρ} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hT : MeasurableSet {z | ‖G z‖ ≤ 2 * ρ} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [← hmp.measure_preimage hS.nullMeasurableSet, ← hmp.measure_preimage hT.nullMeasurableSet]
  let C : Set (Fin N → ℝ) := {x | ‖H x‖ ≤ 2 * ρ}
  have hCconv : Convex ℝ C := by
    have h := (convex_closedBall (0 : V) (2 * ρ)).linear_preimage H
    convert h using 1
    ext x
    simp [C, dist_zero_right]
  have hCsymm : ∀ x ∈ C, -x ∈ C := fun x hx => by simpa [C] using hx
  have hCmeas : MeasurableSet C :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  by_cases hne : ∃ x₀, ‖H x₀ - f‖ ≤ ρ
  · obtain ⟨x₀, hx₀⟩ := hne
    refine le_trans (measure_mono fun x hx => ?_)
      (standardGaussian_linear_shift_le_of_pos hN C (LinearMap.id) (-x₀) hCconv hCsymm hCmeas)
    change ‖H (x + -x₀)‖ ≤ 2 * ρ
    have hx' : ‖H x - f‖ ≤ ρ := hx
    calc ‖H (x + -x₀)‖ = ‖(H x - f) - (H x₀ - f)‖ := by
          rw [map_add, map_neg]; congr 1; abel
      _ ≤ ‖H x - f‖ + ‖H x₀ - f‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith
  · have : {x : Fin N → ℝ | ‖H x - f‖ ≤ ρ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hne ⟨x, hx⟩
    change productStandardGaussian (Fin N) {x | ‖H x - f‖ ≤ ρ} ≤ _
    rw [this, measure_empty]
    exact zero_le

/-- The covering obstruction for a dilated Gaussian synthesis: a class of mass
above `m · Q` cannot be covered by `m` balls of radius `ρ`, provided the
centered sup-norm ball of radius `ε₀` has mass at most `Q` and `2ρ ≤ A ε₀`. -/
theorem scaled_externalCover_gt {α ι : Type*} [Fintype ι] [Nonempty ι] [TopologicalSpace α]
    [CompactSpace α] (F : (ι → ℝ) →ₗ[ℝ] C(α, ℝ)) {A ε₀ : ℝ} (hA : 0 < A) (ρ : ℝ≥0)
    (hρ : 2 * ρ ≤ A * ε₀) (E : Set (ι → ℝ)) (K : Set C(α, ℝ)) (Q : ℝ≥0∞) (m : ℕ)
    (hclass : ∀ z ∈ E, A • F z ∈ K)
    (hconf : productStandardGaussian ι {z | ‖F z‖ ≤ ε₀} ≤ Q)
    (hmass : (m : ℝ≥0∞) * Q < productStandardGaussian ι E) :
    (m : ℕ∞) < Metric.externalCoveringNumber ρ K := by
  refine externalCoveringNumber_gt_of_admissible_mass (productStandardGaussian ι)
    (fun z => A • F z) E K ρ Q m hclass (fun f => ?_) hmass
  refine le_trans (measure_mono fun z hz => ?_) (le_trans
    (linearSynthesis_ball_mass_le (A • F) f ρ) (le_trans (measure_mono fun z hz => ?_) hconf))
  · change edist (A • F z) f ≤ ρ at hz
    rw [edist_dist, dist_eq_norm] at hz
    exact (ENNReal.ofReal_le_ofReal_iff ρ.2).1 (by simpa using hz)
  · change ‖A • F z‖ ≤ 2 * ρ at hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA] at hz
    exact le_of_mul_le_mul_left (hz.trans hρ) hA

end BrownianSharp.AlignmentPaperConfinementBridge
