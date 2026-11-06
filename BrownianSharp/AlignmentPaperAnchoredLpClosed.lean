import BrownianSharp.AlignmentPaperAnchoredLpCompact
import TauCeti.MeasureTheory.Function.Lp.UniformConvex
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-! Closedness and compactness of the anchored `Lᵖ` integration image for `1 < p < ∞`
(proof of Theorem 1.2, "closed by reflexivity of `Lᵖ`").

`Lᵖ(ℝ)` is uniformly convex, hence reflexive (Milman–Pettis, ported TauCeti sources), so its
closed unit ball is weakly compact.  If `T g_n → f` uniformly with `‖g_n‖ ≤ 1`, a weak cluster
point `g` of `(g_n)` has `‖g‖ ≤ 1`, and each evaluation `g ↦ (T g) t` is a weakly continuous
functional, so `(T g) t` is a cluster point of `(T g_n) t → f t`, i.e. `T g = f`. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BrownianSharp.AlignmentPaperAnchoredLpClosed

open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpCompact
open HaarQuarter

variable {d : ℕ}

/-- Theorem 1.2 (closedness of `K_{d,p}`), `1 < p < ∞`: the image of the closed unit ball of
`Lᵖ` under the anchored integration operator is closed in `C([0,1]^d)`. -/
theorem anchoredIntegrationLpImage_isClosed {p : ℝ} (hp : 1 < p) :
    IsClosed (anchoredIntegrationLpImage d p) := by
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := ENNReal.one_lt_ofReal.2 hp
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨hp1.le⟩
  refine closure_subset_iff_isClosed.1 fun f hf => ?_
  have hex : ∀ n : ℕ, ∃ g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d), ‖g‖ ≤ 1 ∧
      ∀ t, |anchoredLpValue p g t - f t| ≤ 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨f', ⟨g, hg, hgf⟩, hdist⟩ :=
      Metric.mem_closure_iff.1 hf (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨g, hg, fun t => ?_⟩
    rw [hgf t, ← Real.dist_eq, dist_comm]
    exact (ContinuousMap.dist_apply_le_dist t).trans hdist.le
  choose g hg1 hg2 using hex
  have hK := TauCeti.isCompact_toWeakSpace_closedBall (𝕜 := ℝ)
    (Lp.surjective_inclusionInDoubleDual hp1 ENNReal.ofReal_ne_top)
    (0 : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) 1
  obtain ⟨_, ⟨g₀, hg₀, rfl⟩, hcl⟩ := hK.exists_mapClusterPt (f := atTop)
    (u := fun n => toWeakSpace ℝ _ (g n))
    (le_principal_iff.2 (mem_map.2
      (Eventually.of_forall fun n => ⟨g n, by simpa using hg1 n, rfl⟩)))
  refine ⟨g₀, by simpa using hg₀, fun t => ?_⟩
  let ℓ : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ t).comp (anchoredIntegrationOperator p hp)
  have hcont : Continuous fun w : WeakSpace ℝ (Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) => ℓ w :=
    WeakBilin.eval_continuous (topDualPairing ℝ _).flip ℓ
  have hlim : Tendsto (fun n => ℓ (g n)) atTop (𝓝 (f t)) := by
    refine (tendsto_sub_nhds_zero_iff.1
      (squeeze_zero_norm (fun n => (Real.norm_eq_abs _).le.trans (hg2 n t))
        tendsto_one_div_add_atTop_nhds_zero_nat)).congr fun n => rfl
  exact eq_of_nhds_neBot
    ((MapClusterPt.continuousAt_comp hcont.continuousAt hcl).clusterPt.mono hlim)

/-- Theorem 1.2 (compactness of `K_{d,p}`), `1 < p < ∞`: the image of the `Lᵖ` unit ball under
the anchored integration operator is compact in `C([0,1]^d)`. -/
theorem anchoredIntegrationLpImage_isCompact {p : ℝ} (hp : 1 < p) :
    IsCompact (anchoredIntegrationLpImage d p) :=
  (anchoredIntegrationLpImage_closure_isCompact (d := d) hp).of_isClosed_subset
    (anchoredIntegrationLpImage_isClosed hp) subset_closure

end BrownianSharp.AlignmentPaperAnchoredLpClosed
