import BrownianSharp.Carl
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Tactic

/-!
# Ambient-space transfer for Kolmogorov widths
The comparison is useful for the manuscript's C versus L-infinity widths.
It isolates the exact sufficient analytic input: contractive linear smoothers
which approximate the embedded set uniformly. No existence of smoothers is
postulated as an axiom.
-/
noncomputable section
set_option maxHeartbeats 1000000
open scoped ENNReal
namespace BrownianSharp.AlignmentAmbientWidth
open HaarQuarter.TheoremD.Width
universe u
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem approximationError_le_of_pointwise (K : Set X) (V : Submodule ℝ X)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ K, ∃ v ∈ V, ‖x-v‖ ≤ ε) :
    approximationError K V ≤ ENNReal.ofReal ε := by
  apply iSup_le
  intro x
  obtain ⟨v,hv,hd⟩ := h x.val x.property
  calc
    Metric.infEDist x.val (V : Set X) ≤ edist x.val v :=
      Metric.infEDist_le_edist_of_mem hv
    _ = ENNReal.ofReal ‖x.val-v‖ := by rw [edist_dist, dist_eq_norm]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hd

theorem smooth_subspace_approximation
    (T : X →ₗᵢ[ℝ] Y) (S : Y →L[ℝ] X) (K : Set X)
    (V : Submodule ℝ Y) {m : ℕ} {δ ε : ℝ}
    (hV : Module.rank ℝ V ≤ (m : Cardinal))
    (hS : ∀ y, ‖S y‖ ≤ ‖y‖)
    (hδ : ∀ x ∈ K, ‖x-S (T x)‖ ≤ δ)
    (happrox : ∀ x ∈ K, ∃ v ∈ V, ‖T x-v‖ ≤ ε) :
    ∃ W : Submodule ℝ X, Module.rank ℝ W ≤ (m : Cardinal) ∧
      ∀ x ∈ K, ∃ w ∈ W, ‖x-w‖ ≤ δ+ε := by
  refine ⟨V.map S.toLinearMap, (rank_map_le S.toLinearMap V).trans hV, ?_⟩
  intro x hx
  obtain ⟨v,hv,hd⟩ := happrox x hx
  refine ⟨S v, Submodule.mem_map.mpr ⟨v,hv,rfl⟩, ?_⟩
  calc
    ‖x-S v‖ = ‖(x-S (T x)) + S (T x-v)‖ := by congr 1; simp
    _ ≤ ‖x-S (T x)‖ + ‖S (T x-v)‖ := norm_add_le _ _
    _ ≤ δ+ε := add_le_add (hδ x hx) ((hS _).trans hd)

theorem kolmogorovWidth_image_le
    (T : X →ₗᵢ[ℝ] Y) (K : Set X) (m : ℕ) :
    kolmogorovWidth (T '' K) m ≤ kolmogorovWidth K m := by
  unfold kolmogorovWidth
  apply le_iInf
  intro V
  let W : Submodule ℝ Y := V.val.map T.toLinearMap
  have hW : Module.rank ℝ W ≤ (m : Cardinal) :=
    (rank_map_le T.toLinearMap V.val).trans V.property
  calc
    kolmogorovWidth (T '' K) m ≤ approximationError (T '' K) W :=
      iInf_le (fun U : {U : Submodule ℝ Y // Module.rank ℝ U ≤ (m : Cardinal)} => approximationError (T '' K) U.val) ⟨W,hW⟩
    _ ≤ approximationError K V.val := by
      apply iSup_le
      rintro ⟨y,hy⟩
      obtain ⟨x,hx,rfl⟩ := hy
      have hset : (W : Set Y) = T '' (V.val : Set X) := by
        ext z
        exact Submodule.mem_map
      rw [hset, Metric.infEDist_image T.isometry]
      exact le_iSup (fun z : K => Metric.infEDist z.val (V.val : Set X)) ⟨x,hx⟩

/-- An isometric embedding preserves widths of a set whenever arbitrarily
accurate contractive linear smoothers back into the smaller ambient space
exist. The finite-dimensional approximating subspaces themselves need not
lie in that smaller space. -/
theorem kolmogorovWidth_eq_of_contractile_smoothing
    (T : X →ₗᵢ[ℝ] Y) (K : Set X)
    (hsmooth : ∀ δ : ℝ, 0 < δ → ∃ S : Y →L[ℝ] X,
      (∀ y, ‖S y‖ ≤ ‖y‖) ∧ ∀ x ∈ K, ‖x-S (T x)‖ ≤ δ)
    (m : ℕ) :
    kolmogorovWidth K m = kolmogorovWidth (T '' K) m := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hb
    let b := kolmogorovWidth (T '' K) m
    have hbne : b ≠ ⊤ := ne_of_lt hb
    have hεR : 0 < (ε : ℝ) := hε
    have hδ : 0 < (ε : ℝ)/2 := by positivity
    obtain ⟨S,hS,hSK⟩ := hsmooth ((ε : ℝ)/2) hδ
    have hr : 0 < b.toReal+(ε : ℝ)/2 := add_pos_of_nonneg_of_pos (ENNReal.toReal_nonneg) hδ
    have hwidth : b < ENNReal.ofReal (b.toReal+(ε : ℝ)/2) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hbne]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (by linarith)
    obtain ⟨V,hV,happrox⟩ :=
      Carl.exists_width_subspace_pointwise_approximation (T '' K) m hr hwidth
    have happroxK : ∀ x ∈ K, ∃ v ∈ V, ‖T x-v‖ ≤ b.toReal+(ε : ℝ)/2 := by
      intro x hx
      obtain ⟨v,hd⟩ := happrox (T x) ⟨x,hx,rfl⟩
      exact ⟨v.val,v.property,hd.le⟩
    obtain ⟨W,hW,hWK⟩ := smooth_subspace_approximation T S K V hV hS hSK happroxK
    have hbound : approximationError K W ≤ ENNReal.ofReal (b.toReal+(ε : ℝ)) := by
      apply approximationError_le_of_pointwise K W (by positivity)
      intro x hx
      obtain ⟨w,hw,hd⟩ := hWK x hx
      refine ⟨w,hw,?_⟩
      linarith
    calc
      kolmogorovWidth K m ≤ approximationError K W :=
        iInf_le (fun U : {U : Submodule ℝ X // Module.rank ℝ U ≤ (m : Cardinal)} =>
          approximationError K U.val) ⟨W,hW⟩
      _ ≤ ENNReal.ofReal (b.toReal+(ε : ℝ)) := hbound
      _ = b+ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
          ENNReal.ofReal_toReal hbne, ENNReal.ofReal_coe_nnreal]
  · exact kolmogorovWidth_image_le T K m

end BrownianSharp.AlignmentAmbientWidth
