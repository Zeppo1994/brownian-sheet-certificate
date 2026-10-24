import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Bounded

/-!
An extended-nonnegative-real version of the Kolmogorov width. It is the
supremum, over points of `K`, of the infimum distance to a candidate linear
subspace, followed by the infimum over subspaces of dimension at most `m`.
For compact `K` this has the same finite value as the manuscript's
real-valued formula after taking `ENNReal.toReal`; the conversion is not
formalized in this module.
-/

namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Worst-case distance of a set `K` to a linear subspace `V`. -/
noncomputable def approximationError (K : Set X) (V : Submodule ℝ X) : ENNReal :=
  ⨆ x : {x : X // x ∈ K}, Metric.infEDist x.1 (V : Set X)

/-- Kolmogorov width: infimum of worst-case approximation error over linear
subspaces of dimension at most `m`. The cardinal-valued rank bound is used
instead of `finrank`, since Lean defines `finrank` to be zero at infinite
rank. -/
noncomputable def kolmogorovWidth (K : Set X) (m : ℕ) : ENNReal :=
  ⨅ V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)},
    approximationError K V.1

/-- Enlarging the approximating subspace cannot increase worst-case error. -/
theorem approximationError_anti (K : Set X) {V W : Submodule ℝ X}
    (hVW : V ≤ W) : approximationError K W ≤ approximationError K V := by
  unfold approximationError
  apply iSup_mono
  intro x
  exact Metric.infEDist_anti (SetLike.coe_subset_coe.mpr hVW)

/-- Kolmogorov widths are nonincreasing in the allowed dimension. This is
the monotonicity step used when the Carl inequality's `d_{j-1}` is bounded by
`d_m` for `j > m+1`. -/
theorem kolmogorovWidth_antitone (K : Set X) {m n : ℕ} (hmn : m ≤ n) :
    kolmogorovWidth K n ≤ kolmogorovWidth K m := by
  unfold kolmogorovWidth
  apply le_iInf
  intro V
  have hmn' : (m : Cardinal) ≤ (n : Cardinal) := by exact_mod_cast hmn
  exact iInf_le (fun W : {W : Submodule ℝ X // Module.rank ℝ W ≤ (n : Cardinal)} =>
      approximationError K W.1)
    ⟨V.1, le_trans V.2 hmn'⟩

/-- A set contained in an approximating subspace has zero error. -/
theorem approximationError_eq_zero_of_subset (K : Set X) (V : Submodule ℝ X)
    (hKV : K ⊆ (V : Set X)) : approximationError K V = 0 := by
  unfold approximationError
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [Metric.infEDist_zero_of_mem (hKV x.2)]
  · exact bot_le

/-- Any finite-dimensional subspace containing `K` witnesses zero width at
every dimension bound that admits that subspace. -/
theorem kolmogorovWidth_eq_zero_of_subset (K : Set X) (V : Submodule ℝ X)
    (m : ℕ) (hV : Module.rank ℝ V ≤ (m : Cardinal))
    (hKV : K ⊆ (V : Set X)) : kolmogorovWidth K m = 0 := by
  apply le_antisymm
  · change (⨅ W : {W : Submodule ℝ X //
      Module.rank ℝ W ≤ (m : Cardinal)}, approximationError K W.1) ≤ 0
    rw [← approximationError_eq_zero_of_subset K V hKV]
    exact iInf_le (fun W : {W : Submodule ℝ X //
      Module.rank ℝ W ≤ (m : Cardinal)} => approximationError K W.1) ⟨V, hV⟩
  · exact bot_le

/-- The zero-dimensional approximating subspace gives zero width for a set
contained in the origin. -/
theorem kolmogorovWidth_eq_zero_of_subset_zero (K : Set X)
    (hK : K ⊆ ({0} : Set X)) : kolmogorovWidth K 0 = 0 := by
  apply kolmogorovWidth_eq_zero_of_subset K ⊥ 0 ?_ ?_
  · simp
  · intro x hx
    rcases hK hx with rfl
    exact (Submodule.zero_mem (⊥ : Submodule ℝ X))

/-- Bounded sets have finite worst-case approximation error, because every
linear subspace contains zero and the distance to it is at most `‖x‖`. -/
theorem approximationError_ne_top_of_isBounded (K : Set X) (V : Submodule ℝ X)
    (hK : Bornology.IsBounded K) : approximationError K V ≠ ⊤ := by
  obtain ⟨C, hC0, hC⟩ :=
    (Metric.isBounded_iff_exists_ge (s := insert (0 : X) K) 0).mp (hK.insert 0)
  have hle : approximationError K V ≤ ENNReal.ofReal C := by
    unfold approximationError
    apply iSup_le
    intro x
    have hxK : (x : X) ∈ K := x.property
    have hx' : (x : X) ∈ insert (0 : X) K := Set.mem_insert_of_mem (0 : X) hxK
    have hzero : (0 : X) ∈ insert (0 : X) K := Set.mem_insert _ _
    calc
      Metric.infEDist x.1 (V : Set X) ≤ edist x.1 (0 : X) :=
        Metric.infEDist_le_edist_of_mem (V.zero_mem)
      _ = ENNReal.ofReal (dist x.1 (0 : X)) := edist_dist x.1 (0 : X)
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal
          (hC hx' hzero)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Compact sets have finite worst-case approximation error. -/
theorem approximationError_ne_top_of_isCompact (K : Set X) (V : Submodule ℝ X)
    (hK : IsCompact K) : approximationError K V ≠ ⊤ :=
  approximationError_ne_top_of_isBounded K V hK.isBounded

end HaarQuarter.TheoremD.Width


/-!
Real-valued interface for the extended-real Kolmogorov width in
`KolmogorovWidth.lean`. This interface is intended to connect the width
monotonicity lemma to the real-valued numerical extraction.
-/

namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The ordinary real-valued width, defined by the extended width's canonical
real part. Under boundedness this is finite and agrees with the usual
real-valued infimum formula. -/
noncomputable def kolmogorovWidthReal (K : Set X) (m : ℕ) : ℝ :=
  (kolmogorovWidth K m).toReal

/-- Boundedness makes every extended width finite, by comparison with the
zero subspace. -/
theorem kolmogorovWidth_ne_top_of_isBounded (K : Set X) (m : ℕ)
    (hK : Bornology.IsBounded K) : kolmogorovWidth K m ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (approximationError_ne_top_of_isBounded K ⊥ hK)
  unfold kolmogorovWidth
  exact iInf_le (fun V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)} =>
    approximationError K V.1) ⟨⊥, by simp⟩

/-- The real-valued width is nonincreasing in the allowed dimension. -/
theorem kolmogorovWidthReal_antitone (K : Set X) (hK : Bornology.IsBounded K)
    {m n : ℕ} (hmn : m ≤ n) :
    kolmogorovWidthReal K n ≤ kolmogorovWidthReal K m := by
  unfold kolmogorovWidthReal
  apply ENNReal.toReal_mono (kolmogorovWidth_ne_top_of_isBounded K m hK)
  exact kolmogorovWidth_antitone K hmn

/-- At dimension zero, the only admissible linear subspace is `{0}`, so the
width is exactly the worst-case distance to the zero subspace. -/
theorem kolmogorovWidth_zero_eq_bot (K : Set X) :
    kolmogorovWidth K 0 = approximationError K ⊥ := by
  unfold kolmogorovWidth
  apply le_antisymm
  · exact iInf_le (fun V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (0 : Cardinal)} =>
      approximationError K V.1) ⟨⊥, by simp⟩
  · apply le_iInf
    intro V
    have hrank : Module.rank ℝ V.1 = 0 := by
      exact le_antisymm V.2 zero_le
    have hsub : Subsingleton V.1 := rank_zero_iff.mp hrank
    have hV : V.1 = (⊥ : Submodule ℝ X) := by
      apply le_antisymm
      · intro x hx
        change x = 0
        have hx' : (⟨x, hx⟩ : V.1) = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val hx'
      · exact bot_le
    rw [hV]

/-- The same zero-dimensional identity holds for the real-valued interface. -/
theorem kolmogorovWidthReal_zero_eq_bot (K : Set X)
    (_hK : Bornology.IsBounded K) :
    kolmogorovWidthReal K 0 = (approximationError K ⊥).toReal := by
  simp [kolmogorovWidthReal, kolmogorovWidth_zero_eq_bot]

end HaarQuarter.TheoremD.Width


namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The bounded-set real interface is exactly the manuscript's real
infimum-supremum-infimum norm formula, with the finite dimension restriction
represented by its cardinal-rank bound. -/
theorem kolmogorovWidthReal_eq_norm_formula (K : Set X)
    (hK : Bornology.IsBounded K) (m : ℕ) :
    kolmogorovWidthReal K m =
      ⨅ V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)},
        ⨆ x : {x : X // x ∈ K}, ⨅ v : V.1, ‖x.val - v.val‖ := by
  unfold kolmogorovWidthReal kolmogorovWidth
  rw [ENNReal.toReal_iInf (fun V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)} =>
    approximationError_ne_top_of_isBounded K V.1 hK)]
  congr 1
  funext V
  unfold approximationError
  rw [ENNReal.toReal_iSup]
  · congr 1
    funext x
    change Metric.infDist x.val (V.1 : Set X) = _
    rw [Metric.infDist_eq_iInf]
    simp only [dist_eq_norm]
    congr 1
  · intro x
    exact Metric.infEDist_ne_top ⟨0, V.1.zero_mem⟩

end HaarQuarter.TheoremD.Width
