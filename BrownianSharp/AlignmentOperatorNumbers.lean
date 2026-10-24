import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.KolmogorovWidth

/-! Bridges between set widths in the certificate and the strict-dimension
operator Kolmogorov numbers used by the revised manuscript. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentOperatorNumbers

open HaarQuarter.TheoremD.Width

/-- Operator Kolmogorov number for a set of outputs. The strict rank
constraint is the manuscript's `dim V < k` convention. -/
def operatorKolmogorovNumber {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (k : ℕ) : ℝ≥0∞ :=
  ⨅ V : {V : Submodule ℝ X // Module.rank ℝ V < (k : Cardinal)},
    approximationError K V.1

/-- Strict operator index `k` is exactly the set width with allowed
dimension `k-1`. The hypothesis `1≤k` excludes the manuscript's zero index. -/
theorem operatorKolmogorovNumber_eq_width_pred
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) {k : ℕ} (hk : 1 ≤ k) :
    operatorKolmogorovNumber K k = kolmogorovWidth K (k-1) := by
  classical
  unfold operatorKolmogorovNumber kolmogorovWidth
  apply le_antisymm
  · apply le_iInf
    intro V
    have hcast : ((k-1 : ℕ) : Cardinal) + 1 = (k : Cardinal) := by
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      exact_mod_cast hk'
    have hrank : Module.rank ℝ V.1 < (k : Cardinal) := by
      rw [← hcast]
      rw [Cardinal.lt_natCast_add_one_iff]
      exact V.2
    exact iInf_le (fun W : {W : Submodule ℝ X // Module.rank ℝ W < (k : Cardinal)} =>
      approximationError K W.1) ⟨V.1, hrank⟩
  · apply le_iInf
    intro V
    have hcast : ((k-1 : ℕ) : Cardinal) + 1 = (k : Cardinal) := by
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      exact_mod_cast hk'
    have hrank : Module.rank ℝ V.1 ≤ ((k-1 : ℕ) : Cardinal) := by
      apply Cardinal.lt_natCast_add_one_iff.mp
      rw [hcast]
      exact V.2
    exact iInf_le (fun W : {W : Submodule ℝ X //
      Module.rank ℝ W ≤ ((k-1 : ℕ) : Cardinal)} => approximationError K W.1)
      ⟨V.1, hrank⟩

end BrownianSharp.AlignmentOperatorNumbers
