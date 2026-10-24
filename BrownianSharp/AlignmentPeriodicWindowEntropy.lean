import BrownianSharp.AlignmentPeriodicCubeRestriction
import BrownianSharp.AlignmentInverseLipschitzEntropy
import Mathlib.Tactic

/-! Positive continuous window multipliers preserve the lower entropy rate
when periodic classes are represented on the fundamental cube. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPeriodicWindowEntropy
open Torus AlignmentPeriodicCubeRestriction AlignmentInverseLipschitzEntropy

def weightedCubeRestriction {d : ℕ} (g : C(BrownianCubeAnchor d,ℝ))
    (f : RealPeriodic d) : C(BrownianCubeAnchor d,ℝ) :=
  g * periodicCubeRestriction d f

theorem weightedCubeRestriction_inverse_norm {d : ℕ}
    (g : C(BrownianCubeAnchor d,ℝ)) (c : ℝ) (hc : 0 < c)
    (hg : ∀ t, c ≤ ‖g t‖) (f : RealPeriodic d) :
    ‖f‖ ≤ c⁻¹ * ‖weightedCubeRestriction g f‖ := by
  have hb : ‖periodicCubeRestriction d f‖ ≤ ‖weightedCubeRestriction g f‖ / c := by
    apply (ContinuousMap.norm_le _ (div_nonneg (norm_nonneg _) hc.le)).2
    intro t
    apply (le_div_iff₀ hc).2
    calc
      ‖periodicCubeRestriction d f t‖ * c =
          c * ‖periodicCubeRestriction d f t‖ := by ring
      _ ≤ ‖g t‖ * ‖periodicCubeRestriction d f t‖ :=
        mul_le_mul_of_nonneg_right (hg t) (norm_nonneg _)
      _ = ‖weightedCubeRestriction g f t‖ := by
        simp only [weightedCubeRestriction, ContinuousMap.mul_apply, norm_mul]
      _ ≤ ‖weightedCubeRestriction g f‖ := (weightedCubeRestriction g f).norm_coe_le_norm t
  rw [periodicCubeRestriction_norm] at hb
  simpa only [div_eq_mul_inv, mul_comm] using hb

theorem weightedCubeRestriction_inverse_distance {d : ℕ}
    (g : C(BrownianCubeAnchor d,ℝ)) (c : ℝ) (hc : 0 < c)
    (hg : ∀ t, c ≤ ‖g t‖) (f₁ f₂ : RealPeriodic d) :
    dist f₁ f₂ ≤ c⁻¹ * dist (weightedCubeRestriction g f₁) (weightedCubeRestriction g f₂) := by
  have hn := weightedCubeRestriction_inverse_norm g c hc hg (f₁-f₂)
  simpa only [dist_eq_norm, weightedCubeRestriction, map_sub, mul_sub] using hn

theorem weightedCubeRestriction_injective {d : ℕ}
    (g : C(BrownianCubeAnchor d,ℝ)) (c : ℝ) (hc : 0 < c)
    (hg : ∀ t, c ≤ ‖g t‖) : Function.Injective (weightedCubeRestriction g) := by
  intro f₁ f₂ heq
  have hd := weightedCubeRestriction_inverse_distance g c hc hg f₁ f₂
  rw [heq, dist_self, mul_zero] at hd
  exact dist_le_zero.mp hd

theorem weightedCubeRestriction_entropy_lower {d : ℕ}
    (g : C(BrownianCubeAnchor d,ℝ)) (c : ℝ) (hc : 0 < c)
    (hg : ∀ t, c ≤ ‖g t‖) (K : Set (RealPeriodic d)) (k : ℕ) (E : ℝ)
    (hE : ENNReal.ofReal E ≤ HaarQuarter.TheoremD.entropyNumber k K) :
    ENNReal.ofReal (c*E/2) ≤
      HaarQuarter.TheoremD.entropyNumber k (weightedCubeRestriction g '' K) := by
  let L : ℝ≥0 := Real.toNNReal c⁻¹
  have hLc : (L:ℝ) = c⁻¹ := Real.coe_toNNReal _ (inv_pos.mpr hc).le
  have hLpos : 0 < L := Real.toNNReal_pos.mpr (inv_pos.mpr hc)
  have hdist : ∀ x y, dist x y ≤ (L:ℝ) *
      dist (weightedCubeRestriction g x) (weightedCubeRestriction g y) := by
    intro x y
    rw [hLc]
    exact weightedCubeRestriction_inverse_distance g c hc hg x y
  have h := entropy_lower_of_inverse_distance (weightedCubeRestriction g)
    (weightedCubeRestriction_injective g c hc hg) L hLpos hdist K k E hE
  have he : E/(2*(L:ℝ)) = c*E/2 := by rw [hLc]; field_simp
  simpa only [he] using h

end BrownianSharp.AlignmentPeriodicWindowEntropy
