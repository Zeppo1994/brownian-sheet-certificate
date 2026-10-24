import BrownianSharp.CameronMartinDictionaryError
import BrownianSharp.GaussianDictionaryApproximation
import BrownianSharp.DKLLWidthRateExtraction

/-! Unconditional sharp upper widths for the actual restricted-cube
Cameron–Martin integration unit ball. -/
noncomputable section
namespace BrownianSharp

/-- Finite Gaussian dictionary approximation, exact mixed Haar grid expansion,
sharp layer energies and positive sampling extension give the dyadic DKLL
upper bound with no external approximation hypothesis. -/
theorem cameronMartinDyadicWidthUpper_certified {d : ℕ} (hd : 2≤d) :
    ∃ B : ℝ,0<B ∧ ∀ n : ℕ,2≤n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d)
        (4*Fintype.card (LayerIndex d n))≤
      ENNReal.ofReal (B*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n) := by
  exact KdUnitCube_dyadic_width_of_finite_dictionary hd
    GaussianRIP.finDictionaryApproximation_gaussian (by norm_num : (0:ℝ)≤10000)
    (dyadicHaarDictionaryRateConstant_pos 10000 d)
    (fun n hn => dyadicHaarDictionaryErrorSum_le hd hn 10000 (by norm_num))

/-- The full sharp upper width rate holds at every sufficiently large index,
with constants depending only on the dimension. -/
theorem cameronMartinSharpWidthUpper_certified {d : ℕ} (hd : 2≤d) :
    ∃ C : ℝ,0<C ∧ ∃ m₀ : ℕ,2≤m₀ ∧ ∀ m : ℕ,m₀≤m →
      HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) m≤
        ENNReal.ofReal (C*cmIndexRate d m) := by
  obtain ⟨B,hB,hdyadic⟩ := cameronMartinDyadicWidthUpper_certified hd
  obtain ⟨C,hC,m₀,hm₀,hall⟩ :=
    DKLLWidthRateExtraction.all_index_width_rate_of_dyadic_layer_bound hd
      (CameronMartin.KdUnitCube d) B hB 2 hdyadic
  exact ⟨C,hC,m₀,by omega,hall⟩

end BrownianSharp
