import BrownianSharp.AlignmentPeriodicWidth
import BrownianSharp.AlignmentIsometricEntropy
import BrownianSharp.AlignmentLatestStatements

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentIsometricEntropy
open BrownianSharp.AlignmentPeriodicWidth

theorem logarithmicIndexRate_nonneg (s a : ℝ) (n : ℕ) :
    0≤logarithmicIndexRate s a n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)

theorem logarithmicIndexRate_pos (s a : ℝ) {n : ℕ} (hn : 2≤n) :
    0<logarithmicIndexRate s a n := by
  unfold logarithmicIndexRate
  have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (Real.log_pos hnR) _)

/-- The sharp Carl consequence at any positive power and nonnegative
logarithmic exponent, including eventual entropy and upper-width inputs. -/
theorem twoSidedWidthRate_of_entropy_lower_and_width_upper
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (s a R : ℝ) (hs : 0<s) (ha : 0≤a) (hR : 0≤R)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hEntropy : ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n, n₀≤n →
      ENNReal.ofReal (c*logarithmicIndexRate s a n) ≤
        HaarQuarter.TheoremD.entropyNumber n K)
    (hUpper : ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n, n₀≤n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth K n ≤
        ENNReal.ofReal (C*logarithmicIndexRate s a n)) :
    Latest.twoSidedWidthRate K s a := by
  obtain ⟨c,hc,nE,hE⟩ := hEntropy
  obtain ⟨c₀,hc₀,hE₀⟩ := entropy_lower_uniformize K (logarithmicIndexRate s a)
    (logarithmicIndexRate_nonneg s a) (fun n hn => logarithmicIndexRate_pos s a hn)
    c hc nE hE
  obtain ⟨C,hC,nU,hU⟩ := hUpper
  let A := ⌈s⌉₊+1
  let q := A+1
  have hsA : s<(A:ℝ) := by
    have hceil : s≤(⌈s⌉₊:ℝ) := Nat.le_ceil s
    dsimp [A]
    push_cast
    linarith
  have hAq : A+1≤3*q := by dsimp [q]; omega
  obtain ⟨c',M,hc',hLower⟩ :=
    eventually_width_lower_of_entropy_rate_upper_A K hs ha hsA hAq
      (le_max_left 2 nU) hR hC hc₀ hzero
      (fun n hn => by
        simpa only [rate,logarithmicIndexRate] using hU n ((le_max_right 2 nU).trans hn))
      (fun n hn => by simpa only [rate,logarithmicIndexRate] using hE₀ n hn)
  refine ⟨c',C,hc',hC,max 2 (max M nU),le_max_left _ _,?_⟩
  intro n hn
  have hnM : M≤n := (le_max_left M nU).trans ((le_max_right 2 (max M nU)).trans hn)
  have hnU : nU≤n := (le_max_right M nU).trans ((le_max_right 2 (max M nU)).trans hn)
  exact ⟨by simpa only [rate,logarithmicIndexRate] using hLower n hnM,hU n hnU⟩

end BrownianSharp.AlignmentWidthRates
