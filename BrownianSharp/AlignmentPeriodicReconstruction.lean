import BrownianSharp.AlignmentPeriodicEnergy
import BrownianSharp.NativeLayerThetaBudget
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentPeriodicReconstruction
open SmoothResolution Torus

theorem frequencyBox_card_le {d : ℕ} (s : Fin d → ℕ) :
    (frequencyBox s).card ≤ 5^d * 2^(∑ i, s i) := by
  classical
  unfold frequencyBox
  rw [Fintype.card_piFinset]
  have hb : ∀ i, (Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1))).card ≤
      5*2^(s i) := by
    intro i
    have hi := Int.card_Icc_of_le (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1)) (by
      have hp : 0 ≤ (2:ℤ)^(s i+1) := by positivity
      omega)
    have hpow : (1:ℕ) ≤ 2^(s i) := one_le_pow₀ (by norm_num)
    have heq : (Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1))).card =
        4*2^(s i)+1 := by
      have hz : ((Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1))).card : ℤ) =
          4*(2:ℤ)^(s i)+1 := by
        rw [hi, pow_succ]
        ring
      exact_mod_cast hz
    rw [heq]
    omega
  calc
    (∏ i, (Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1))).card) ≤
        ∏ i, 5*2^(s i) := Finset.prod_le_prod' fun i hi => hb i
    _ = 5^d * 2^(∑ i, s i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

theorem frequencyBox_card_real_le {d : ℕ} (s : Fin d → ℕ) :
    ((frequencyBox s).card : ℝ) ≤ (5:ℝ)^d * (2:ℝ)^(∑ i, s i) := by
  exact_mod_cast frequencyBox_card_le s

/-- Coordinatewise geometric decay is summable over every dyadic shape. -/
theorem summable_shape_geometric (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun s : Fin d → ℕ => q^(∑ i, s i)) := by
  let a : ℝ≥0 := ⟨q,hq0⟩
  let f : (Fin d → ℕ) → ℝ≥0 := fun s => ∏ i, a^(s i)
  have hfinite : (∑' s, (f s : ENNReal)) ≠ ⊤ := by
    change (∑' s : Fin d → ℕ, ((∏ i, a^(s i) : ℝ≥0) : ENNReal)) ≠ ⊤
    push_cast
    rw [NativeLayerThetaBudget.ennreal_tsum_pi_prod d (fun _ n => (a:ENNReal)^n)]
    apply ENNReal.prod_ne_top
    intro i hi
    exact (tsum_geometric_lt_top.mpr (by exact_mod_cast hq1)).ne
  have h := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hfinite
  have heq : (fun s : Fin d → ℕ => (f s : ℝ)) = (fun s => q^(∑ i,s i)) := by
    funext s
    dsimp [f]
    rw [Finset.prod_pow_eq_pow_sum]
    exact NNReal.coe_pow a _
  rw [heq] at h
  exact h

theorem block_toLp_norm {d : ℕ} (s : Fin d → ℕ) (f : RealPeriodic d) :
    ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖ =
      (eLpNorm (block s f) 2 (volume : Measure (UnitAddTorus (Fin d)))).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _)]

theorem nikolsky_two_block_L2_bound {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) (r : ℝ) (hf : NikolskyUnitBall 2 r f) :
    ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖ ≤
      (2:ℝ)^(-r * ∑ i, (s i : ℝ)) := by
  have hb := hf s
  have ht := ENNReal.toReal_mono (by simp : (1:ENNReal)≠⊤) hb
  unfold weightedBlockNorm at ht
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_one] at ht
  rw [block_toLp_norm]
  have hw : 0 < (2:ℝ)^(r*∑ i,(s i:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hn : (eLpNorm (block s f) 2 (volume : Measure (UnitAddTorus (Fin d)))).toReal ≤
      1/((2:ℝ)^(r*∑ i,(s i:ℝ))) := by
    apply (le_div_iff₀ hw).2
    nlinarith
  convert hn using 1
  rw [one_div, ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

theorem smoothBlock_global_sup_le_sqrt_card_L2 {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) :
    ‖block s f‖ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
      ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖ := by
  have h := AlignmentTrigonometricL2.smoothBlock_sup_le_sqrt_card_L2 s f
  change ‖block s f‖ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
    ‖(block s f).toLp 2 (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ℂ‖ at h
  have hn : ‖(block s f).toLp 2 (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ℂ‖ =
      (eLpNorm (block s f) 2 (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _)]
  rw [hn] at h
  rw [block_toLp_norm]
  simpa only [unitAddTorus_volume_eq_productHaar] using h

theorem sqrt_dyadic_weight_identity (d n : ℕ) (r : ℝ) :
    Real.sqrt ((5:ℝ)^d * (2:ℝ)^n) * (2:ℝ)^(-r*(n:ℝ)) =
      Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^n := by
  have hsq : Real.sqrt ((2:ℝ)^n) = (2:ℝ)^((n:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hpow : ((2:ℝ)^(1/2-r))^n = (2:ℝ)^((1/2-r)*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  rw [Real.sqrt_mul (by positivity), hsq, hpow, mul_assoc,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 2
  ring

theorem nikolsky_two_block_sup_bound {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) (r : ℝ) (hf : NikolskyUnitBall 2 r f) :
    ‖block s f‖ ≤ Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^(∑ i,s i) := by
  calc
    ‖block s f‖ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
        ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖ :=
      smoothBlock_global_sup_le_sqrt_card_L2 s f
    _ ≤ Real.sqrt ((5:ℝ)^d * (2:ℝ)^(∑ i,s i)) *
        (2:ℝ)^(-r*∑ i,(s i:ℝ)) := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt (frequencyBox_card_real_le s)
      · exact nikolsky_two_block_L2_bound s f r hf
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      rw [← Nat.cast_sum]
      exact sqrt_dyadic_weight_identity d _ r

/-- The actual smooth Fourier blocks are uniformly absolutely summable for
r>1/2 throughout the literal Nikolsky-2 ball. -/
theorem nikolsky_two_blocks_summable {d : ℕ} (r : ℝ) (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f) :
    Summable (fun s : Fin d → ℕ => block s f) := by
  have hq0 : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hs := (summable_shape_geometric d hq0 hq1).mul_left (Real.sqrt ((5:ℝ)^d))
  exact Summable.of_norm_bounded hs (fun s => nikolsky_two_block_sup_bound s f r hf)

end BrownianSharp.AlignmentPeriodicReconstruction
