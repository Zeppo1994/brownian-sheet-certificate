import BrownianSharp.SmoothGaussianLp
import BrownianSharp.SmoothClassMeasurability
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Higher Sobolev moments are reduced to countable Minkowski for the
nonnegative block-square series. The only stochastic input is the actual
scalar Gaussian block moment at each spatial point. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover

local instance instSmoothSobolevHigherMeasureSpace : MeasureSpace UnitAddCircle :=
  AddCircle.measureSpace 1
local instance instSmoothSobolevHigherCircleVolume :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)

theorem eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) {q : ℝ} (hq : 0 < q)
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (ENNReal.ofReal q) μ) ^ q =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ := by
  have hq0 : 0 ≤ q := le_of_lt hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    ((ENNReal.ofReal_pos.mpr hq).ne') (by simp) hf]
  rw [ENNReal.toReal_ofReal hq0]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]

/-- Countable Minkowski for a nonnegative series of real functions. This
finite-to-countable step follows the Fatou/liminf proof used by Mathlib's
`lintegral_rpow_tsum_coe_enorm_sub_le_tsum` in
`MeasureTheory/Function/LpSpace/Complete.lean`. -/
theorem lintegral_tsum_ofReal_rpow_le_of_lsum_eLpNorm
    {ι α : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}
    (e : ℕ ≃ ι) (f : ι → α → ℝ) {q : ℝ} (hq1 : 1 ≤ q)
    (hmeas : ∀ i, Measurable (f i))
    (hnonneg : ∀ i x, 0 ≤ f i x)
    {B : ℝ≥0∞}
    (hsum : (∑' i, eLpNorm (f i) (ENNReal.ofReal q) μ) ≤ B) :
    (∫⁻ x, (∑' i, ENNReal.ofReal (f i x)) ^ q ∂μ) ≤ B ^ q := by
  classical
  let g : ℕ → α → ℝ := fun n => f (e n)
  let A : ℕ → α → ℝ≥0∞ := fun n x =>
    ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (g i x)
  have hsumNat : (∑' n, eLpNorm (g n) (ENNReal.ofReal q) μ) ≤ B := by
    calc
      (∑' n, eLpNorm (g n) (ENNReal.ofReal q) μ) =
          ∑' i, eLpNorm (f i) (ENNReal.ofReal q) μ := by
            rw [← e.tsum_eq]
      _ ≤ B := hsum
  have hAmeas (n : ℕ) : AEMeasurable (A n) μ := by
    dsimp [A, g]
    exact ((Finset.range (n + 1)).aemeasurable_fun_sum fun i hi =>
      (hmeas (e i)).ennreal_ofReal.aemeasurable)
  have hA_limit (x : α) :
      (∑' i, ENNReal.ofReal (g i x)) = Filter.liminf (fun n => A n x) atTop := by
    rw [ENNReal.tsum_eq_liminf_sum_nat, ← Filter.liminf_nat_add _ 1]
  have hfinite (n : ℕ) :
      (∫⁻ x, (A n x) ^ q ∂μ) ≤ B ^ q := by
    let u : α → ℝ := fun x => ∑ i ∈ Finset.range (n + 1), g i x
    have hu_nonneg (x : α) : 0 ≤ u x := by
      dsimp [u]
      exact Finset.sum_nonneg fun i hi => hnonneg (e i) x
    have hAeq (x : α) : A n x = ENNReal.ofReal (u x) := by
      dsimp [A, g, u]
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact hnonneg (e i) x
    have huMeas : Measurable u := by
      dsimp [u]
      exact (Finset.range (n + 1)).measurable_fun_sum fun i hi => hmeas (e i)
    have huLp : AEStronglyMeasurable u μ := huMeas.aestronglyMeasurable
    have hq1' : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq1
    have htriangle : eLpNorm u (ENNReal.ofReal q) μ ≤
        ∑ i ∈ Finset.range (n + 1), eLpNorm (g i) (ENNReal.ofReal q) μ := by
      rw [show u = ∑ i ∈ Finset.range (n + 1), (fun x => g i x) by
        funext x
        simp [u]]
      exact eLpNorm_sum_le (p := ENNReal.ofReal q)
        (f := fun i x => g i x) (s := Finset.range (n + 1)) hq1'
    have hpartial : (∑ i ∈ Finset.range (n + 1),
        eLpNorm (g i) (ENNReal.ofReal q) μ) ≤ B :=
      (ENNReal.sum_le_tsum _).trans hsumNat
    have hnorm : eLpNorm u (ENNReal.ofReal q) μ ≤ B := htriangle.trans hpartial
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
    have hmoment := eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow u hqpos huLp
    have hA_pow (x : α) : (A n x) ^ q = ENNReal.ofReal (‖u x‖ ^ q) := by
      rw [hAeq x, ENNReal.ofReal_rpow_of_nonneg (hu_nonneg x) (le_of_lt hqpos)]
      congr 2
      rw [Real.norm_of_nonneg (hu_nonneg x)]
    rw [show (fun x => (A n x) ^ q) = fun x => ENNReal.ofReal (‖u x‖ ^ q) by
      funext x
      exact hA_pow x]
    rw [← hmoment]
    exact ENNReal.rpow_le_rpow hnorm (by positivity)
  have hpow_liminf (x : α) :
      (Filter.liminf (fun n => A n x) atTop) ^ q =
        Filter.liminf (fun n => (A n x) ^ q) atTop := by
    have hm := ENNReal.strictMono_rpow_of_pos (lt_of_lt_of_le zero_lt_one hq1)
    have hs := (ENNReal.rpow_left_bijective
      (lt_of_lt_of_le zero_lt_one hq1).ne.symm).2
    exact (hm.orderIsoOfSurjective _ hs).liminf_apply
      (by isBoundedDefault) (by isBoundedDefault)
      (by isBoundedDefault) (by isBoundedDefault)
  calc
    (∫⁻ x, (∑' i, ENNReal.ofReal (f i x)) ^ q ∂μ)
        = ∫⁻ x, (Filter.liminf (fun n => A n x) atTop) ^ q ∂μ := by
            apply lintegral_congr
            intro x
            rw [← e.tsum_eq (fun i => ENNReal.ofReal (f i x)), hA_limit]
    _ = ∫⁻ x, Filter.liminf (fun n => (A n x) ^ q) atTop ∂μ := by
          apply lintegral_congr
          intro x
          exact hpow_liminf x
    _ ≤ Filter.liminf (fun n => ∫⁻ x, (A n x) ^ q ∂μ) atTop :=
          lintegral_liminf_le' (fun n => (hAmeas n).pow_const q)
    _ ≤ B ^ q := by
          refine liminf_le_of_frequently_le' ?_
          exact Filter.Frequently.of_forall hfinite

private theorem smoothBlock_square_eLpNorm_le {d ι : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (x : UnitAddTorus (Fin d)) {p : ℝ} (hp2 : 2 ≤ p)
    (V : ℝ) (hV : 0 ≤ V)
    (hvariance : (∑ i : Fin ι,
      ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V)
    (w : ℝ) (hw : 0 ≤ w) :
    eLpNorm (fun z : Fin ι → ℝ => w *
      ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ 2)
      (ENNReal.ofReal (p / 2)) (productStandardGaussian (Fin ι)) ≤
        ENNReal.ofReal (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) := by
  classical
  let P : Measure (Fin ι → ℝ) := productStandardGaussian (Fin ι)
  let b : (Fin ι → ℝ) → ℝ := fun z =>
    ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖
  let f : (Fin ι → ℝ) → ℝ := fun z => w * b z ^ 2
  let q : ℝ := p / 2
  have hp : 1 ≤ p := by linarith
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := by linarith
  have hdata := smoothBlock_gaussian_absRpow_data s atoms x hp
  have hbInt : Integrable (fun z => b z ^ p) P := by
    simpa [P, b] using hdata.1
  have hbMean : (∫ z, b z ^ p ∂P) ≤
      2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p := by
    have h := hdata.2
    have hmono :
        (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ^ (p / 2) ≤
          V ^ (p / 2) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact hvariance
      · linarith
    calc
      (∫ z, b z ^ p ∂P) ≤
          2 ^ p *
            (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ^ (p / 2) *
              gaussianAbsoluteMoment p := by simpa [P, b] using h
      _ ≤ 2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmono (by positivity)) (by
            unfold gaussianAbsoluteMoment
            exact integral_nonneg fun _ => by positivity)
  have hqENN : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hqENNtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hfMeas : AEStronglyMeasurable f P := by
    have hm : Measurable f := by
      have hrepr : f = fun z => w * ‖∑ i : Fin ι,
          (z i : ℂ) * SmoothResolution.block s (atoms i) x‖ ^ 2 := by
        funext z
        dsimp [f, b]
        rw [AtomicBlockVariance.smoothBlock_gaussianSynthesis]
      rw [hrepr]
      fun_prop
    exact hm.aestronglyMeasurable
  have hformula := eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow f hqpos hfMeas
  have hweightedInt : Integrable (fun z => w ^ q * b z ^ p) P :=
    hbInt.const_mul (w ^ q)
  have hweightedNN : ∀ᵐ z ∂P, 0 ≤ w ^ q * b z ^ p :=
    Filter.Eventually.of_forall fun z => mul_nonneg (Real.rpow_nonneg hw _) (by positivity)
  have hweightedL : (∫⁻ z, ENNReal.ofReal (w ^ q * b z ^ p) ∂P) =
      ENNReal.ofReal (∫ z, w ^ q * b z ^ p ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hweightedInt hweightedNN).symm
  have hpoint (z : Fin ι → ℝ) :
      ‖f z‖ ^ q = w ^ q * b z ^ p := by
    dsimp [f, b, q]
    rw [abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    rw [Real.mul_rpow hw (sq_nonneg _)]
    rw [show (‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ 2) =
      ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ (2 : ℝ) by
        rw [← Real.rpow_natCast]
        norm_num]
    rw [← Real.rpow_mul (norm_nonneg _)]
    rw [show (2 : ℝ) * (p / 2) = p by ring]
  have hlintegral :
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ q) ∂P) =
        ENNReal.ofReal (w ^ q * ∫ z, b z ^ p ∂P) := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal (w ^ q * b z ^ p) ∂P := by
        apply lintegral_congr
        intro z
        rw [hpoint z]
      _ = ENNReal.ofReal (∫ z, w ^ q * b z ^ p ∂P) := hweightedL
      _ = ENNReal.ofReal (w ^ q * ∫ z, b z ^ p ∂P) := by
        rw [integral_const_mul]
  have hmomentNonneg : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have hconstNonneg : 0 ≤ w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p)) := by
    positivity
  have hrealBound : w ^ q * (∫ z, b z ^ p ∂P) ≤
      (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := by
    have hexp : (2 / p) * q = 1 := by dsimp [q]; field_simp
    have hfour : (4 : ℝ) ^ q = (2 : ℝ) ^ p := by
      calc
        (4 : ℝ) ^ q = ((2 : ℝ) ^ (2 : ℝ)) ^ q :=
          congrArg (fun y : ℝ => y ^ q) (by norm_num : (4 : ℝ) = 2 ^ (2 : ℝ))
        _ = (2 : ℝ) ^ (2 * q) := (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 2 q).symm
        _ = (2 : ℝ) ^ p := by rw [show (2 : ℝ) * q = p by dsimp [q]; ring]
    have hMeq : (gaussianAbsoluteMoment p ^ (2 / p)) ^ q =
        gaussianAbsoluteMoment p := by
      rw [← Real.rpow_mul hmomentNonneg, hexp, Real.rpow_one]
    have hthree : (4 * V * gaussianAbsoluteMoment p ^ (2 / p)) ^ q =
        4 ^ q * V ^ q * (gaussianAbsoluteMoment p ^ (2 / p)) ^ q := by
      calc
        (4 * V * gaussianAbsoluteMoment p ^ (2 / p)) ^ q =
            ((4 * V) * gaussianAbsoluteMoment p ^ (2 / p)) ^ q := by congr 1 <;> ring
        _ = (4 * V) ^ q * (gaussianAbsoluteMoment p ^ (2 / p)) ^ q :=
          Real.mul_rpow (mul_nonneg (by positivity : 0 ≤ (4 : ℝ)) hV)
            (Real.rpow_nonneg hmomentNonneg _)
        _ = (4 ^ q * V ^ q) * (gaussianAbsoluteMoment p ^ (2 / p)) ^ q := by
          rw [Real.mul_rpow (by positivity : 0 ≤ (4 : ℝ)) hV]
        _ = 4 ^ q * V ^ q * (gaussianAbsoluteMoment p ^ (2 / p)) ^ q := by ring
    have hscale : w ^ q * (2 ^ p * V ^ q * gaussianAbsoluteMoment p) =
        (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := by
      calc
        w ^ q * (2 ^ p * V ^ q * gaussianAbsoluteMoment p) =
            w ^ q * ((4 : ℝ) ^ q * V ^ q *
              (gaussianAbsoluteMoment p ^ (2 / p)) ^ q) := by
                rw [hfour, hMeq]
        _ = (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := by
          rw [Real.mul_rpow hw (by positivity), hthree]
    calc
      w ^ q * (∫ z, b z ^ p ∂P) ≤
          w ^ q * (2 ^ p * V ^ q * gaussianAbsoluteMoment p) := by
        have hqrewrite : q = p / 2 := by rfl
        calc
          _ ≤ w ^ q * (2 ^ p * V ^ (p / 2) * gaussianAbsoluteMoment p) :=
            mul_le_mul_of_nonneg_left hbMean (Real.rpow_nonneg hw _)
          _ = _ := by rw [hqrewrite]
      _ = (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := hscale
  have hlinBound :
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ q) ∂P) ≤
        ENNReal.ofReal (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := by
    rw [hlintegral, ENNReal.ofReal_rpow_of_nonneg hconstNonneg hqpos.le]
    exact ENNReal.ofReal_le_ofReal hrealBound
  have hnormq : (eLpNorm f (ENNReal.ofReal q) P) ^ q ≤
      ENNReal.ofReal (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) ^ q := by
    rw [hformula]
    exact hlinBound
  have hmono := ENNReal.strictMono_rpow_of_pos hqpos
  by_contra hnot
  have hlt : ENNReal.ofReal (w * (4 * V * gaussianAbsoluteMoment p ^ (2 / p))) <
      eLpNorm f (ENNReal.ofReal q) P := lt_of_not_ge hnot
  have hpowlt := hmono hlt
  exact (not_lt_of_ge hnormq) hpowlt

/-- Higher moments of the actual literal smooth square function follow from
the block Gaussian moments and countable Minkowski. The countable indexing
equivalence is explicit so callers can supply the standard enumeration of
the dyadic scale lattice. -/
theorem smoothSobolev_higherP_expected_energy_le {d ι : ℕ}
    (p r : ℝ) (hp2 : 2 ≤ p)
    (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    (e : ℕ ≃ (Fin d → ℕ)) {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ, ENNReal.ofReal
      ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (4 * V s * gaussianAbsoluteMoment p ^ (2 / p)))) ≤ M) :
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤ M ^ (p / 2) := by
  classical
  let μx : Measure (UnitAddTorus (Fin d)) := volume
  let P : Measure (Fin ι → ℝ) := productStandardGaussian (Fin ι)
  let q : ℝ := p / 2
  let w : (Fin d → ℕ) → ℝ := fun s =>
    (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ))
  let g : (Fin d → ℕ) → (Fin ι → ℝ) → UnitAddTorus (Fin d) → ℝ :=
    fun s z x => w s * ‖SmoothResolution.block s
      (gaussianSynthesis atoms z) x‖ ^ 2
  let G : (Fin ι → ℝ) × UnitAddTorus (Fin d) → ℝ≥0∞ :=
    fun y => (SmoothResolution.squareFunctionSquared r
      (gaussianSynthesis atoms y.1) y.2) ^ q
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := by dsimp [q]; linarith
  have hVmoment (s : Fin d → ℕ) :
      0 ≤ w s * (4 * V s * gaussianAbsoluteMoment p ^ (2 / p)) := by
    have hm : 0 ≤ gaussianAbsoluteMoment p := by
      unfold gaussianAbsoluteMoment
      exact integral_nonneg fun _ => by positivity
    dsimp [w]
    positivity [hm, hV s]
  have hgm (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
      Measurable (fun z : Fin ι → ℝ => g s z x) := by
    have hrepr : (fun z : Fin ι → ℝ => g s z x) =
        fun z => w s * ‖∑ i : Fin ι, (z i : ℂ) *
          SmoothResolution.block s (atoms i) x‖ ^ 2 := by
      funext z
      dsimp [g]
      rw [AtomicBlockVariance.smoothBlock_gaussianSynthesis]
    rw [hrepr]
    fun_prop
  have hgnonneg (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) (z : Fin ι → ℝ) :
      0 ≤ g s z x := by
    dsimp [g]
    positivity
  have hsum (x : UnitAddTorus (Fin d)) :
      (∑' s : Fin d → ℕ,
        eLpNorm (fun z : Fin ι → ℝ => g s z x)
          (ENNReal.ofReal q) P) ≤ M := by
    calc
      _ ≤ ∑' s : Fin d → ℕ, ENNReal.ofReal
          (w s * (4 * V s * gaussianAbsoluteMoment p ^ (2 / p))) := by
        apply ENNReal.tsum_le_tsum
        intro s
        have hw : 0 ≤ w s := by dsimp [w]; positivity
        exact smoothBlock_square_eLpNorm_le s atoms x hp2 (V s) (hV s)
          (hvariance s x) (w s) hw
      _ ≤ M := by simpa [w] using hsummable
  have hpoint (x : UnitAddTorus (Fin d)) :
      (∫⁻ z : Fin ι → ℝ,
        (SmoothResolution.squareFunctionSquared r
          (gaussianSynthesis atoms z) x) ^ q ∂P) ≤ M ^ q := by
    have hsum' := lintegral_tsum_ofReal_rpow_le_of_lsum_eLpNorm e
      (fun s z => g s z x) hq1 (fun s => hgm s x)
      (fun s z => hgnonneg s x z) (hsum x)
    have hident (z : Fin ι → ℝ) :
        SmoothResolution.squareFunctionSquared r (gaussianSynthesis atoms z) x =
          ∑' s : Fin d → ℕ, ENNReal.ofReal (g s z x) := by
      simp [SmoothResolution.squareFunctionSquared, g, w]
    simpa only [hident] using hsum'
  have hGmeas : Measurable G := by
    have hbase := smoothSquare_gaussian_joint_measurable r atoms
    dsimp [G]
    exact hbase.pow_const q
  letI : IsProbabilityMeasure μx := by
    dsimp [μx]
    infer_instance
  have hprod := MeasureTheory.lintegral_prod (μ := P) (ν := μx) G hGmeas.aemeasurable
  have hsymm := MeasureTheory.lintegral_prod_symm (μ := P) (ν := μx) G hGmeas.aemeasurable
  calc
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ q ∂μx ∂P)
        = ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), G y ∂P.prod μx := by
          simpa [G, P, μx] using hprod.symm
    _ = ∫⁻ x : UnitAddTorus (Fin d), ∫⁻ z : Fin ι → ℝ, G (z,x) ∂P ∂μx := hsymm
    _ ≤ ∫⁻ x : UnitAddTorus (Fin d), M ^ q ∂μx := by
          apply lintegral_mono
          intro x
          simpa [G, P] using hpoint x
    _ = M ^ q := by simp [μx]

end BrownianSharp
