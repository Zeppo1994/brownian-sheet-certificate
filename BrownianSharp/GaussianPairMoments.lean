import BrownianSharp.GaussianRows
import BrownianSharp.Moments

/-!
Transfer the independent-coordinate high-moment envelope to an independent
pair of standard Gaussian random variables on an arbitrary probability space.
This is the distributional bridge used after orthogonalizing two Gaussian rows.
-/

open MeasureTheory ProbabilityTheory

namespace BrownianSharp


/-- Any two finite linear combinations of independent Gaussian coordinates form
an actual jointly Gaussian pair. This is assembled from the independent vector
of two-dimensional coordinate contributions. -/
theorem gaussianRows_pair_hasGaussianLaw
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ) :
    HasGaussianLaw (fun ω => (GaussianRows.row G c ω, GaussianRows.row G d ω)) P := by
  classical
  let Z : ι → Ω → ℝ × ℝ := fun i ω => (c i * G i ω, d i * G i ω)
  have hZIndep : iIndepFun Z P := by
    simpa [Z, Function.comp_def] using
      hIndep.comp (fun i x => (c i * x, d i * x)) (fun _ => by fun_prop)
  have hZlaw (i : ι) : HasGaussianLaw (Z i) P := by
    let f : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ (c i)
    let g : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ (d i)
    have h := (GaussianRows.coordinate_gaussian G hG hLaw i).map (f.prod g)
    convert h using 1 <;> ext ω <;> simp [Z, f, g, ContinuousLinearMap.lsmul_apply]
  have hsum := hZIndep.hasGaussianLaw_fun_sum hZlaw
  convert hsum using 1
  funext ω
  apply Prod.ext
  · simp [GaussianRows.row, Z, Prod.fst_sum]
  · simp [GaussianRows.row, Z, Prod.snd_sum]

/-- The direct binomial covariance envelope is invariant under replacing the
canonical product Gaussian coordinates by any independent standard Gaussian
pair. -/
theorem independentStandardGaussian_evenPowerCovariance_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : P.map X = gaussianReal (0 : ℝ) (1 : NNReal))
    (hYlaw : P.map Y = gaussianReal (0 : ℝ) (1 : NNReal))
    (hXY : IndepFun X Y P) (k : ℕ) (rho : ℝ) (hrho : rho ^ 2 ≤ 1) :
    (((∫ ω, X ω ^ (2 * k) *
        (rho * X ω + Real.sqrt (1 - rho ^ 2) * Y ω) ^ (2 * k) ∂P) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1) ≤
      ((4 * k : ℝ) * |rho|) ^ 2 * Real.exp ((4 * k : ℝ) * |rho|) := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  let Φ : Ω → ℝ × ℝ := fun ω => (X ω, Y ω)
  let F : ℝ × ℝ → ℝ := fun z =>
    z.1 ^ (2 * k) * (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ (2 * k)
  have hΦ : Measurable Φ := Measurable.prodMk hX hY
  have hmap : P.map Φ = γ.prod γ := by
    dsimp [Φ, γ]
    rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hXlaw, hYlaw]
  have hF : AEStronglyMeasurable F (P.map Φ) := by
    rw [hmap]
    dsimp [F]
    fun_prop
  have htransfer :
      (∫ z : ℝ × ℝ, z.1 ^ (2 * k) *
        (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ (2 * k) ∂(γ.prod γ)) =
      ∫ ω, X ω ^ (2 * k) *
        (rho * X ω + Real.sqrt (1 - rho ^ 2) * Y ω) ^ (2 * k) ∂P := by
    have h := integral_map hΦ.aemeasurable hF
    simpa [Φ, F, hmap, γ] using h
  rw [← htransfer]
  exact correlatedGaussian_evenPowerCovariance_bound k rho hrho


/-- High-order moment covariance for two normalized linear combinations of
independent standard Gaussian coordinates, when their correlation is strictly
inside the unit interval. The residual direction is obtained by orthogonalizing
one coefficient vector against the other. -/
theorem normalizedGaussianRows_evenPowerCovariance_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (k : ℕ) (hrho :
      (∑ i, c i * d i) ^ 2 < 1) :
    (((∫ ω, GaussianRows.row G c ω ^ (2 * k) *
        GaussianRows.row G d ω ^ (2 * k) ∂P) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1) ≤
      ((4 * k : ℝ) * |∑ i, c i * d i|) ^ 2 *
        Real.exp ((4 * k : ℝ) * |∑ i, c i * d i|) := by
  classical
  let rho : ℝ := ∑ i, c i * d i
  let sigma : ℝ := Real.sqrt (1 - rho ^ 2)
  let e : ι → ℝ := fun i => (d i - rho * c i) / sigma
  let X : Ω → ℝ := GaussianRows.row G c
  let Y : Ω → ℝ := GaussianRows.row G e
  have hrho' : rho ^ 2 < 1 := by simpa [rho] using hrho
  have hsigma2 : sigma ^ 2 = 1 - rho ^ 2 := by
    dsimp [sigma]
    rw [Real.sq_sqrt]
    nlinarith
  have hsigma0 : 0 < sigma := Real.sqrt_pos.mpr (by nlinarith)
  have hsigmaNe : sigma ≠ 0 := ne_of_gt hsigma0
  have hcross : ∑ i, (d i - rho * c i) ^ 2 = 1 - rho ^ 2 := by
    have hpw : ∀ i, (d i - rho * c i) ^ 2 =
        d i ^ 2 - 2 * rho * (c i * d i) + rho ^ 2 * c i ^ 2 := by
      intro i
      ring
    calc
      ∑ i, (d i - rho * c i) ^ 2 =
          (∑ i, d i ^ 2) - 2 * rho * (∑ i, c i * d i) +
            rho ^ 2 * (∑ i, c i ^ 2) := by
        calc
          _ = ∑ i, (d i ^ 2 - 2 * rho * (c i * d i) + rho ^ 2 * c i ^ 2) :=
            Finset.sum_congr rfl (fun i hi => hpw i)
          _ = (∑ i, d i ^ 2) - (∑ i, 2 * rho * (c i * d i)) +
              ∑ i, rho ^ 2 * c i ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = (∑ i, d i ^ 2) - 2 * rho * (∑ i, c i * d i) +
              rho ^ 2 * (∑ i, c i ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 - rho ^ 2 := by
        rw [hd, hc]
        dsimp [rho]
        ring
  have heNorm : ∑ i, e i ^ 2 = 1 := by
    dsimp [e]
    simp_rw [div_pow]
    rw [← Finset.sum_div, hcross, hsigma2]
    field_simp [ne_of_gt (by nlinarith : 0 < 1 - rho ^ 2)]
  have heOrth : ∑ i, c i * e i = 0 := by
    dsimp [e]
    have hnum : ∑ i, c i * (d i - rho * c i) =
        (∑ i, c i * d i) - rho * (∑ i, c i ^ 2) := by
      calc
        _ = ∑ i, (c i * d i - rho * c i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, c i * d i) - ∑ i, rho * c i ^ 2 := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ i, c i * d i) - rho * (∑ i, c i ^ 2) := by
          rw [← Finset.mul_sum]
    rw [show (fun i => c i * ((d i - rho * c i) / sigma)) =
        fun i => (c i * (d i - rho * c i)) / sigma by
          funext i; ring]
    rw [← Finset.sum_div, hnum, hc]
    dsimp [rho]
    field_simp [hsigmaNe]
    ring
  have hXlaw : P.map X = gaussianReal 0 1 := by
    dsimp [X]
    rw [GaussianRows.row_law G hG hLaw hIndep c, hc]
    norm_num
  have hYlaw : P.map Y = gaussianReal 0 1 := by
    dsimp [Y]
    rw [GaussianRows.row_law G hG hLaw hIndep e, heNorm]
    norm_num
  have hPair := gaussianRows_pair_hasGaussianLaw G hG hLaw hIndep c e
  have hcov : cov[X, Y; P] = 0 := by
    rw [show X = GaussianRows.row G c by rfl,
      show Y = GaussianRows.row G e by rfl,
      GaussianRows.row_covariance G hG hLaw hIndep]
    simpa [heOrth]
  have hXY : IndepFun X Y P := hPair.indepFun_of_covariance_eq_zero hcov
  have hXm : Measurable X := by
    change Measurable (fun ω => ∑ i, c i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hYm : Measurable Y := by
    change Measurable (fun ω => ∑ i, e i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hrel : ∀ ω, GaussianRows.row G d ω =
      rho * X ω + sigma * Y ω := by
    intro ω
    have hrow : sigma * GaussianRows.row G e ω =
        ∑ i, (d i - rho * c i) * G i ω := by
      dsimp [GaussianRows.row, e]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hsigmaNe]
    have hsum : (∑ i, (d i - rho * c i) * G i ω) =
        GaussianRows.row G d ω - rho * GaussianRows.row G c ω := by
      calc
        _ = ∑ i, (d i * G i ω - rho * (c i * G i ω)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, d i * G i ω) - ∑ i, rho * (c i * G i ω) := by
          rw [Finset.sum_sub_distrib]
        _ = GaussianRows.row G d ω - rho * GaussianRows.row G c ω := by
          rw [GaussianRows.row, GaussianRows.row, Finset.mul_sum]
    dsimp [X, Y]
    nlinarith
  have hbound := independentStandardGaussian_evenPowerCovariance_bound
    P X Y hXm hYm hXlaw hYlaw hXY k rho (by nlinarith [hrho'])
  calc
    (((∫ ω, GaussianRows.row G c ω ^ (2 * k) *
        GaussianRows.row G d ω ^ (2 * k) ∂P) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1) =
      (((∫ ω, X ω ^ (2 * k) *
        (rho * X ω + sigma * Y ω) ^ (2 * k) ∂P) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1) := by
        congr 2
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← hrel ω]
    _ ≤ ((4 * k : ℝ) * |rho|) ^ 2 * Real.exp ((4 * k : ℝ) * |rho|) := by
      simpa [sigma] using hbound



/-- At the degenerate correlation endpoint, the normalized doubled moment is
bounded by a central-binomial coefficient, hence by `4^p`. -/
theorem standardGaussian_doubledMoment_ratio_le (k : ℕ) :
    (∫ x : ℝ, x ^ (4 * k) ∂gaussianReal 0 1) /
        ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ^ 2) ≤ (4 : ℝ) ^ (2 * k) := by
  have hchooseN := Nat.choose_mul_factorial_mul_factorial
    (show 2 * k ≤ 4 * k by omega)
  have hidx : 4 * k - 2 * k = 2 * k := by omega
  rw [hidx] at hchooseN
  have hchooseR : (Nat.choose (4 * k) (2 * k) : ℝ) *
      (Nat.factorial (2 * k) : ℝ) ^ 2 = (Nat.factorial (4 * k) : ℝ) := by
    have hchooseNat : Nat.choose (4 * k) (2 * k) *
        (Nat.factorial (2 * k)) ^ 2 = Nat.factorial (4 * k) := by
      nlinarith [hchooseN]
    exact_mod_cast hchooseNat
  have heq :
      (∫ x : ℝ, x ^ (4 * k) ∂gaussianReal 0 1) /
        ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ^ 2) =
      (Nat.choose (4 * k) (2 * k) : ℝ) *
        (Nat.factorial k : ℝ) ^ 2 / (Nat.factorial (2 * k) : ℝ) := by
    rw [show 4 * k = 2 * (2 * k) by omega,
      standardGaussian_evenMoment_factorial (2 * k),
      standardGaussian_evenMoment_factorial k]
    have hchooseR' : (Nat.choose (2 * (2 * k)) (2 * k) : ℝ) *
        (Nat.factorial (2 * k) : ℝ) ^ 2 =
          (Nat.factorial (2 * (2 * k)) : ℝ) := by
      simpa [show 2 * (2 * k) = 4 * k by omega] using hchooseR
    rw [← hchooseR']
    field_simp
    ring
  have hfacNat : Nat.factorial k * Nat.factorial k ≤ Nat.factorial (2 * k) := by
    have hmul := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have hidx : 2 * k - k = k := by omega
    rw [hidx] at hmul
    have hcpos : 1 ≤ Nat.choose (2 * k) k := by
      exact Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    nlinarith [hmul, hcpos]
  have hfac : (Nat.factorial k : ℝ) ^ 2 ≤
      (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast (by simpa [pow_two] using hfacNat)
  have hchoose : (Nat.choose (4 * k) (2 * k) : ℝ) ≤ (2 : ℝ) ^ (4 * k) := by
    exact_mod_cast Nat.choose_le_two_pow (4 * k) (2 * k)
  calc
    _ = (Nat.choose (4 * k) (2 * k) : ℝ) *
        (Nat.factorial k : ℝ) ^ 2 / (Nat.factorial (2 * k) : ℝ) := heq
    _ ≤ (Nat.choose (4 * k) (2 * k) : ℝ) := by
      have hfrac : (Nat.factorial k : ℝ) ^ 2 /
          (Nat.factorial (2 * k) : ℝ) ≤ 1 :=
        div_le_one_of_le₀ hfac (by positivity)
      calc
        _ = (Nat.choose (4 * k) (2 * k) : ℝ) *
            ((Nat.factorial k : ℝ) ^ 2 / (Nat.factorial (2 * k) : ℝ)) := by ring
        _ ≤ (Nat.choose (4 * k) (2 * k) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = _ := by ring
    _ ≤ (4 : ℝ) ^ (2 * k) := by
      have hpow : (2 : ℝ) ^ (4 * k) = (4 : ℝ) ^ (2 * k) := by
        rw [show 4 * k = 2 * (2 * k) by omega, pow_mul]
        norm_num
      rw [← hpow]
      exact hchoose

/-- Integer-power form of the standard Gaussian moment-root bound:
`E|G|^(2k) ≤ (sqrt(2k))^(2k)`. -/
theorem standardGaussian_evenMoment_le_sqrt_power (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ≤
      (Real.sqrt (2 * k : ℝ)) ^ (2 * k) := by
  rw [standardGaussian_evenMoment]
  have hdf : Nat.doubleFactorial (2 * k - 1) ≤ (2 * k) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        have hrec : Nat.doubleFactorial (2 * (k + 1) - 1) =
            (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
          simpa [Nat.mul_add, Nat.mul_one, Nat.sub_add_comm] using
            Nat.doubleFactorial_add_one (2 * k)
        rw [hrec]
        calc
          (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) ≤
              (2 * k + 2) * ((2 * k) ^ k) := by
            exact Nat.mul_le_mul (by omega) ih
          _ ≤ (2 * k + 2) * (2 * k + 2) ^ k := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
          _ = (2 * (k + 1)) ^ (k + 1) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_succ]
            ring
  have hdfR : (Nat.doubleFactorial (2 * k - 1) : ℝ) ≤ (2 * k : ℝ) ^ k := by
    exact_mod_cast hdf
  have hsqrt : (Real.sqrt (2 * k : ℝ)) ^ 2 = 2 * k :=
    Real.sq_sqrt (by positivity)
  calc
    (Nat.doubleFactorial (2 * k - 1) : ℝ) ≤ (2 * k : ℝ) ^ k := hdfR
    _ = (Real.sqrt (2 * k : ℝ)) ^ (2 * k) := by
      rw [pow_mul, hsqrt]


/-- The normalized-row envelope also covers the endpoint correlations
`rho = ±1`, where orthogonalization has a zero residual variance. -/
theorem normalizedGaussianRows_evenPowerCovariance_bound_full
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (k : ℕ) :
    (((∫ ω, GaussianRows.row G c ω ^ (2 * k) *
        GaussianRows.row G d ω ^ (2 * k) ∂P) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1) ≤
      ((4 * k : ℝ) * |∑ i, c i * d i|) ^ 2 *
        Real.exp ((4 * k : ℝ) * |∑ i, c i * d i|) := by
  classical
  let rho : ℝ := ∑ i, c i * d i
  have hCS : rho ^ 2 ≤ 1 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c d
    simpa [rho, hc, hd] using h
  by_cases hrhoStrict : rho ^ 2 < 1
  · simpa [rho] using
      normalizedGaussianRows_evenPowerCovariance_bound G hG hLaw hIndep c d hc hd k hrhoStrict
  · have hrhoSq : rho ^ 2 = 1 := le_antisymm hCS (le_of_not_gt hrhoStrict)
    have hcross : ∑ i, (d i - rho * c i) ^ 2 = 0 := by
      have hpw : ∀ i, (d i - rho * c i) ^ 2 =
          d i ^ 2 - 2 * rho * (c i * d i) + rho ^ 2 * c i ^ 2 := by
        intro i
        ring
      calc
        ∑ i, (d i - rho * c i) ^ 2 =
            (∑ i, d i ^ 2) - 2 * rho * (∑ i, c i * d i) +
              rho ^ 2 * (∑ i, c i ^ 2) := by
          calc
            _ = ∑ i, (d i ^ 2 - 2 * rho * (c i * d i) + rho ^ 2 * c i ^ 2) :=
              Finset.sum_congr rfl (fun i hi => hpw i)
            _ = (∑ i, d i ^ 2) - (∑ i, 2 * rho * (c i * d i)) +
                ∑ i, rho ^ 2 * c i ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            _ = (∑ i, d i ^ 2) - 2 * rho * (∑ i, c i * d i) +
                rho ^ 2 * (∑ i, c i ^ 2) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = 0 := by
          rw [hd, hc]
          have hdot : (∑ i, c i * d i) = rho := rfl
          rw [hdot]
          nlinarith [hrhoSq]
    have hcoord (i : ι) : d i = rho * c i := by
      have hle : (d i - rho * c i) ^ 2 ≤ ∑ j, (d j - rho * c j) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j => (d j - rho * c j) ^ 2)
          (fun j hj => sq_nonneg _) (Finset.mem_univ i)
      have : (d i - rho * c i) ^ 2 = 0 := by rw [hcross] at hle; nlinarith
      nlinarith [sq_nonneg (d i - rho * c i)]
    let X : Ω → ℝ := GaussianRows.row G c
    have hXm : Measurable X := by
      change Measurable (fun ω => ∑ i, c i * G i ω)
      exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
    have hXlaw : P.map X = gaussianReal 0 1 := by
      dsimp [X]
      rw [GaussianRows.row_law G hG hLaw hIndep c, hc]
      norm_num
    have hrow : ∀ ω, GaussianRows.row G d ω = rho * X ω := by
      intro ω
      calc
        GaussianRows.row G d ω = ∑ i, (rho * c i) * G i ω := by
          unfold GaussianRows.row
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoord i]
        _ = rho * X ω := by
          rw [show (∑ i, (rho * c i) * G i ω) =
              rho * (∑ i, c i * G i ω) by rw [Finset.mul_sum]; simp [mul_assoc]]
          rfl
    have hRhoCases : rho = 1 ∨ rho = -1 := by
      by_cases h : 0 ≤ rho
      · left
        nlinarith [sq_nonneg (rho - 1)]
      · right
        have hneg : rho < 0 := lt_of_not_ge h
        nlinarith [sq_nonneg (rho + 1)]
    have hAbs : |rho| = 1 := by rcases hRhoCases with h | h <;> simp [h]
    have hRhoPow : rho ^ (2 * k) = 1 := by
      rcases hRhoCases with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    have hMoment :
        (∫ ω, X ω ^ (4 * k) ∂P) =
          ∫ x : ℝ, x ^ (4 * k) ∂gaussianReal 0 1 := by
      have hm := integral_map hXm.aemeasurable
        (f := fun x : ℝ => x ^ (4 * k)) (by rw [hXlaw]; fun_prop)
      simpa [hXlaw] using hm.symm
    have hProduct : (∫ ω, GaussianRows.row G c ω ^ (2 * k) *
        GaussianRows.row G d ω ^ (2 * k) ∂P) =
        ∫ x : ℝ, x ^ (4 * k) ∂gaussianReal 0 1 := by
      calc
        _ = ∫ ω, X ω ^ (2 * k) * (rho * X ω) ^ (2 * k) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hrow ω]
        _ = ∫ ω, X ω ^ (4 * k) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          calc
            X ω ^ (2 * k) * (rho * X ω) ^ (2 * k) =
                X ω ^ (2 * k) * X ω ^ (2 * k) := by
              rw [mul_pow, hRhoPow]
              ring
            _ = X ω ^ (4 * k) := by
              rw [← pow_add]
              congr 1
              omega
        _ = _ := hMoment
    have hratio := standardGaussian_doubledMoment_ratio_le k
    have hfour : 4 ≤ Real.exp 2 := by
      have ht := exp_taylor_partial_le (2 : ℝ) (by norm_num) 3
      norm_num at ht
      linarith
    have hExp : (4 : ℝ) ^ (2 * k) ≤ Real.exp (4 * k) := by
      calc
        _ ≤ (Real.exp 2) ^ (2 * k) := by gcongr
        _ = Real.exp (4 * k) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    by_cases hk : k = 0
    · subst k
      simp [hProduct, hMoment, hXlaw, IsProbabilityMeasure.measure_univ]
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hxSq : (1 : ℝ) ≤ (4 * k : ℝ) ^ 2 := by
        have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        nlinarith
      rw [hProduct]
      calc
        ((∫ x : ℝ, x ^ (4 * k) ∂gaussianReal 0 1) /
            ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ^ 2)) - 1 ≤
            (4 : ℝ) ^ (2 * k) - 1 := by linarith [hratio]
        _ ≤ Real.exp (4 * k) := by linarith [hExp]
        _ ≤ ((4 * k : ℝ) * |rho|) ^ 2 * Real.exp ((4 * k : ℝ) * |rho|) := by
          calc
            Real.exp (4 * (k : ℝ)) = 1 * Real.exp (4 * (k : ℝ)) := by ring
            _ ≤ (4 * (k : ℝ)) ^ 2 * Real.exp (4 * (k : ℝ)) :=
              mul_le_mul_of_nonneg_right hxSq (Real.exp_nonneg _)
            _ = ((4 * k : ℝ) * |rho|) ^ 2 * Real.exp ((4 * k : ℝ) * |rho|) := by
              rw [hAbs]
              ring

end BrownianSharp
