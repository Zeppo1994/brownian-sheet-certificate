import BrownianSharp.AlignmentAnchoredLpEnergy
import BrownianSharp.PeriodicNativeEntropy
import BrownianSharp.SmoothEnergyNormalization
import BrownianSharp.NativeEnergyRate
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentPaperPeriodic
import BrownianSharp.AlignmentOperatorWidthIndexShift

set_option pp.proofs false
noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped ENNReal NNReal BigOperators Pointwise
namespace BrownianSharp.AlignmentPaperAnchoredLpLower
open BrownianSharp.AlignmentAnchoredLpEnergy
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp

theorem scaled_field_ball_cap
    {Ω Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : Measure Ω) (V : Ω → Y) (A ε ρ : ℝ)
    (hA : 0 < A) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hrad : ρ ≤ A*ε)
    (Q : ℝ≥0∞)
    (hcap : ∀ f : Y, P {x | edist (V x) f ≤ ENNReal.ofReal ε} ≤ Q) :
    ∀ f : Y, P {x | edist (A • V x) f ≤ ENNReal.ofReal ρ} ≤ Q := by
  intro f
  apply le_trans (measure_mono ?_) (hcap (A⁻¹ • f))
  intro x hx
  have hd : dist (A • V x) f ≤ ρ := by
    change edist (A • V x) f ≤ ENNReal.ofReal ρ at hx
    rw [edist_dist] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp hx
  have hdiff : V x - A⁻¹ • f = A⁻¹ • (A • V x - f) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
  have hnorm : dist (V x) (A⁻¹ • f) ≤ ε := by
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA)]
    rw [dist_eq_norm] at hd
    calc
      A⁻¹ * ‖A • V x - f‖ ≤ A⁻¹ * ρ :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ A⁻¹ * (A * ε) := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = ε := by field_simp
  change edist (V x) (A⁻¹ • f) ≤ ENNReal.ofReal ε
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hnorm

theorem scaledCube_externalCover_gt_of_class_mass
    {d n k : ℕ} {A ε ρ : ℝ}
    (hA : 0 < A) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hrad : ρ ≤ A*ε)
    (K : Set C(BrownianCubeAnchor d, ℝ))
    (E : Set (LayerIndex d n → ℝ)) (Q : ℝ≥0∞)
    (hclass : ∀ x ∈ E, A • smoothNativeCubePath x ∈ K)
    (hcap : ∀ f : C(BrownianCubeAnchor d, ℝ),
      productStandardGaussian (LayerIndex d n)
        {x | edist (smoothNativeCubePath x) f ≤ ENNReal.ofReal ε} ≤ Q)
    (hmass : ((2^(k-1):ℕ):ℝ≥0∞)*Q <
      productStandardGaussian (LayerIndex d n) E) :
    ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber ⟨ρ,hρ⟩ K := by
  apply externalCoveringNumber_gt_of_admissible_mass
    (productStandardGaussian (LayerIndex d n))
    (fun x => A • smoothNativeCubePath x) E K ⟨ρ,hρ⟩ Q
    (2^(k-1)) hclass
  · intro f
    convert scaled_field_ball_cap (productStandardGaussian (LayerIndex d n))
        smoothNativeCubePath A ε ρ hA hε hρ hrad Q hcap f using 1 <;>
      simp only [ENNReal.ofReal_eq_coe_nnreal hρ]
    congr 1
  · exact hmass

theorem cube_entropy_rate_of_scaled_smooth_class_mass
    {d : ℕ} (hd : 2 ≤ d) (K : Set C(BrownianCubeAnchor d, ℝ))
    (r β a : ℝ) (hr : 0 < r) (ha : 0 < a) (N : ℕ)
    (hclass : ∀ n : ℕ, N ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r β) • smoothNativeCubePath x ∈ K}) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  obtain ⟨a₀,b,ha₀,hb,hconf⟩ := AlignmentPaperConfinementBridge.norm_confinement_all_grades hd
    (fun n => smoothNativeCubePath (d := d) (n := n))
    (fun n z s hs => ⟨⟨s, fun i => hs i (Set.mem_univ i)⟩,
      AlignmentPaperConfinementBridge.periodicNative_cube_eq z s hs⟩)
  let s : ℕ := max 1 ⌈(2/b)⌉₊
  have hs : 1 ≤ s := le_max_left _ _
  have hceil : 2/b ≤ (s:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 ⌈(2/b)⌉₊)
  have hbs : 2 ≤ b*(s:ℝ) := by
    have h := (div_le_iff₀ hb).1 hceil
    nlinarith
  have htwo : 1 ≤ 2*s := by omega
  obtain ⟨k₀,hk₀,hgrade⟩ := nativeEntropyCrossing_multiple_eventually_ge hd htwo (max N s)
  let η : ℝ := a₀ / 2
  have hη : 0 < η := half_pos ha₀
  have hcover : ∀ (k : ℕ) (hk : k₀ ≤ k),
      ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber
        (NNReal.mk ((a*η)*periodicNativeRadius d
          (nativeEntropyCrossing d ((2*s)*k) (by omega)) r β)
          (mul_pos (mul_pos ha hη) (periodicNativeRadius_pos
            (nativeEntropyCrossing_bracket hd (by nlinarith [hk] : 2≤(2*s)*k)).1)).le) K := by
    intro k hk
    have hk2 : 2 ≤ k := hk₀.trans hk
    let q := nativeEntropyCrossing d ((2*s)*k) (by omega)
    have hsk : 2 ≤ (2*s)*k := by nlinarith
    have hbr := nativeEntropyCrossing_bracket hd hsk
    have hq : 0 < q := hbr.1
    have hqN : N ≤ q := (le_max_left N s).trans (hgrade k hk)
    have hqs : s ≤ q := (le_max_right N s).trans (hgrade k hk)
    let S : ℕ := Nat.choose (2*q+d-1) (d-1)
    let D : ℝ := nativeDimension d (2*q)
    have hS : 0 < S := Nat.choose_pos (by omega)
    have hDk : (2*(s:ℝ))*(k:ℝ) ≤ D := by
      have h := hbr.2.2.1
      simpa [D, q, Nat.cast_mul] using h
    have hDS : (2*(s:ℝ))*(S:ℝ) ≤ D := by
      have hnat : 2*s ≤ 2^(2*q) :=
        (Nat.mul_le_mul_left 2 hqs).trans (Nat.le_of_lt (2*q).lt_two_pow_self)
      have hreal : 2*(s:ℝ) ≤ (2:ℝ)^(2*q) := by exact_mod_cast hnat
      change (2*(s:ℝ))*(S:ℝ) ≤ (2:ℝ)^(2*q)*hyperbolicCount d (2*q)
      have hSid : (S:ℝ) = hyperbolicCount d (2*q) := rfl
      rw [← hSid]
      exact mul_le_mul_of_nonneg_right hreal (Nat.cast_nonneg _)
    have hbudget := dyadic_exponential_mass_lt_shape_cutoff hk2 hb hbs hDk hDS
    let A : ℝ := a*periodicSynthesisScale d (2*q) r β
    let ε : ℝ := η*Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q))
    let ρ : ℝ := (a*η)*periodicNativeRadius d q r β
    have hA : 0 < A := mul_pos ha (periodicSynthesisScale_pos (by omega) r β)
    have hε : 0 < ε := mul_pos hη (Real.sqrt_pos.2
      (mul_pos (by exact_mod_cast (by omega : 0<2*q)) (hyperbolicCount_pos (by omega))))
    have hρ : 0 < ρ := mul_pos (mul_pos ha hη) (periodicNativeRadius_pos hq)
    have hρε : ρ ≤ A*ε := by
      have heq := periodicSynthesisScale_mul_confinement (d:=d) (q:=q) (by omega) a η r β
      exact le_of_eq heq.symm
    let Q := ENNReal.ofReal (Real.exp (-b*D))
    have hcap : ∀ f : C(BrownianCubeAnchor d, ℝ),
        productStandardGaussian (LayerIndex d (2*q))
          {x | edist (smoothNativeCubePath x) f ≤ ENNReal.ofReal ε} ≤ Q := by
      have hεR : 2 * ε = a₀ * Real.sqrt (((2*q:ℕ):ℝ)*hyperbolicCount d (2*q)) := by
        dsimp [ε, η]
        ring
      have hconfNN : productStandardGaussian (LayerIndex d (2*q))
          {x | ‖smoothNativeCubePath x‖ ≤ 2 * ((⟨ε, hε.le⟩ : ℝ≥0) : ℝ)} ≤ Q := by
        change productStandardGaussian (LayerIndex d (2*q))
          {x | ‖smoothNativeCubePath x‖ ≤ 2 * ε} ≤ Q
        rw [hεR, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        apply ENNReal.ofReal_le_ofReal
        simpa [Measure.real_def, D] using hconf (2*q) (by omega)
      have h := smoothNativeCubePath_translated_ball_mass_le (by omega) ⟨ε, hε.le⟩ Q hconfNN
      intro f
      have hf := h f
      convert hf using 1 <;> simp only [ENNReal.ofReal_eq_coe_nnreal hε.le]
      congr 1
    let E : Set (LayerIndex d (2*q) → ℝ) :=
      {x | A • smoothNativeCubePath x ∈ K}
    have hmass : ((2^(k-1):ℕ):ℝ≥0∞)*Q < productStandardGaussian (LayerIndex d (2*q)) E :=
      hbudget.trans_le (hclass (2*q) (by omega))
    exact scaledCube_externalCover_gt_of_class_mass hA hε.le hρ.le hρε K E Q
      (fun x hx => hx) hcap hmass
  obtain ⟨c,hc,hentropy⟩ := periodic_entropy_rate_of_cover_at_multiple K hd htwo hk₀
    r β (a*η) hr (mul_pos ha hη) hcover
  exact ⟨c,hc,k₀,hk₀,hentropy⟩

theorem derivative_energy_rate
    {d n : ℕ} (hd : 1 ≤ d) (p C : ℝ) (hp : 0 < p) (hC : 0 < C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C) :
    (∫⁻ z : LayerIndex d n → ℝ, firstMixedDerivativeCubeEnergy p z
      ∂productStandardGaussian (LayerIndex d n)) ≤
      ENNReal.ofReal (((C^d)^p * gaussianAbsoluteMoment p) *
        (nativeClassNormScale d n 1 (1/2))^p) := by
  have h := firstMixedDerivative_cube_expected_rpow_le (d := d) (n := n) p C hC.le hderiv hp
  have hcard : (Fintype.card (Shape d n) : ℝ) = hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast shape_card d n hd
  have hraw : (2 : ℝ)^n * C^d * Real.sqrt (Fintype.card (Shape d n) : ℝ) =
      C^d * nativeClassNormScale d n 1 (1/2) := by
    rw [hcard, Real.sqrt_eq_rpow]
    unfold nativeClassNormScale
    rw [one_mul, Real.rpow_natCast]
    ring
  have heq : ((2 : ℝ)^n * C^d * Real.sqrt (Fintype.card (Shape d n) : ℝ))^p *
      gaussianAbsoluteMoment p =
      ((C^d)^p * gaussianAbsoluteMoment p) * (nativeClassNormScale d n 1 (1/2))^p := by
    rw [hraw, Real.mul_rpow (pow_nonneg hC.le _) (nativeClassNormScale_pos hd _ _).le]
    ring
  simpa only [firstMixedDerivativeCubeEnergy, heq] using h

theorem exists_scaled_cube_image_mass
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ,
      (1/2 : ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
        {z | (a * periodicSynthesisScale d n 1 0) • smoothNativeCubePath z ∈
          anchoredIntegrationLpImage d p} := by
  obtain ⟨C, hC, hderiv⟩ := exists_smoothAtom_iteratedDeriv_bound 1
  let G := (C^d)^p * gaussianAbsoluteMoment p
  have hG : 0 ≤ G := by
    have hmoment : 0 ≤ gaussianAbsoluteMoment p := by
      unfold gaussianAbsoluteMoment
      exact integral_nonneg fun _ => by positivity
    dsimp [G]
    positivity
  let B := 1 + 2*G
  have hB : 0 < B := by dsimp [B]; linarith
  let Q := B^(1/p)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hB _
  have hQpow : Q^p = B := by
    dsimp [Q]
    rw [← Real.rpow_mul hB.le,
      show (1/p)*p = (1 : ℝ) by field_simp, Real.rpow_one]
  let a := Q⁻¹
  refine ⟨a, inv_pos.mpr hQ, ?_⟩
  intro n
  let N := nativeClassNormScale d n 1 (1/2)
  have hN : 0 < N := nativeClassNormScale_pos (by omega) _ _
  let L := Q*N
  have hL : 0 < L := mul_pos hQ hN
  have hLpow : L^p = B*N^p := by
    dsimp [L]
    rw [Real.mul_rpow hQ.le hN.le, hQpow]
  have hmean : (∫⁻ z : LayerIndex d n → ℝ, firstMixedDerivativeCubeEnergy p z
      ∂productStandardGaussian (LayerIndex d n)) ≤ ENNReal.ofReal (L^p/2) := by
    apply (derivative_energy_rate (by omega) p C (by linarith) hC hderiv).trans
    apply ENNReal.ofReal_le_ofReal
    change G * N^p ≤ L^p/2
    rw [hLpow]
    have hNp : 0 ≤ N^p := Real.rpow_nonneg hN.le _
    dsimp [B]
    nlinarith
  have hmass := firstMixedDerivative_smoothNative_image_ball_mass p hp L hL hmean
  have hAL : (a*periodicSynthesisScale d n 1 0)*L = 1 := by
    rw [periodicSynthesisScale_eq_inverseNormScale]
    norm_num
    dsimp [a, L, N]
    field_simp [ne_of_gt hQ,
      ne_of_gt (nativeClassNormScale_pos (d := d) (n := n) (by omega) 1 (1/2))]
    exact div_self (ne_of_gt hN)
  apply hmass.trans
  apply measure_mono
  intro z hz
  obtain ⟨y, hy, hzy⟩ := hz
  have hy' : y ∈ anchoredIntegrationLpImage d p := by
    rwa [← anchoredIntegrationOperator_image_eq p hp]
  change L • y = smoothNativeCubePath z at hzy
  change (a*periodicSynthesisScale d n 1 0) • smoothNativeCubePath z ∈
    anchoredIntegrationLpImage d p
  rw [← hzy, smul_smul, hAL, one_smul]
  exact hy'

theorem anchoredIntegrationLp_entropy_lower_all_p
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (anchoredIntegrationLpImage d p) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  obtain ⟨a, ha, hmass⟩ := exists_scaled_cube_image_mass hd p hp
  obtain ⟨c, hc, k₀, hk₀, hent⟩ := cube_entropy_rate_of_scaled_smooth_class_mass hd
    (anchoredIntegrationLpImage d p) 1 0 a (by norm_num) ha 0 (by
      intro n _
      exact (shapeCutoff_le_half (by omega)).trans (hmass n))
  refine ⟨c, hc, k₀, hk₀, ?_⟩
  intro k hk
  have he : (1 : ℝ)*((d-1:ℕ):ℝ)+(1/2+0*((d-1:ℕ):ℝ)) = (d:ℝ)-1/2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    ring
  simpa only [he, cmIndexRate, logarithmicIndexRate, mul_assoc] using hent k hk

theorem anchoredIntegrationLp_image_norm_le_one
    {d : ℕ} (p : ℝ) (hp : 1 < p) (f : C(BrownianCubeAnchor d, ℝ))
    (hf : f ∈ anchoredIntegrationLpImage d p) : ‖f‖ ≤ 1 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  rw [← anchoredIntegrationOperator_image_eq p hp] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have hg' : ‖g‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hg
  exact (integrationPath_norm_le p hp g).trans hg'

theorem anchoredIntegrationLp_width_zero_le_one
    {d : ℕ} (p : ℝ) (hp : 1 < p) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth (anchoredIntegrationLpImage d p) 0 ≤ 1 := by
  rw [HaarQuarter.TheoremD.Width.kolmogorovWidth_zero_eq_bot]
  have h := AlignmentAmbientWidth.approximationError_le_of_pointwise
    (anchoredIntegrationLpImage d p)
    (⊥ : Submodule ℝ C(BrownianCubeAnchor d, ℝ)) (ε := 1) (by norm_num) (by
      intro f hf
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simpa using anchoredIntegrationLp_image_norm_le_one p hp f hf)
  simpa using h

theorem anchoredIntegrationLp_entropy_equivalent_ge_two
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    AlignmentPaperPeriodic.twoSidedEntropyRate (anchoredIntegrationLpImage d p)
      1 ((d:ℝ)-1/2) := by
  obtain ⟨cl,hcl,nl,hnl,hl⟩ :=
    anchoredIntegrationLp_entropy_lower_all_p hd p (by linarith)
  obtain ⟨cu,hcu,nu,hu⟩ := anchoredIntegrationLp_entropy_upper hd hp
  refine ⟨cl,cu,hcl,hcu,max nl (max 2 nu),hnl.trans (le_max_left _ _),?_⟩
  intro k hk
  constructor
  · exact hl k ((le_max_left _ _).trans hk)
  · exact hu k ((le_max_right 2 nu).trans ((le_max_right nl _).trans hk))

theorem anchoredIntegrationLp_width_equivalent_ge_two
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    Latest.twoSidedWidthRate (anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2) := by
  obtain ⟨cl,hcl,nl,hnl,hl⟩ :=
    anchoredIntegrationLp_entropy_lower_all_p hd p (by linarith)
  obtain ⟨cu,hcu,nu,_hnu,hu⟩ := anchoredIntegrationLp_width_upper hd hp
  apply AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
    (anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2) 1 (by norm_num)
    (by
      have h : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith) (by norm_num)
    (by simpa using anchoredIntegrationLp_width_zero_le_one (d := d) p (by linarith))
  · exact ⟨cl,hcl,nl,hl⟩
  · exact ⟨cu,hcu,nu,hu⟩

theorem anchoredIntegrationLp_operatorWidth_equivalent_ge_two
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    AlignmentOperatorStatements.twoSidedWidthRate
      (anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2) := by
  obtain ⟨c,C,hc,hC,k₀,hk₀,hwidth⟩ :=
    anchoredIntegrationLp_width_equivalent_ge_two hd p hp
  let k₁ := max (k₀+1) 3
  have hk₁ : 3 ≤ k₁ := le_max_right _ _
  have hk₀' : k₀+1 ≤ k₁ := le_max_left _ _
  obtain ⟨c',C',hc',hC',hshift⟩ :=
    AlignmentOperatorWidthIndexShift.twoSided_width_index_shift
      (anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2) (by norm_num)
      (by
      have h : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith)
      c C hc hC k₁ hk₁ (by
        intro k hk
        exact hwidth (k-1) (by omega))
  refine ⟨c',C',hc',hC',k₁,by omega,?_⟩
  intro k hk
  have hEq := AlignmentOperatorNumbers.operatorKolmogorovNumber_eq_width_pred
    (anchoredIntegrationLpImage d p) (by omega : 1 ≤ k)
  simpa only [hEq] using hshift k hk

end BrownianSharp.AlignmentPaperAnchoredLpLower

