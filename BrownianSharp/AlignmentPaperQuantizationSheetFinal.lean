import BrownianSharp.AlignmentPaperQuantizationSheetUpper
import BrownianSharp.AlignmentPaperQuantizationLowerCertified
import BrownianSharp.AlignmentPaperQuantizationLowerUniversal
import BrownianSharp.AlignmentPaperQuantizationEmpiricalComparison
import BrownianSharp.AlignmentPaperContinuousGaussianFernique
import BrownianSharp.AlignmentPaperMomentComparison

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperQuantizationSheetFinal

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperEmpiricalWasserstein
open BrownianSharp.AlignmentPaperEmpiricalWassersteinMeasurable
open BrownianSharp.AlignmentPaperQuantizationEmpiricalComparison
open BrownianSharp.AlignmentPaperQuantizationSheetUpper
open BrownianSharp.AlignmentPaperQuantizationAtomicBridge
open BrownianSharp.Latest

def fractionalRate (h : ℝ) (ν : ℕ) (m : ℕ) : ℝ :=
  (Real.log (m:ℝ)) ^ (-h) *
    (Real.log (Real.log (m:ℝ))) ^ (h*((ν-1:ℕ):ℝ)+(ν:ℝ)/2)

private theorem fractionalRadius_eq {h : ℝ} (hh : 0 < h) {ν m : ℕ}
    (hν : 1 ≤ ν)
    (c : ℝ) :
    canonicalPowerlogRadius (h⁻¹)
      (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) c (Real.log (m:ℝ)) =
      c * fractionalRate h ν m := by
  rw [canonicalPowerlogRadius]
  have he1 : -(1/(h⁻¹)) = -h := by field_simp [ne_of_gt hh]
  have he2 : (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h))/(h⁻¹) =
      h*((ν-1:ℕ):ℝ)+(ν:ℝ)/2 := by
    rw [Nat.cast_sub hν]
    field_simp [ne_of_gt hh]
  simp [he1, he2, fractionalRate]
  ring

private theorem fractionalRate_nonneg {h : ℝ} (hh : 0 < h)
    {ν m : ℕ} (hm : 3 ≤ m) : 0 ≤ fractionalRate h ν m := by
  have hm1 : 1 < (m:ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hloggt1 : 1 < Real.log (m:ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans_le hm3)
  dsimp [fractionalRate]
  apply mul_nonneg
  · exact Real.rpow_nonneg (Real.log_nonneg hm1.le) _
  · exact Real.rpow_nonneg (Real.log_pos hloggt1).le _

def FractionalQuantizationStatement
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) : Prop :=
∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : FractionalBrownianSheetOnCube d Ω P)
        (hBH : B.H = H) (m : ℕ) (hm : 0 < m), M ≤ m →
        let μ := P.map B.path
        let r := fractionalRate h ν m
        ENNReal.ofReal (c₁*r)/2 ≤ quantizationQ1 μ m hm ∧
        ENNReal.ofReal (c₂*r)/2 ≤ quantizationQ2 μ m hm ∧
        quantizationQ1 μ m hm ≤ quantizationQ2 μ m hm ∧
        quantizationQ2 μ m hm ≤ ENNReal.ofReal (C*r) ∧
        ENNReal.ofReal (c₂*r)/2 ≤ expectedEmpiricalWassersteinTwo μ m hm ∧
        expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal (C*r) ∧
        (c₂*r)/2 ≤ (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ∧
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ≤ C*r

/-- Full two-sided quantization and empirical W₂ rate for fractional sheets,
including both ENNReal expected error and ordinary real expected error. -/
theorem fractional_quantization_results
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    FractionalQuantizationStatement hd H hH h ν hν hmin := by
  classical
  obtain ⟨M₁,c₁,hc₁,hq₁⟩ :=
    AlignmentPaperQuantizationLowerUniversal.fractionalSheetQ1_lower_rate hd H hH h ν hν hmin
  obtain ⟨M₂,c₂,hc₂,hq₂⟩ :=
    AlignmentPaperQuantizationLowerUniversal.fractionalSheetQ2_lower_rate hd H hH h ν hν hmin
  obtain ⟨C,hC,M₃,hM₃,hupper⟩ :=
    fractionalSheet_expected_empirical_upper hd H hH h ν hν hmin
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by
    rw [hmin.2]
    omega : 0 < (Finset.univ.filter (fun i : Fin d => H i = h)).card)
  have hh : 0 < h := by rw [← (Finset.mem_filter.mp hi).2]; exact (hH i).1
  let M := max (max M₁ M₂) (max M₃ 3)
  refine ⟨c₁,c₂,C,hc₁,hc₂,hC,M,?_,?_⟩
  · dsimp [M]
    omega
  · intro Ω _ P hP B hBH m hm hM
    letI : IsProbabilityMeasure P := hP
    let μ : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) := P.map B.path
    let r : ℝ := fractionalRate h ν m
    have hm3 : 3 ≤ m := by dsimp [M] at hM; omega
    have hr : 0 ≤ r := fractionalRate_nonneg hh hm3
    have hM₁ : M₁ ≤ m := by dsimp [M] at hM; omega
    have hM₂ : M₂ ≤ m := by dsimp [M] at hM; omega
    have hM₃ : M₃ ≤ m := by dsimp [M] at hM; omega
    have hlow₁ := hq₁ B hBH m hM₁ hm
    have hlow₂ := hq₂ B hBH m hM₂ hm
    have heq₁ := fractionalRadius_eq hh (by omega : 1 ≤ ν) (ν:=ν) (m:=m) c₁
    have heq₂ := fractionalRadius_eq hh (by omega : 1 ≤ ν) (ν:=ν) (m:=m) c₂
    have hlow₁' : ENNReal.ofReal (c₁*r)/2 ≤ quantizationQ1 μ m hm := by
      rw [← heq₁]
      simpa [μ] using hlow₁
    have hlow₂' : ENNReal.ofReal (c₂*r)/2 ≤ quantizationQ2 μ m hm := by
      rw [← heq₂]
      simpa [μ] using hlow₂
    have hupper' := hupper B hBH m hm hM₃
    have hrateeq : C*r = C * (Real.log (m:ℝ))^(-h) *
        (Real.log (Real.log (m:ℝ)))^(h*((ν-1:ℕ):ℝ)+(ν:ℝ)/2) := by
      dsimp [r, fractionalRate]
      ring
    have hupper' : expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal (C*r) := by
      rw [hrateeq]
      simpa [μ] using hupper'
    have hchain := quantization_le_expectedEmpiricalWassersteinTwo μ m hm
    obtain ⟨M4,hM4top,hM4le⟩ :=
      AlignmentPaperContinuousGaussianFernique.centeredGaussian_path_fourth_lintegral_finite
      B.path B.measurable_path B.gaussian B.mean_zero
    have hfour : (∫⁻ f : C(HaarQuarter.BrownianCubeAnchor d,ℝ),
        edist f 0 ^ (4:ℕ) ∂μ) ≠ ⊤ := by
      exact ne_top_of_le_ne_top hM4top hM4le
    have hsecond := AlignmentPaperMomentComparison.second_moment_ne_top_of_fourth μ 0 hfour
    have hCr : 0 ≤ C*r := mul_nonneg hC.le hr
    have hreal := ordinary_empirical_integral_le_of_lintegral μ m hm hsecond hCr hupper'
    have hreal' : (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
        empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ≤ C*r := by
      simpa [μ] using hreal
    have hEfinite : expectedEmpiricalWassersteinTwo μ m hm ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper'
    have hq2finite : quantizationQ2 μ m hm ≠ ⊤ :=
      ne_top_of_le_ne_top hEfinite hchain.2
    have hlow₂of : ENNReal.ofReal (c₂*r) / ENNReal.ofReal (2:ℝ) ≤
        quantizationQ2 μ m hm := by simpa using hlow₂'
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)] at hlow₂of
    have hlowto := ENNReal.toReal_mono hq2finite hlow₂of
    have hlowQ : (c₂*r)/2 ≤ (quantizationQ2 μ m hm).toReal := by
      rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hc₂.le hr) (by norm_num))] at hlowto
      exact hlowto
    have hq2toE := ENNReal.toReal_mono hEfinite hchain.2
    have hrealEq := integral_empiricalWassersteinReal_eq_toReal_lintegral μ 0 hsecond hm
    have hrealEq' :
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) =
          (expectedEmpiricalWassersteinTwo μ m hm).toReal := by
      simpa [expectedEmpiricalWassersteinTwo] using hrealEq
    have hlowReal : (c₂*r)/2 ≤
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) := by
      rw [hrealEq']
      exact le_trans hlowQ hq2toE
    exact ⟨hlow₁',hlow₂',hchain.1,(hchain.2.trans hupper'),
      hlow₂'.trans hchain.2,hupper',hlowReal,hreal'⟩

def brownianRate (d m : ℕ) : ℝ :=
  (Real.log (m:ℝ)) ^ (-(1/2:ℝ)) *
    (Real.log (Real.log (m:ℝ))) ^ (((2*d-1:ℕ):ℝ)/2)

def BrownianQuantizationStatement {d : ℕ} (hd : 2 ≤ d) : Prop :=
∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ) (hm : 0 < m), M ≤ m →
        let μ := P.map B.path
        let r := brownianRate d m
        ENNReal.ofReal (c₁*r)/2 ≤ quantizationQ1 μ m hm ∧
        ENNReal.ofReal (c₂*r)/2 ≤ quantizationQ2 μ m hm ∧
        quantizationQ1 μ m hm ≤ quantizationQ2 μ m hm ∧
        quantizationQ2 μ m hm ≤ ENNReal.ofReal (C*r) ∧
        ENNReal.ofReal (c₂*r)/2 ≤ expectedEmpiricalWassersteinTwo μ m hm ∧
        expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal (C*r) ∧
        (c₂*r)/2 ≤ (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ∧
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ≤ C*r

/-- Brownian-sheet specialization of the full quantization and empirical
W₂ comparison. -/
theorem brownian_quantization_results {d : ℕ} (hd : 2 ≤ d) :
    BrownianQuantizationStatement hd := by
  classical
  let H : Fin d → ℝ := fun _ => 1/2
  have hH : ∀ i, 0 < H i ∧ H i < 1 := by intro i; dsimp [H]; norm_num
  have hmin : Latest.minimumMultiplicity H (1/2) d := by
    constructor
    · intro i
      simp [H]
    · simp [H, Latest.minimumMultiplicity]
  obtain ⟨c₁,c₂,C,hc₁,hc₂,hC,M,hM,hfrac⟩ :=
    fractional_quantization_results hd H hH (1/2) d (by omega) hmin
  refine ⟨c₁,c₂,C,hc₁,hc₂,hC,M,hM,?_⟩
  intro Ω _ P hP B m hm hM'
  letI : IsProbabilityMeasure P := hP
  let BF := FractionalBrownianSheetOnCube.ofBrownian B
  have hh : BF.H = H := rfl
  have h := hfrac BF hh m hm hM'
  have hexp : (1/2:ℝ)*((d-1:ℕ):ℝ)+(d:ℝ)/2 = ((2*d-1:ℕ):ℝ)/2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : 1 ≤ 2*d)]
    push_cast
    ring_nf
  have hexp' : (2:ℝ)⁻¹*((d-1:ℕ):ℝ)+(d:ℝ)/2 =
      ((2*d-1:ℕ):ℝ)/2 := by simpa [one_div] using hexp
  simp only [fractionalRate, one_div, hexp'] at h
  simpa [brownianRate, BF, FractionalBrownianSheetOnCube.ofBrownian] using h

def integratedCommonRate (q d m : ℕ) : ℝ :=
  (Real.log (m:ℝ)) ^ (-((q:ℝ)+(1/2:ℝ))) *
    (Real.log (Real.log (m:ℝ))) ^ (((q+1:ℕ):ℝ)*(d-1:ℕ)+1/2)

private theorem integratedRadius_eq {q d m : ℕ} (hd : 2 ≤ d) (c : ℝ) :
    canonicalPowerlogRadius (2/(2*(q:ℝ)+1))
      (((d-1:ℕ):ℝ)+(d:ℝ)/(2*(q:ℝ)+1)) c (Real.log (m:ℝ)) =
      c * integratedCommonRate q d m := by
  rw [canonicalPowerlogRadius]
  have hden : 0 < 2*(q:ℝ)+1 := by positivity
  have he1 : -(1/(2/(2*(q:ℝ)+1))) = -((q:ℝ)+(1/2:ℝ)) := by
    field_simp [ne_of_gt hden]
  have he2 : (((d-1:ℕ):ℝ)+(d:ℝ)/(2*(q:ℝ)+1))/(2/(2*(q:ℝ)+1)) =
      ((q+1:ℕ):ℝ)*((d-1:ℕ):ℝ)+(1/2:ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    field_simp [ne_of_gt hden]
    ring_nf
  simp [he1, he2, integratedCommonRate]
  ring_nf

private theorem integratedCommonRate_nonneg {q d m : ℕ}
    (hm : 3 ≤ m) : 0 ≤ integratedCommonRate q d m := by
  have hm1 : 1 < (m:ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hloggt1 : 1 < Real.log (m:ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans_le hm3)
  dsimp [integratedCommonRate]
  apply mul_nonneg
  · exact Real.rpow_nonneg (Real.log_nonneg hm1.le) _
  · exact Real.rpow_nonneg (Real.log_pos hloggt1).le _

def IntegratedQuantizationStatement {d : ℕ} (hd : 2 ≤ d) (q : ℕ) : Prop :=
∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ) (hm : 0 < m), M ≤ m →
        let μ := P.map (fun ω => integrateSheetPath (fun _ : Fin d => q) (B.path ω))
        let r := integratedCommonRate q d m
        ENNReal.ofReal (c₁*r)/2 ≤ quantizationQ1 μ m hm ∧
        ENNReal.ofReal (c₂*r)/2 ≤ quantizationQ2 μ m hm ∧
        quantizationQ1 μ m hm ≤ quantizationQ2 μ m hm ∧
        quantizationQ2 μ m hm ≤ ENNReal.ofReal (C*r) ∧
        ENNReal.ofReal (c₂*r)/2 ≤ expectedEmpiricalWassersteinTwo μ m hm ∧
        expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal (C*r) ∧
        (c₂*r)/2 ≤ (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ∧
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ≤ C*r

/-- Full two-sided quantization and empirical W₂ rate for common-integer
integrated sheets, including both ENNReal and ordinary real expected error. -/
theorem integrated_common_quantization_results {d : ℕ} (hd : 2 ≤ d) (q : ℕ) :
    IntegratedQuantizationStatement hd q := by
  classical
  let orders : Fin d → ℕ := fun _ => q
  have hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ)) (q:ℝ) d := by
    constructor
    · intro i
      simp [orders]
    · simp [orders, Latest.minimumMultiplicity]
  obtain ⟨M₁,c₁,hc₁,hq₁⟩ :=
    AlignmentPaperQuantizationLowerUniversal.integratedSheetQ1_lower_rate hd orders q d (by omega) hmin
  obtain ⟨M₂,c₂,hc₂,hq₂⟩ :=
    AlignmentPaperQuantizationLowerUniversal.integratedSheetQ2_lower_rate hd orders q d (by omega) hmin
  obtain ⟨C,hC,M₃,hM₃,hupper⟩ :=
    integrated_common_expected_empirical_upper hd q
  let M := max (max M₁ M₂) (max M₃ 3)
  refine ⟨c₁,c₂,C,hc₁,hc₂,hC,M,?_,?_⟩
  · dsimp [M]
    omega
  · intro Ω _ P hP B m hm hM
    letI : IsProbabilityMeasure P := hP
    let μ : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) :=
      P.map (fun ω => integrateSheetPath orders (B.path ω))
    let μB : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) := P.map B.path
    have hlaw := BrownianSharp.AlignmentPaperGaussianPathLaws.isCenteredPathLaw_map
      B.path B.measurable_path B.gaussian B.mean_zero
      (fun x y => ∏ i, min (x.val i) (y.val i)) B.covariance
    let Bcanon : HaarQuarter.BrownianSheetOnCube d
        (C(HaarQuarter.BrownianCubeAnchor d,ℝ)) μB := {
      B with
      path := id
      measurable_path := measurable_id
      gaussian := hlaw.2.1
      mean_zero := hlaw.2.2.1
      covariance := hlaw.2.2.2 }
    let r : ℝ := integratedCommonRate q d m
    have hm3 : 3 ≤ m := by dsimp [M] at hM; omega
    have hr : 0 ≤ r := integratedCommonRate_nonneg hm3
    have hM₁ : M₁ ≤ m := by dsimp [M] at hM; omega
    have hM₂ : M₂ ≤ m := by dsimp [M] at hM; omega
    have hM₃ : M₃ ≤ m := by dsimp [M] at hM; omega
    have hlow₁ := hq₁ B m hM₁ hm
    have hlow₂ := hq₂ B m hM₂ hm
    have heq₁ := integratedRadius_eq hd (q:=q) (d:=d) (m:=m) c₁
    have heq₂ := integratedRadius_eq hd (q:=q) (d:=d) (m:=m) c₂
    have hlow₁' : ENNReal.ofReal (c₁*r)/2 ≤ quantizationQ1 μ m hm := by
      rw [← heq₁]
      simpa [μ, orders] using hlow₁
    have hlow₂' : ENNReal.ofReal (c₂*r)/2 ≤ quantizationQ2 μ m hm := by
      rw [← heq₂]
      simpa [μ, orders] using hlow₂
    have hupperCanon := hupper Bcanon m hm hM₃
    have hmap : Measurable (fun f : C(HaarQuarter.BrownianCubeAnchor d,ℝ) =>
        integrateSheetPath orders f) := (integrateSheetPath_continuous orders).measurable
    have hupperCanon' : expectedEmpiricalWassersteinTwo
        (μB.map (fun f => integrateSheetPath orders f)) m hm ≤
        ENNReal.ofReal (C * (Real.log (m:ℝ)) ^ (-((q:ℝ)+(1/2:ℝ))) *
          (Real.log (Real.log (m:ℝ))) ^ (((q+1:ℕ):ℝ)*(d-1:ℕ)+1/2)) := by
      simpa [Bcanon] using hupperCanon
    rw [show μB = P.map B.path from rfl] at hupperCanon'
    rw [Measure.map_map hmap B.measurable_path] at hupperCanon'
    have hrateeq : C*r = C *
        (Real.log (m:ℝ)) ^ (-((q:ℝ)+(1/2:ℝ))) *
          (Real.log (Real.log (m:ℝ))) ^ (((q+1:ℕ):ℝ)*(d-1:ℕ)+1/2) := by
      dsimp [r, integratedCommonRate]
      ring
    have hupper' : expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal (C*r) := by
      rw [hrateeq]
      change expectedEmpiricalWassersteinTwo
        (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm ≤ _
      simpa [orders, Function.comp_def] using hupperCanon'
    have hchain := quantization_le_expectedEmpiricalWassersteinTwo μ m hm
    let F : Ω → C(HaarQuarter.BrownianCubeAnchor d,ℝ) := fun ω =>
      integrateSheetPath orders (B.path ω)
    have hF : Measurable F := measurable_integrateBrownianSheetPath B orders
    have hX : IsGaussianProcess (fun x ω => F ω x) P := by
      simpa [F] using AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess B orders
    have hmean : ∀ x, ∫ ω, F ω x ∂P = 0 := by
      intro x
      obtain ⟨T,W,hW,hpath⟩ := AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal B orders
      calc
        _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hpath x)
        _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hW _).symm
        _ = 0 := W.mean_zero _
    obtain ⟨M4,hM4top,hM4le⟩ :=
      AlignmentPaperContinuousGaussianFernique.centeredGaussian_path_fourth_lintegral_finite
        F hF hX hmean
    have hfour : (∫⁻ f : C(HaarQuarter.BrownianCubeAnchor d,ℝ),
        edist f 0 ^ (4:ℕ) ∂μ) ≠ ⊤ := ne_top_of_le_ne_top hM4top hM4le
    have hsecond := AlignmentPaperMomentComparison.second_moment_ne_top_of_fourth μ 0 hfour
    have hCr : 0 ≤ C*r := mul_nonneg hC.le hr
    have hreal := ordinary_empirical_integral_le_of_lintegral μ m hm hsecond hCr hupper'
    have hreal' : (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
        empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) ≤ C*r := by
      simpa [μ] using hreal
    have hEfinite : expectedEmpiricalWassersteinTwo μ m hm ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper'
    have hq2finite : quantizationQ2 μ m hm ≠ ⊤ :=
      ne_top_of_le_ne_top hEfinite hchain.2
    have hlow₂of : ENNReal.ofReal (c₂*r)/ENNReal.ofReal (2:ℝ) ≤ quantizationQ2 μ m hm := by
      simpa only [ENNReal.ofReal_ofNat] using hlow₂'
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)] at hlow₂of
    have hlowto := ENNReal.toReal_mono hq2finite hlow₂of
    have hlowQ : (c₂*r)/2 ≤ (quantizationQ2 μ m hm).toReal := by
      rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hc₂.le hr) (by norm_num))] at hlowto
      exact hlowto
    have hq2toE := ENNReal.toReal_mono hEfinite hchain.2
    have hrealEq := integral_empiricalWassersteinReal_eq_toReal_lintegral μ 0 hsecond hm
    have hrealEq' :
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) =
          (expectedEmpiricalWassersteinTwo μ m hm).toReal := by
      simpa [expectedEmpiricalWassersteinTwo] using hrealEq
    have hlowReal : (c₂*r)/2 ≤
        (∫ x : Fin m → C(HaarQuarter.BrownianCubeAnchor d,ℝ),
          empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) := by
      rw [hrealEq']
      exact le_trans hlowQ hq2toE
    exact ⟨hlow₁',hlow₂',hchain.1,(hchain.2.trans hupper'),
      hlow₂'.trans hchain.2,hupper',hlowReal,hreal'⟩

/-- Public all-family quantization result bundle. -/
def PaperQuantizationResultsStatement : Prop :=
  (∀ {d : ℕ} (hd : 2 ≤ d), BrownianQuantizationStatement.{u} hd) ∧
  (∀ {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν),
    FractionalQuantizationStatement.{u} hd H hH h ν hν hmin) ∧
  (∀ {d : ℕ} (hd : 2 ≤ d) (q : ℕ), IntegratedQuantizationStatement.{u} hd q)

theorem paperQuantizationResultsStatement : PaperQuantizationResultsStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd; exact brownian_quantization_results hd
  · intro d hd H hH h ν hν hmin; exact fractional_quantization_results hd H hH h ν hν hmin
  · intro d hd q; exact integrated_common_quantization_results hd q

end BrownianSharp.AlignmentPaperQuantizationSheetFinal
