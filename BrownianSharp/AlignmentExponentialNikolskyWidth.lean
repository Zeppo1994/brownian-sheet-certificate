import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.AlignmentPeriodicTail
import BrownianSharp.AlignmentPeriodicWidthUniformUpper

/-! Gradewise scaling interface for the periodic KGG construction.  It lets a
Nikolsky block use its natural `sqrt(number of shapes)` source norm rather than
the global Sobolev source norm. -/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace BrownianSharp.AlignmentExponentialNikolskyWidth

open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.AlignmentTorusSampling
open BrownianSharp.AlignmentPeriodicWidthLayerAlgebra
open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.AlignmentPeriodicWidthRealification
open BrownianSharp.AlignmentPeriodicRealEnergy
open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.AlignmentPeriodicTail
open BrownianSharp.AlignmentPeriodicWidthUniformUpper
open BrownianSharp.AlignmentAmbientWidth
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open BrownianSharp.AtomicBlockKernelL2
open HaarQuarter
open HaarQuarter.TheoremD.Width

theorem partition_geometric_hilbert_layer_approximation_scaled
    {α I G : Type} [TopologicalSpace α] [CompactSpace α]
    [Fintype I] [Fintype G]
    (v : α → EuclideanSpace ℝ I)
    (φ : G → C(α, ℝ)) (a : G → α)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {L : ℕ} (σ : I → Option (Fin L)) (R : Fin L → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g, ‖coordinateLayerMask σ (some j) (v (a g))‖ ≤ R j)
    {A₀ ρ q : ℝ} {k : ℕ} (hA₀ : 0 ≤ A₀)
    (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q)
    (henergy : ∀ j, (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val))
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : I // σ i = none} ≤ D)
    {δ B : ℝ} (hB : 0 < B)
    (hosc : ∀ i t, φ i t ≠ 0 → ‖v t-v (a i)‖ ≤ δ) :
    ∃ W : Submodule ℝ C(α, ℝ),
      Module.rank ℝ W ≤ (D*Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ B → ∃ y ∈ W,
        ∀ t, |⟪x,v t⟫ - y t| ≤ B * (δ + Real.sqrt (
          (4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) k)) := by
  obtain ⟨W, hWrank, hWapprox⟩ :=
    partition_geometric_hilbert_layer_approximation
      v φ a hφ hsum σ R hR hrow hA₀ hρ hq hq1 hρq henergy D hD hlow hosc
  refine ⟨W, hWrank, ?_⟩
  intro x hx
  have hx' : ‖(B⁻¹) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    have hmul := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hB.le)
    have hcancel : B⁻¹ * B = 1 := by field_simp
    nlinarith [hmul]
  obtain ⟨y, hy, hyerr⟩ := hWapprox ((B⁻¹) • x) hx'
  refine ⟨B • y, W.smul_mem B hy, ?_⟩
  intro t
  have hscale : ⟪(B⁻¹) • x, v t⟫ = B⁻¹ * ⟪x, v t⟫ := by
    rw [real_inner_smul_left]
  have hnorm : |B⁻¹ * ⟪x, v t⟫ - y t| ≤
      δ + Real.sqrt ((4*(10000:ℝ)^2*A₀*Real.log
        (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) * polynomialBudget (ρ/q) k) := by
    simpa [hscale] using hyerr t
  have hrewrite : ⟪x, v t⟫ - B * y t = B * (B⁻¹ * ⟪x, v t⟫ - y t) := by
    field_simp
  change |⟪x, v t⟫ - B * y t| ≤ _
  rw [hrewrite, abs_mul, abs_of_pos hB]
  exact mul_le_mul_of_nonneg_left hnorm hB.le

/-- A Nikolsky-2 source restricted to one dyadic shape grade has Euclidean
coefficient norm at most the square root of the number of shapes. -/
theorem nikolsky_source_vector_norm_le_of_grade
    {d : ℕ} (hd : 0 < d) (S : Finset (Fin d → ℕ)) (r : ℝ)
    (f : RealPeriodic d) (hf : NikolskyUnitBall (2:ENNReal) r f)
    (n : ℕ) (hgrade : ∀ s ∈ S, (∑ i, s i) = n)
    (hcard : S.card ≤ (n+1)^(d-1)) :
    ‖periodicSourceVector S r f‖ ≤ Real.sqrt (((n+1:ℕ):ℝ)^(d-1)) := by
  classical
  change BesovUnitBall (2:ENNReal) r ⊤ f at hf
  simp only [BesovUnitBall, ↓reduceIte] at hf
  have henergy : ∀ s ∈ S, realBlockEnergy r f s ≤ 1 := by
    intro s hs
    rw [realBlockEnergy_eq_toReal]
    have hnorm : weightedBlockNorm 2 r s f ≤ 1 := hf s
    have hpow' : (weightedBlockNorm 2 r s f)^2 ≤ (1:ENNReal)^2 :=
      pow_le_pow_left₀ (by positivity) hnorm 2
    have hpow : (weightedBlockNorm 2 r s f)^2 ≤ (1:ENNReal) := by
      simpa using hpow'
    simpa using ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) hpow
  have hnormsq : ‖periodicSourceVector S r f‖^2 ≤ ((n+1:ℕ):ℝ)^(d-1) := by
    rw [periodicSourceVector_norm_sq]
    calc
      ∑ s ∈ S, realBlockEnergy r f s ≤ ∑ s ∈ S, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        exact henergy s hs
      _ = (S.card:ℝ) := by simp
      _ ≤ ((n+1:ℕ):ℝ)^(d-1) := by exact_mod_cast hcard
  have hnonneg : 0 ≤ ((n+1:ℕ):ℝ)^(d-1) := by positivity
  have hsqrt : Real.sqrt (((n+1:ℕ):ℝ)^(d-1)) ^ 2 =
      ((n+1:ℕ):ℝ)^(d-1) := Real.sq_sqrt hnonneg
  have hnorm_nonneg := norm_nonneg (periodicSourceVector S r f)
  exact (sq_le_sq₀ hnorm_nonneg (Real.sqrt_nonneg _)).1 (by nlinarith)

theorem periodic_grade_shape_card_le {d : ℕ} (hd : 0<d)
    (S : Finset (Fin d → ℕ)) (n : ℕ)
    (hgrade : ∀ s ∈ S, (∑ i, s i) = n) :
    S.card ≤ (n+1)^(d-1) := by
  have hfilter : S.filter (fun s => (∑ i, s i) = n) = S := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hs
      exact ⟨hs, hgrade s hs⟩
  rw [← hfilter]
  exact shape_grade_card_le_power_pred hd S n

theorem nikolsky_source_vector_norm_le_sqrt_card
    {d : ℕ} (S : Finset (Fin d → ℕ)) (r : ℝ)
    (f : RealPeriodic d) (hf : NikolskyUnitBall (2:ENNReal) r f) :
    ‖periodicSourceVector S r f‖ ≤ Real.sqrt (S.card:ℝ) := by
  classical
  change BesovUnitBall (2:ENNReal) r ⊤ f at hf
  simp only [BesovUnitBall, ↓reduceIte] at hf
  have henergy : ∀ s ∈ S, realBlockEnergy r f s ≤ 1 := by
    intro s hs
    rw [realBlockEnergy_eq_toReal]
    have hnorm : weightedBlockNorm 2 r s f ≤ 1 := hf s
    have hpow' : (weightedBlockNorm 2 r s f)^2 ≤ (1:ENNReal)^2 :=
      pow_le_pow_left₀ (by positivity) hnorm 2
    have hpow : (weightedBlockNorm 2 r s f)^2 ≤ (1:ENNReal) := by simpa using hpow'
    simpa using ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) hpow
  have hnormsq : ‖periodicSourceVector S r f‖^2 ≤ (S.card:ℝ) := by
    rw [periodicSourceVector_norm_sq]
    calc
      ∑ s ∈ S, realBlockEnergy r f s ≤ ∑ s ∈ S, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        exact henergy s hs
      _ = (S.card:ℝ) := by simp
  have hnonneg : 0 ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (S.card:ℝ)^2 = (S.card:ℝ) := Real.sq_sqrt hnonneg
  have hnorm_nonneg := norm_nonneg (periodicSourceVector S r f)
  exact (sq_le_sq₀ hnorm_nonneg (Real.sqrt_nonneg _)).1 (by nlinarith)

/-- Low-grade Nikolsky blocks are handled with all feature coordinates in the
exact (uncompressed) layer of the partition dictionary. -/
theorem periodic_nikolsky_low_blocks_KGG
    {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (r : ℝ)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d),ℝ))
    (a : G → UnitAddTorus (Fin d))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector (periodicShapeSimplex (M-1)) r t -
        periodicFeatureVector (periodicShapeSimplex (M-1)) r (a i)‖ ≤ δ) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤
        (2*5^d*(M+1)^(d-1)*2^M * Nat.ceil (1+(1-(3/4:ℝ))⁻¹):Cardinal) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |(∑ s ∈ periodicShapeSimplex (M-1), (block s f t).re)-y t| ≤
          Real.sqrt (((M+1:ℕ):ℝ)^d) * δ := by
  classical
  let S : Finset (Fin d → ℕ) := periodicShapeSimplex (d:=d) (M-1)
  let σ : (FourierCoeffIndex S × Fin 2) → Option (Fin 1) := fun _ => none
  let R : Fin 1 → ℝ := fun _ => 0
  let A₀ : ℝ := 0
  let D : ℕ := 2*5^d*(M+1)^(d-1)*2^M
  have hD : 0 < D := by dsimp [D]; positivity
  have hlow : Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i = none} ≤ D := by
    have hbelow : ∀ i : FourierCoeffIndex S × Fin 2, σ i = none →
        coefficientGrade i.1 < M := by
      intro i hi
      have hs := i.1.1.2
      have hgrade := (mem_periodicShapeSimplex i.1.1.1).1 hs
      dsimp [S, coefficientGrade]
      omega
    have hbelowNat : ∀ i : FourierCoeffIndex S × Fin 2,
        (fun _ : FourierCoeffIndex S × Fin 2 => (none : Option ℕ)) i = none →
          coefficientGrade i.1 < M := by
      intro i hi
      exact hbelow i (by simpa [σ] using hi)
    have hcount := periodic_low_frequency_card_le_sharp hd S
      (fun _ : FourierCoeffIndex S × Fin 2 => (none : Option ℕ)) hbelowNat
    simpa [D, σ] using hcount
  have hR : ∀ j : Fin 1, 0 ≤ R j := by intro j; simp [R]
  have hrow : ∀ j g, ‖coordinateLayerMask σ (some j) (periodicFeatureVector S r (a g))‖ ≤ R j := by
    intro j g
    have hz : coordinateLayerMask σ (some j) (periodicFeatureVector S r (a g)) = 0 := by
      ext i
      simp [σ, coordinateLayerMask_apply]
    rw [hz]
    simp [R]
  have hA₀ : 0 ≤ A₀ := by simp [A₀]
  have henergy : ∀ j : Fin 1,
      (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^(d-1)*(1/2:ℝ)^(j.val) := by
    intro j
    simp [R, A₀]
  have hlowcard : S.card ≤ (M+1)^d := by
    have hsub : S ⊆ periodicShapeBox M := by
      intro s hs
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Finset.mem_range.mpr
      have hsumgrade := (mem_periodicShapeSimplex s).1 hs
      have hcoord := Finset.single_le_sum
        (fun j hj => Nat.zero_le (s j)) (Finset.mem_univ i)
      have hlt : s i < M := by omega
      omega
    calc
      S.card ≤ (periodicShapeBox M).card := Finset.card_le_card hsub
      _ = (M+1)^d := by simp [periodicShapeBox]
  have hB : 0 < Real.sqrt (((M+1:ℕ):ℝ)^d) := by positivity
  obtain ⟨W,hWrank,happrox⟩ :=
    partition_geometric_hilbert_layer_approximation_scaled
      (fun x => periodicFeatureVector S r x) φ a hφ hsum σ R hR hrow
      (A₀:=A₀) (ρ:=1/2) (q:=3/4) (k:=d-1) hA₀ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) henergy D hD hlow hB hosc
  refine ⟨W, ?_, ?_⟩
  · simpa [D, Nat.cast_mul, Nat.cast_add] using hWrank
  intro f hf
  have hsource0 := nikolsky_source_vector_norm_le_sqrt_card S r f hf
  have hsource : ‖periodicSourceVector S r f‖ ≤ Real.sqrt (((M+1:ℕ):ℝ)^d) := by
    calc
      _ ≤ Real.sqrt (S.card:ℝ) := hsource0
      _ ≤ Real.sqrt (((M+1:ℕ):ℝ)^d) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hlowcard)
  obtain ⟨y,hy,hyerr⟩ := happrox (periodicSourceVector S r f) hsource
  refine ⟨y,hy,?_⟩
  intro t
  have hpair := periodicSourceVector_feature_pairing S r f t
  have herr := hyerr t
  change |⟪periodicSourceVector S r f, periodicFeatureVector S r t⟫ - y t| ≤ _ at herr
  rw [hpair] at herr
  simpa [A₀, hδ] using herr

/-- One shared quantitative torus partition controls every feature vector
whose shapes have grade at most `T`, including all exact-grade projections. -/
theorem periodic_nikolsky_grid_oscillation_of_support
    {d T H K : ℕ} (r : ℝ) (hr : 0 ≤ r) (hK : 0 < K)
    (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    {S : Finset (Fin d → ℕ)}
    (hSgrade : ∀ s ∈ S, (∑ i, s i) ≤ T)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d),ℝ))
    (a : G → UnitAddTorus (Fin d))
    (hsupport : ∀ i t, φ i t ≠ 0 →
      dist t (a i) <
        2/((AlignmentTorusSampling.samplingGridSize d K T H):ℝ)) :
    ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector S r t-periodicFeatureVector S r (a i)‖ ≤
        ((2:ℝ)^H)⁻¹ := by
  intro i t hne
  have hdist : dist t (a i) ≤
      2/((AlignmentTorusSampling.samplingGridSize d K T H:ℕ):ℝ) :=
    (hsupport i t hne).le
  have hlip := periodicFeatureLipschitzConstant_exp_bound S r hr hSgrade
  have hbound :
      periodicFeatureLipschitzConstant S r * dist t (a i) ≤ ((2:ℝ)^H)⁻¹ := by
    calc
      _ ≤ (AlignmentTorusSampling.samplingConstant d *
          (2:ℝ)^((d+2)*T)) *
          (2/((AlignmentTorusSampling.samplingGridSize d K T H:ℕ):ℝ)) := by
        exact mul_le_mul hlip hdist (dist_nonneg)
          (by unfold AlignmentTorusSampling.samplingConstant; positivity)
      _ ≤ _ := by
        have hKreal : 0 < (K:ℝ) := by exact_mod_cast hK
        have hratio : 2*AlignmentTorusSampling.samplingConstant d/(K:ℝ) ≤ 1 :=
          (div_le_one hKreal).2 hKC
        have hcast :
            ((AlignmentTorusSampling.samplingGridSize d K T H:ℕ):ℝ) =
              (K:ℝ)*(2:ℝ)^((d+2)*T+H) := by
          simp [AlignmentTorusSampling.samplingGridSize, Nat.cast_mul]
        rw [hcast]
        have hfactor :
            AlignmentTorusSampling.samplingConstant d * (2:ℝ)^((d+2)*T) *
                (2/((K:ℝ)*(2:ℝ)^((d+2)*T+H))) =
              (2*AlignmentTorusSampling.samplingConstant d/(K:ℝ)) *
                ((2:ℝ)^H)⁻¹ := by
          field_simp
          rw [pow_add]
          ring
        rw [hfactor]
        calc
          _ ≤ 1 * ((2:ℝ)^H)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr (by positivity))
          _ = _ := by simp
  exact (periodicFeature_dist_bound S r t (a i)).trans hbound

theorem periodic_nikolsky_grid_oscillation
    {d T H K : ℕ} (hd : 0 < d) (r : ℝ) (hr : 0 ≤ r)
    (hK : 0 < K)
    (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    (S : Finset (Fin d → ℕ))
    (hSgrade : ∀ s ∈ S, (∑ i, s i) ≤ T) :
    ∃ φ : (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)) →
        C(UnitAddTorus (Fin d),ℝ),
      (∀ i t, 0 ≤ φ i t) ∧ (∀ t, ∑ i, φ i t = 1) ∧
      (∀ i t, φ i t ≠ 0 →
        dist t (AlignmentTorusSampling.torusGridPoint i) <
          2/((AlignmentTorusSampling.samplingGridSize d K T H:ℕ):ℝ)) ∧
      ∀ i t, φ i t ≠ 0 →
        ‖periodicFeatureVector S r t - periodicFeatureVector S r
          (AlignmentTorusSampling.torusGridPoint i)‖ ≤ ((2:ℝ)^H)⁻¹ := by
  classical
  let N := AlignmentTorusSampling.samplingGridSize d K T H
  have hN : 0 < N := AlignmentTorusSampling.samplingGridSize_pos hK
  obtain ⟨φ,hφ,hsum,hsupport⟩ :=
    AlignmentTorusSampling.torus_grid_partition (d:=d) N hN
  have hosc := periodic_nikolsky_grid_oscillation_of_support r hr hK hKC
    hSgrade φ AlignmentTorusSampling.torusGridPoint hsupport
  exact ⟨φ,hφ,hsum,hsupport,hosc⟩

/-- Continuous-function KGG approximation for one exact Nikolsky-2 shape
grade.  The source norm contribution is the square root of the grade's shape
count, which is the factor needed in the sharp all-grade logarithmic rate. -/
theorem periodic_nikolsky_single_grade_KGG
    {d : ℕ} (hd : 0<d) (S : Finset (Fin d → ℕ)) (r : ℝ)
    (n : ℕ) (hgrade : ∀ s ∈ S, (∑ i, s i) = n)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d), ℝ))
    (a : G → UnitAddTorus (Fin d))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ}
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector S r t-periodicFeatureVector S r (a i)‖ ≤ δ)
    {q ρ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (D : ℕ) (hD : 0 < D) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤ (D*Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |(∑ s ∈ S, (block s f t).re)-y t| ≤
          Real.sqrt (((n+1:ℕ):ℝ)^(d-1)) *
          (δ + Real.sqrt ((4*(10000:ℝ)^2 *
            (2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n) *
            Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) (d-1))) := by
  classical
  let σ : (FourierCoeffIndex S × Fin 2) → Option (Fin 1) := fun _ => some 0
  let N : ℕ := 2*5^d*2^n*(n+1)^(d-1)
  let R : Fin 1 → ℝ := fun _ =>
    Real.sqrt (N:ℝ)*(2:ℝ)^(-r*(n:ℝ))
  let A₀ : ℝ := 2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n
  have hshape := periodic_grade_shape_card_le hd S n hgrade
  have hshapeFiltered := shape_grade_card_le_power_pred hd S n
  have hsiggrade : ∀ i k, σ i = some k → coefficientGrade i.1 = n := by
    intro i k hi
    have hk : k = 0 := by simpa [σ] using hi.symm
    subst k
    simpa [coefficientGrade] using hgrade i.1.1.1 i.1.1.2
  let σNat : (FourierCoeffIndex S × Fin 2) → Option ℕ := fun _ => some 0
  have hcountNat :
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 =>
        σNat i = some 0)).card ≤ N := by
    have h := periodic_grade_coordinate_count_le S hd
      σNat n (by
        intro i k hk
        have hk0 : k = 0 := by simpa [σNat] using hk.symm
        subst k
        simpa [coefficientGrade] using hgrade i.1.1.1 i.1.1.2)
      0 hshapeFiltered
    simpa [N, σNat, Nat.cast_add] using h
  have hcount :
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 =>
        σ i = some (0:Fin 1))).card ≤ N := by
    simpa [σ, σNat] using hcountNat
  have hrow : ∀ j g,
      ‖coordinateLayerMask σ (some j) (periodicFeatureVector S r (a g))‖ ≤ R j := by
    intro j g
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have hrad := periodicFeature_layer_radius S r (a g) σ (0:Fin 1) n
      (fun i hi => hsiggrade i 0 hi) hcount
    simpa [R, N] using hrad
  have hR : ∀ j : Fin 1, 0 ≤ R j := by intro j; dsimp [R]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have henergy : ∀ j : Fin 1,
      (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val) := by
    intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have hid := periodic_feature_radius_energy_identity d (d-1) n r
    have hid' : (Real.sqrt ((N:ℝ))*(2:ℝ)^(-r*(n:ℝ)))^2 =
        (2*(5:ℝ)^d)*((n+1:ℕ):ℝ)^(d-1)*ρ^n := by
      simpa [N, hρeq, Nat.cast_add] using hid
    simpa [R, A₀] using hid'.le
  have hlow : Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i = none} ≤ D := by
    simp [σ]
  have hB : 0 < Real.sqrt (((n+1:ℕ):ℝ)^(d-1)) := by positivity
  obtain ⟨W,hWrank,happrox⟩ :=
    partition_geometric_hilbert_layer_approximation_scaled
      (fun x => periodicFeatureVector S r x) φ a hφ hsum σ R hR hrow
      (A₀:=A₀) (ρ:=ρ) (q:=q) (k:=d-1) hA₀ hρ hq hq1 hρq henergy
      D hD hlow hB hosc
  refine ⟨W,hWrank,?_⟩
  intro f hf
  have hsource := nikolsky_source_vector_norm_le_of_grade hd S r f hf n hgrade hshape
  obtain ⟨y,hy,hyerr⟩ := happrox (periodicSourceVector S r f) hsource
  refine ⟨y,hy,?_⟩
  intro t
  have hpair := periodicSourceVector_feature_pairing S r f t
  have herr := hyerr t
  change |⟪periodicSourceVector S r f, periodicFeatureVector S r t⟫ - y t| ≤ _ at herr
  rw [hpair] at herr
  simpa [A₀] using herr

/-- Rank of a finite sum of subspaces is at most the sum of their ranks. -/
theorem rank_finset_sup_le_sum
    {J V : Type} [AddCommGroup V] [Module ℝ V]
    (F : Finset J) (W : J → Submodule ℝ V) :
    Module.rank ℝ ↥(Finset.sup F W) ≤ ∑ j ∈ F, Module.rank ℝ (W j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    rw [Finset.sup_insert]
    calc
      Module.rank ℝ ↥(W i ⊔ F.sup W) ≤
          Module.rank ℝ (W i) + Module.rank ℝ ↥(F.sup W) :=
        Submodule.rank_add_le_rank_add_rank _ _
      _ = Module.rank ℝ ↥(F.sup W) + Module.rank ℝ (W i) := by rw [add_comm]
      _ ≤ (∑ j ∈ F, Module.rank ℝ (W j)) + Module.rank ℝ (W i) :=
        by gcongr
      _ = Module.rank ℝ (W i) + ∑ j ∈ F, Module.rank ℝ (W j) := by rw [add_comm]
      _ = ∑ j ∈ insert i F, Module.rank ℝ (W j) := by simp [hi]

/-- Assemble finitely many continuous-function approximants by summing both
their subspaces and their errors. This is the finite-sum step used to combine
the exact Nikolsky shape grades. -/
theorem finite_subspace_approximation_sum
    {α J : Type} [TopologicalSpace α] [Fintype J]
    (F : Finset J) (f : J → C(α,ℝ)) (W : J → Submodule ℝ C(α,ℝ))
    (ε : J → ℝ)
    (happrox : ∀ j ∈ F, ∃ y ∈ W j, ∀ t, |f j t-y t| ≤ ε j) :
    ∃ Wsum : Submodule ℝ C(α,ℝ),
      Module.rank ℝ Wsum ≤ ∑ j ∈ F, Module.rank ℝ (W j) ∧
      ∃ y ∈ Wsum, ∀ t,
        |(∑ j : {j : J // j ∈ F}, f j.1) t-y t| ≤
          ∑ j : {j : J // j ∈ F}, ε j.1 := by
  classical
  let Wsum : Submodule ℝ C(α,ℝ) := Finset.sup F W
  have hrank := rank_finset_sup_le_sum F W
  let JF := {j : J // j ∈ F}
  have happrox' : ∀ j : JF, ∃ y ∈ W j.1, ∀ t, |f j.1 t-y t| ≤ ε j.1 :=
    fun j => happrox j.1 j.2
  choose y hy herr using happrox'
  let ysum : C(α,ℝ) := ∑ j : JF, y j
  have hle : ∀ j ∈ F, W j ≤ Wsum := by
    intro j hj
    exact Finset.le_sup hj
  have hysum : ysum ∈ Wsum := by
    apply Submodule.sum_mem Wsum
    intro j hj
    exact hle j.1 j.2 (hy j)
  refine ⟨Wsum, hrank, ysum, hysum, ?_⟩
  intro t
  change |(∑ j : JF, f j.1) t - ysum t| ≤ ∑ j : JF, ε j.1
  simp only [ysum, ContinuousMap.sum_apply]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : JF, (f j.1 t-(y j) t)| ≤ ∑ j : JF, |f j.1 t-(y j) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : JF, ε j.1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact herr j t

/-- The real continuous component of the finite block sum on one exact grade. -/
noncomputable def periodicGradeBlockComponent
    {d L : ℕ} (S : Finset (Fin d → ℕ)) (f : RealPeriodic d)
    (j : Fin L) : C(UnitAddTorus (Fin d),ℝ) := by
  classical
  refine ⟨fun t => ∑ s ∈ S.filter (fun s => (∑ i, s i) = j.val),
    (block s f t).re, ?_⟩
  apply continuous_finset_sum
  intro s hs
  exact Complex.continuous_re.comp (block s f).continuous

/-- Exact finite grade decomposition of all retained Fourier blocks. -/
theorem periodic_grade_block_components_sum
    {d L : ℕ} (hL : 0<L) (S : Finset (Fin d → ℕ))
    (f : RealPeriodic d) (hgrade : ∀ s ∈ S, (∑ i, s i) < L) :
    ∀ t, (∑ j : Fin L, periodicGradeBlockComponent S f j t) =
      ∑ s ∈ S, (block s f t).re := by
  classical
  intro t
  let g : (Fin d → ℕ) → Fin L := fun s =>
    if hs : (∑ i, s i) < L then ⟨∑ i, s i, hs⟩ else ⟨0, hL⟩
  have hg : ∀ s ∈ S, (g s).val = ∑ i, s i := by
    intro s hs
    simp [g, hgrade s hs]
  have hfilter : S.filter (fun s => g s ∈ (Finset.univ : Finset (Fin L))) = S := by
    ext s
    simp
  have hsum := Finset.sum_fiberwise_eq_sum_filter
    (s := S) (t := (Finset.univ : Finset (Fin L)))
    (g := g) (f := fun s => (block s f t).re)
  rw [hfilter] at hsum
  have hgradeFilter (j : Fin L) :
      S.filter (fun s => (∑ i, s i) = j.val) = S.filter (fun s => g s = j) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hsj⟩
      refine ⟨hs, ?_⟩
      apply Fin.ext
      simpa [hg s hs] using hsj
    · rintro ⟨hs, hsj⟩
      refine ⟨hs, ?_⟩
      have := congrArg Fin.val hsj
      rw [hg s hs] at this
      exact this
  unfold periodicGradeBlockComponent
  simp only [ContinuousMap.coe_mk]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hgradeFilter j]

/-- Combine the exact-grade Nikolsky-2 KGG approximations into a finite
retained-block approximation. The explicit gradewise errors are preserved in
the sum, so subsequent rank allocation does not pay a global Sobolev norm. -/
theorem periodic_nikolsky_finite_block_KGG
    {d L : ℕ} (hd : 0<d) (hL : 0<L) (S : Finset (Fin d → ℕ))
    (r : ℝ)
    (hSgrade : ∀ s ∈ S, (∑ i, s i) < L)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d),ℝ)) (a : G → UnitAddTorus (Fin d))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ j : Fin L, ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector (S.filter (fun s => (∑ k, s k)=j.val)) r t -
        periodicFeatureVector (S.filter (fun s => (∑ k, s k)=j.val)) r (a i)‖ ≤ δ)
    {q ρ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (D : Fin L → ℕ) (hD : ∀ j, 0 < D j) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤ ∑ j : Fin L,
        D j * Nat.ceil (1+(1-q)⁻¹) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |(∑ s ∈ S, (block s f t).re)-y t| ≤
          ∑ j : Fin L,
            if S.filter (fun s => (∑ k, s k)=j.val) = ∅ then 0 else
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
                (δ + Real.sqrt ((4*(10000:ℝ)^2 *
                  (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                  Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                  polynomialBudget (ρ/q) (d-1))) := by
  classical
  let Sj : Fin L → Finset (Fin d → ℕ) := fun j =>
    S.filter (fun s => (∑ k, s k)=j.val)
  let εcore : Fin L → ℝ := fun j =>
    Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
      (δ + Real.sqrt ((4*(10000:ℝ)^2 *
        (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
        Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
        polynomialBudget (ρ/q) (d-1)))
  let ε : Fin L → ℝ := fun j => if Sj j = ∅ then 0 else εcore j
  have hkgg : ∀ j : Fin L,
      ∃ Wj : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
        Module.rank ℝ Wj ≤ (D j * Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
        ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
          ∃ y ∈ Wj, ∀ t, |(∑ s ∈ Sj j, (block s f t).re)-y t| ≤ ε j := by
    intro j
    by_cases hempty : Sj j = ∅
    · refine ⟨⊥, by simp, ?_⟩
      intro f hf
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      intro t
      have hcond : ∀ ⦃x : Fin d → ℕ⦄, x ∈ S → ¬(∑ k, x k) = j.val := by
        intro x hx hgrade
        have hmem : x ∈ Sj j := by simp [Sj, hx, hgrade]
        rw [hempty] at hmem
        simp at hmem
      have hSempty : S.filter (fun s => (∑ k, s k)=j.val) = ∅ := by
        simpa [Sj] using hempty
      have hsumzero : (∑ s ∈ Sj j, (block s f t).re) = 0 := by simp [hempty]
      change |(∑ s ∈ S.filter (fun s => (∑ k, s k)=j.val),
        (block s f t).re) - 0| ≤
          if S.filter (fun s => (∑ k, s k)=j.val) = ∅ then 0 else εcore j
      rw [hSempty]
      simp
    · have hgradej : ∀ s ∈ Sj j, (∑ k, s k)=j.val := by
        intro s hs
        exact (Finset.mem_filter.mp hs).2
      have hsingle := periodic_nikolsky_single_grade_KGG hd (Sj j) r j.val
        hgradej φ a hφ hsum (hosc j) hρ hq hq1 hρq hρeq (D j) (hD j)
      have hcond : ¬ (∀ ⦃x : Fin d → ℕ⦄, x ∈ S → ¬(∑ k, x k) = j.val) := by
        intro hall
        have hnonempty : (Sj j).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        rcases hnonempty with ⟨x,hx⟩
        have hx' := Finset.mem_filter.mp hx
        exact (hall hx'.1) hx'.2
      simpa [ε, εcore, Sj, hcond, periodicGradeBlockComponent, ContinuousMap.coe_mk,
        Nat.cast_add] using hsingle
  choose Wj hWrank hUniform using hkgg
  let Wsum : Submodule ℝ C(UnitAddTorus (Fin d),ℝ) :=
    Finset.sup Finset.univ Wj
  have hWsumRank : Module.rank ℝ Wsum ≤
      ∑ j : Fin L, D j * Nat.ceil (1+(1-q)⁻¹) := by
    have hrank' : Module.rank ℝ Wsum ≤
        ∑ j : Fin L, Module.rank ℝ (Wj j) := by
      simpa [Wsum, Finset.sum_attach] using
        rank_finset_sup_le_sum (Finset.univ : Finset (Fin L)) Wj
    calc
      Module.rank ℝ Wsum ≤ ∑ j : Fin L, Module.rank ℝ (Wj j) := hrank'
      _ ≤ ∑ j : Fin L, (↑(D j * Nat.ceil (1+(1-q)⁻¹)) : Cardinal) := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [Nat.cast_mul] using hWrank j
      _ = ↑(∑ j : Fin L, D j * Nat.ceil (1+(1-q)⁻¹)) := by simp
  refine ⟨Wsum, hWsumRank, ?_⟩
  intro f hf
  let fj : Fin L → C(UnitAddTorus (Fin d),ℝ) := fun j =>
    periodicGradeBlockComponent S f j
  have happrox : ∀ j : Fin L, ∃ y ∈ Wj j, ∀ t, |fj j t-y t| ≤ ε j := by
    intro j
    have h := hUniform j f hf
    simpa [fj, Sj, periodicGradeBlockComponent, ContinuousMap.coe_mk,
      Nat.cast_add] using h
  choose yj hyj herrj using happrox
  let ysum : C(UnitAddTorus (Fin d),ℝ) := ∑ j : Fin L, yj j
  have hle : ∀ j : Fin L, Wj j ≤ Wsum := by
    intro j
    exact Finset.le_sup (Finset.mem_univ j)
  have hysum : ysum ∈ Wsum := by
    apply Submodule.sum_mem Wsum
    intro j hj
    exact hle j (hyj j)
  have hdecomp := periodic_grade_block_components_sum hL S f hSgrade
  refine ⟨ysum,hysum,?_⟩
  intro t
  have herr : |(∑ j : Fin L, fj j t) - ∑ j : Fin L, yj j t| ≤
      ∑ j : Fin L, ε j := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin L, (fj j t-yj j t)| ≤
          ∑ j : Fin L, |fj j t-yj j t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin L, ε j := by
        apply Finset.sum_le_sum
        intro j hj
        exact herrj j t
  have herr' : |(∑ j : Fin L, fj j) t - ysum t| ≤ ∑ j : Fin L, ε j := by
    simpa [ysum, ContinuousMap.sum_apply] using herr
  have hdec := hdecomp t
  dsimp [fj, ε] at herr'
  simp only [ContinuousMap.sum_apply] at herr'
  rw [hdec] at herr'
  simpa [ε, εcore, Sj] using herr'

/-- The omitted smooth dyadic blocks contribute their uniform Nikolsky tail
to every point evaluation.  This is the reconstruction step that turns a
finite-block dictionary into an approximation of the actual continuous
function. -/
theorem nikolsky_block_tail_pointwise {d : ℕ} (r : ℝ) (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : NikolskyUnitBall (2:ENNReal) r f)
    (S : Finset (Fin d → ℕ)) {ε : ℝ}
    (htail : (∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖) ≤ ε) :
    ∀ t, |f t - ∑ s ∈ S, (block s f t).re| ≤ ε := by
  classical
  have hhas := BrownianSharp.AlignmentPeriodicFourierReconstruction.nikolsky_two_blocks_hasSum
    r hr f hf
  have hs := hhas.summable
  have hq0 : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hgeo : Summable (fun s : Fin d → ℕ => ((2:ℝ)^(1/2-r))^(∑ i, s i)) :=
    BrownianSharp.AlignmentPeriodicReconstruction.summable_shape_geometric d hq0 hq1
  have hmajor : Summable (fun s : Fin d → ℕ =>
      Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^(∑ i, s i)) :=
    hgeo.mul_left (Real.sqrt ((5:ℝ)^d))
  have hnorm : Summable (fun s : Fin d → ℕ => ‖block s f‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s =>
      BrownianSharp.AlignmentPeriodicReconstruction.nikolsky_two_block_sup_bound
        s f r hf)
  have hdecomp := hs.sum_add_tsum_compl (s := S)
  rw [hhas.tsum_eq] at hdecomp
  have htailnorm : ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f‖ ≤ ε := by
    calc
      _ ≤ ∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖ :=
        norm_tsum_le_tsum_norm (hnorm.subtype _)
      _ ≤ ε := htail
  intro t
  have hEval : (∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f) t =
      ∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t := by
    simpa using (ContinuousMap.evalCLM ℝ t).map_tsum (hs.subtype _)
  have hpw := congrArg (fun g : C(UnitAddTorus (Fin d), ℂ) => g t) hdecomp
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply, hEval] at hpw
  have hpwRe := congrArg Complex.re hpw
  rw [Complex.add_re, Complex.re_sum] at hpwRe
  have hreal : (complexifyContinuous f t).re -
      ∑ s ∈ S, (block s f t).re =
      (∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t).re := by
    linarith
  change |(complexifyContinuous f t).re -
    ∑ s ∈ S, (block s f t).re| ≤ ε
  rw [hreal]
  calc
    |(∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t).re| ≤
      ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t‖ :=
        Complex.abs_re_le_norm _
    _ = ‖(∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f) t‖ := by rw [hEval]
    _ ≤ ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f‖ :=
      ContinuousMap.norm_coe_le_norm _ t
    _ ≤ ε := htailnorm

/-- Uniform KGG approximation for the actual Nikolsky-2 ball, once a uniform
tail estimate is supplied.  Crucially the subspace is selected before the
source function. -/
theorem periodic_nikolsky_full_block_KGG_uniform
    {d L : ℕ} (hd : 0 < d) (hL : 0 < L) (S : Finset (Fin d → ℕ))
    (r : ℝ) (hr : 1/2 < r)
    (hSgrade : ∀ s ∈ S, (∑ i, s i) < L)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d),ℝ)) (a : G → UnitAddTorus (Fin d))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ j : Fin L, ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector
        (S.filter (fun s => (∑ k, s k)=j.val)) r t -
        periodicFeatureVector
          (S.filter (fun s => (∑ k, s k)=j.val)) r (a i)‖ ≤ δ)
    {q ρ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (D : Fin L → ℕ) (hD : ∀ j, 0 < D j)
    {ε : ℝ}
    (htail : ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      (∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖) ≤ ε) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤ ∑ j : Fin L,
        D j * Nat.ceil (1+(1-q)⁻¹) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |f t-y t| ≤ ε + ∑ j : Fin L,
          if S.filter (fun s => (∑ k, s k)=j.val) = ∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
              (δ + Real.sqrt ((4*(10000:ℝ)^2 *
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                polynomialBudget (ρ/q) (d-1))) := by
  obtain ⟨W,hWrank,hUniform⟩ := periodic_nikolsky_finite_block_KGG
    hd hL S r hSgrade φ a hφ hsum hδ hosc hρ hq hq1 hρq hρeq D hD
  refine ⟨W,hWrank,?_⟩
  intro f hf
  obtain ⟨y,hy,hyerr⟩ := hUniform f hf
  refine ⟨y,hy,?_⟩
  intro t
  have htail' := nikolsky_block_tail_pointwise r hr f hf S (htail f hf) t
  have hfinite := hyerr t
  calc
    |f t-y t| ≤ |f t-∑ s ∈ S, (block s f t).re| +
        |(∑ s ∈ S, (block s f t).re)-y t| := abs_sub_le _ _ _
    _ ≤ ε + ∑ j : Fin L,
          if S.filter (fun s => (∑ k, s k)=j.val) = ∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
              (δ + Real.sqrt ((4*(10000:ℝ)^2 *
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                polynomialBudget (ρ/q) (d-1))) := add_le_add htail' hfinite

/-- Actual uniform-in-source finite-dimensional approximation for the
Nikolsky-2 ball: retain all grades below `M` through the exact-coordinate part
of the dictionary, compress the higher retained grades separately, and pay a
uniform smooth-block tail.  This is the reusable grade-window width theorem. -/
theorem periodic_nikolsky_low_high_uniform_approximation
    {d M T H K : ℕ} (hd : 0 < d) (hM : 0 < M) (hMT : M ≤ T+1)
    (r : ℝ) (hr : 1/2 < r)
    (hK : 0 < K)
    (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    {q ρ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (D : Fin (T+1) → ℕ) (hD : ∀ j, 0 < D j)
    {ε : ℝ}
    (htail : ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      (∑' s : ((periodicShapeSimplex (d:=d) T)ᶜ : Set (Fin d → ℕ)),
        ‖block s.1 f‖) ≤ ε) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤
        (2*5^d*(M+1)^(d-1)*2^M *
          Nat.ceil (1+(1-(3/4:ℝ))⁻¹):Cardinal) +
        ∑ j : Fin (T+1), D j * Nat.ceil (1+(1-q)⁻¹) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |f t-y t| ≤ ε + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
          ∑ j : Fin (T+1),
            if (periodicShapeSimplex (d:=d) T).filter
                (fun s => M ≤ ∑ k, s k ∧ (∑ k, s k)=j.val) = ∅ then 0 else
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
                (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
                  (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                  Real.log (2*((Fintype.card
                    (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ))+2)/
                    (D j:ℝ)) * polynomialBudget (ρ/q) (d-1))) := by
  classical
  let N := AlignmentTorusSampling.samplingGridSize d K T H
  let Sfull : Finset (Fin d → ℕ) := periodicShapeSimplex T
  let Slo : Finset (Fin d → ℕ) := periodicShapeSimplex (M-1)
  let Shi : Finset (Fin d → ℕ) := Sfull.filter (fun s => M ≤ ∑ k, s k)
  let G := Fin d → Fin (N+1)
  let a : G → UnitAddTorus (Fin d) := AlignmentTorusSampling.torusGridPoint
  have hN : 0 < N := AlignmentTorusSampling.samplingGridSize_pos hK
  obtain ⟨φ,hφ,hsum,hsupport⟩ :=
    AlignmentTorusSampling.torus_grid_partition (d:=d) N hN
  have hsupport' : ∀ i t, φ i t ≠ 0 →
      dist t (a i) < 2/(N:ℝ) := by
    intro i t hi
    exact hsupport i t hi
  have hδ : 0 ≤ ((2:ℝ)^H)⁻¹ := by positivity
  have hSlo : ∀ s ∈ Slo, (∑ k, s k) ≤ T := by
    intro s hs
    have hgrade := (mem_periodicShapeSimplex s).1 hs
    have : (∑ k, s k) ≤ M-1 := hgrade
    omega
  have hoscLo := periodic_nikolsky_grid_oscillation_of_support
    r (by linarith) hK hKC hSlo φ a hsupport'
  obtain ⟨Wlo,hWloRank,hWlo⟩ := periodic_nikolsky_low_blocks_KGG
    hd hM r φ a hφ hsum hδ hoscLo
  have hShiGrade : ∀ s ∈ Shi, (∑ k, s k) < T+1 := by
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).1
    have hgrade := (mem_periodicShapeSimplex s).1 hs'
    omega
  have hoscHi : ∀ j : Fin (T+1), ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector (Shi.filter (fun s => (∑ k,s k)=j.val)) r t -
        periodicFeatureVector (Shi.filter (fun s => (∑ k,s k)=j.val)) r (a i)‖ ≤
          ((2:ℝ)^H)⁻¹ := by
    intro j i t hne
    have hgradej : ∀ s ∈ Shi.filter (fun s => (∑ k,s k)=j.val),
        (∑ k, s k) ≤ T := by
      intro s hs
      have hs' := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
      exact (mem_periodicShapeSimplex s).1 hs'
    exact periodic_nikolsky_grid_oscillation_of_support r (by linarith)
      hK hKC hgradej φ a hsupport' i t hne
  have hfinhi := periodic_nikolsky_finite_block_KGG
    hd (by omega : 0<T+1) Shi r hShiGrade φ a hφ hsum hδ hoscHi
    hρ hq hq1 hρq hρeq D hD
  obtain ⟨Whi,hWhiRank,hWhi⟩ := hfinhi
  let W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ) := Wlo ⊔ Whi
  have hWrank : Module.rank ℝ W ≤
      (2*5^d*(M+1)^(d-1)*2^M *
        Nat.ceil (1+(1-(3/4:ℝ))⁻¹):Cardinal) +
      ∑ j : Fin (T+1), D j * Nat.ceil (1+(1-q)⁻¹) := by
    calc
      Module.rank ℝ W ≤ Module.rank ℝ Wlo + Module.rank ℝ Whi :=
        Submodule.rank_add_le_rank_add_rank _ _
      _ ≤ (↑(2*5^d*(M+1)^(d-1)*2^M *
            Nat.ceil (1+(1-(3/4:ℝ))⁻¹)) : Cardinal) +
          ∑ j : Fin (T+1), D j * Nat.ceil (1+(1-q)⁻¹) := by
        have hloRank' : Module.rank ℝ Wlo ≤
            (↑(2*5^d*(M+1)^(d-1)*2^M *
              Nat.ceil (1+(1-(3/4:ℝ))⁻¹)) : Cardinal) := by
          simpa [Nat.cast_mul] using hWloRank
        exact add_le_add hloRank' hWhiRank
      _ = _ := by simp [Nat.cast_mul]
  refine ⟨W,hWrank,?_⟩
  intro f hf
  obtain ⟨ylo,hylo,hyloerr⟩ := hWlo f hf
  obtain ⟨yhi,hyhi,hyhierr⟩ := hWhi f hf
  let y : C(UnitAddTorus (Fin d),ℝ) := ylo+yhi
  have hy : y ∈ W := by
    exact Submodule.add_mem_sup hylo hyhi
  refine ⟨y,hy,?_⟩
  intro t
  have hloErr := hyloerr t
  have hhiErr := hyhierr t
  have htail' := nikolsky_block_tail_pointwise r hr f hf Sfull (htail f hf) t
  have hparts : Slo ∪ Shi = Sfull := by
    ext s
    simp only [Slo,Shi,Sfull,Finset.mem_union,Finset.mem_filter,
      mem_periodicShapeSimplex]
    omega
  have hdisj : Disjoint Slo Shi := by
    apply Finset.disjoint_left.mpr
    intro s hslo hshi
    have hlow := (mem_periodicShapeSimplex s).1 hslo
    have hhigh := (Finset.mem_filter.mp hshi).2
    omega
  have hsumParts :
      (∑ s ∈ Sfull, (block s f t).re) =
        (∑ s ∈ Slo, (block s f t).re) +
          ∑ s ∈ Shi, (block s f t).re := by
    rw [← hparts, Finset.sum_union hdisj]
  have hfiniteErr : |(∑ s ∈ Sfull, (block s f t).re)-y t| ≤
      Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
        ∑ j : Fin (T+1),
          if Shi.filter (fun s => (∑ k,s k)=j.val)=∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
              (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                polynomialBudget (ρ/q) (d-1))) := by
    rw [hsumParts]
    have hsumTri : |((∑ s ∈ Slo, (block s f t).re)-ylo t) +
        ((∑ s ∈ Shi, (block s f t).re)-yhi t)| ≤
        |(∑ s ∈ Slo, (block s f t).re)-ylo t| +
          |(∑ s ∈ Shi, (block s f t).re)-yhi t| := by
      exact abs_add_le _ _
    calc
      _ = |((∑ s ∈ Slo, (block s f t).re)-ylo t) +
            ((∑ s ∈ Shi, (block s f t).re)-yhi t)| := by
          simp [y, ContinuousMap.add_apply]; ring_nf
      _ ≤ _ := by
          calc
            _ ≤ |(∑ s ∈ Slo, (block s f t).re)-ylo t| +
                |(∑ s ∈ Shi, (block s f t).re)-yhi t| := hsumTri
            _ ≤ _ := add_le_add hloErr hhiErr
  have hfull : |f t-y t| ≤ ε +
      (Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
        ∑ j : Fin (T+1),
          if Shi.filter (fun s => (∑ k,s k)=j.val)=∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
              (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                polynomialBudget (ρ/q) (d-1)))) := by
    calc
      _ ≤ |f t-(∑ s ∈ Sfull, (block s f t).re)| +
            |(∑ s ∈ Sfull, (block s f t).re)-y t| := abs_sub_le _ _ _
      _ ≤ ε + (Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
            ∑ j : Fin (T+1),
              if Shi.filter (fun s => (∑ k,s k)=j.val)=∅ then 0 else
                Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
                  (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
                    (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                    Real.log (2*(Fintype.card G:ℝ)+2)/(D j:ℝ)) *
                    polynomialBudget (ρ/q) (d-1)))) :=
              add_le_add htail' hfiniteErr
  have hSfullTail := hfull
  simpa [Slo,Shi,Sfull,G,N, add_assoc] using hSfullTail

/-- The grade-window approximation with the certificate's actual, uniform
Nikolsky block tail substituted for the external remainder premise. -/
theorem periodic_nikolsky_low_high_uniform_approximation_of_tail
    {d M T H K : ℕ} (hd : 0 < d) (hM : 0 < M) (hMT : M ≤ T+1)
    (r : ℝ) (hr : 1/2 < r)
    (hK : 0 < K)
    (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    {q ρ q' : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (hqq' : (2:ℝ)^(1/2-r) < q') (hq' : q' < 1)
    (D : Fin (T+1) → ℕ) (hD : ∀ j, 0 < D j) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤
        (2*5^d*(M+1)^(d-1)*2^M *
          Nat.ceil (1+(1-(3/4:ℝ))⁻¹):Cardinal) +
        ∑ j : Fin (T+1), D j * Nat.ceil (1+(1-q)⁻¹) ∧
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
      ∃ y ∈ W, ∀ t,
        |f t-y t| ≤
          Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^(T+1) *
            ∑' s : Fin d → ℕ, q'^(∑ i,s i) +
          Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
          ∑ j : Fin (T+1),
            if (periodicShapeSimplex (d:=d) T).filter
                (fun s => M ≤ ∑ k, s k ∧ (∑ k, s k)=j.val) = ∅ then 0 else
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
                (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
                  (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
                  Real.log (2*((Fintype.card
                    (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ))+2)/
                    (D j:ℝ)) * polynomialBudget (ρ/q) (d-1))) := by
  classical
  let S : Finset (Fin d → ℕ) := periodicShapeSimplex T
  have hgrade : ∀ s, s ∉ S → T+1 ≤ ∑ i, s i := by
    intro s hs
    have hnot : ¬ (∑ i, s i) ≤ T := by
      intro hle
      have hmem : s ∈ S := by
        exact (mem_periodicShapeSimplex s).2 hle
      exact hs hmem
    omega
  have htail := fun f hf => nikolsky_two_uniform_tail S r hr q' hqq' hq'
    hgrade f hf
  refine periodic_nikolsky_low_high_uniform_approximation
    hd hM hMT r hr hK hKC hρ hq hq1 hρq hρeq D hD ?_
  intro f hf
  simpa [S] using htail f hf

/-- Convert the actual Nikolsky grade-window approximation to a Kolmogorov
width bound once the explicit rank allocation and summed error are checked. -/
theorem periodic_nikolsky_width_bound_of_parameters
    {d M T H K m : ℕ} (hd : 2 ≤ d) (hM : 0 < M) (hMT : M ≤ T+1)
    (r : ℝ) (hr : 1/2 < r)
    {q ρ q' : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q) (hρeq : ρ = (2:ℝ)^(1-2*r))
    (hqq' : (2:ℝ)^(1/2-r) < q') (hq' : q' < 1)
    (hK : 0 < K)
    (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    (D : Fin (T+1) → ℕ) (hD : ∀ j, 0 < D j)
    (hrank :
      2*5^d*(M+1)^(d-1)*2^M*Nat.ceil (1+(1-(3/4:ℝ))⁻¹) +
        ∑ j : Fin (T+1), D j*Nat.ceil (1+(1-q)⁻¹) ≤ m)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (herr :
      Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^(T+1) *
        (∑' s : Fin d → ℕ, q'^(∑ i,s i)) +
      Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
      ∑ j : Fin (T+1),
        (if (periodicShapeSimplex (d:=d) T).filter
            (fun s => M ≤ ∑ k, s k ∧ (∑ k,s k)=j.val) = ∅ then (0:ℝ) else
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
            (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
              (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
              Real.log (2*((Fintype.card
                (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ))+2)/
                (D j:ℝ)) * polynomialBudget (ρ/q) (d-1)))) ≤
      B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2)) :
    kolmogorovWidth {f : RealPeriodic d | NikolskyUnitBall (2:ENNReal) r f}
      m ≤ ENNReal.ofReal (B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2)) := by
  classical
  have hdp : 0 < d := by omega
  obtain ⟨W,hWrank,happrox⟩ :=
    periodic_nikolsky_low_high_uniform_approximation_of_tail
      (d:=d) (M:=M) (T:=T) (H:=H) (K:=K) hdp hM hMT r hr
      hK hKC hρ hq hq1 hρq hρeq hqq' hq' D hD
  have hrankCard : Module.rank ℝ W ≤ (m:Cardinal) := by
    have hWcast : (Module.rank ℝ W:Cardinal) ≤ (m:Cardinal) := by
      calc
        Module.rank ℝ W ≤
          ((2*5^d*(M+1)^(d-1)*2^M*Nat.ceil (1+(1-(3/4:ℝ))⁻¹):Cardinal)) +
            ∑ j : Fin (T+1), D j*Nat.ceil (1+(1-q)⁻¹) := hWrank
        _ ≤ (m:Cardinal) := by exact_mod_cast hrank
    exact hWcast
  have hE : 0 ≤ B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2) := by positivity
  unfold kolmogorovWidth
  refine le_trans (iInf_le (fun V : {V : Submodule ℝ C(UnitAddTorus (Fin d),ℝ) //
      Module.rank ℝ V ≤ (m:Cardinal)} => approximationError
        {f : RealPeriodic d | NikolskyUnitBall (2:ENNReal) r f} V.1)
        ⟨W,hrankCard⟩) ?_
  apply approximationError_le_of_pointwise _ W hE
  intro f hf
  obtain ⟨y,hy,hyerr⟩ := happrox f hf
  refine ⟨y,hy,?_⟩
  apply (ContinuousMap.norm_le (f-y) hE).2
  intro t
  have ht := hyerr t
  have htarget := herr
  have hbound := ht.trans htarget
  simpa [Real.norm_eq_abs] using hbound

theorem shifted_rank_profile_sum_bound
    {M T D : ℕ} {q : ℝ} (hM : M ≤ T+1) (hq : 0 < q) (hq1 : q < 1) :
    ((∑ j : Fin (T+1),
      (if M ≤ j.val then rank q D (j.val-M)+1 else 1) : ℕ) : ℝ) ≤
      (M:ℝ) + (D:ℝ)/(1-q) + (T+1-M:ℝ) := by
  classical
  let F : ℕ → ℕ := fun j => if M ≤ j then rank q D (j-M)+1 else 1
  have hsum := Fin.sum_univ_eq_sum_range F (T+1)
  rw [hsum]
  have hsplit := Finset.sum_range_add_sum_Ico F hM
  rw [← hsplit]
  have hlow : (∑ j ∈ Finset.range M, F j) = M := by
    calc
      (∑ j ∈ Finset.range M, F j) = ∑ j ∈ Finset.range M, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjM : j<M := Finset.mem_range.mp hj
        simp [F, Nat.not_le_of_gt hjM]
      _ = M := by simp
  have hhigh : (∑ j ∈ Finset.Ico M (T+1), F j) =
      ∑ ℓ ∈ Finset.range (T+1-M), (rank q D ℓ + 1) := by
    refine Finset.sum_bij (s := Finset.Ico M (T+1))
      (t := Finset.range (T+1-M)) (f := F)
      (g := fun ℓ => rank q D ℓ + 1) (fun j _ => j-M) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]
      omega
    · intro j hj k hk hjk
      simp only [Finset.mem_Ico] at hj hk
      omega
    · intro ℓ hℓ
      simp only [Finset.mem_range] at hℓ
      refine ⟨M+ℓ, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp [F, hj.1]
  rw [hlow, hhigh]
  have hgeom := sum_rank_le hq hq1 D (T+1-M)
  have hsumNat :
      (∑ ℓ ∈ Finset.range (T+1-M), (rank q D ℓ + 1) : ℕ) =
        Finset.sum (Finset.range (T+1-M)) (fun ℓ => rank q D ℓ) + (T+1-M) := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hsumNat]
  have hgeom' :
      (∑ ℓ ∈ Finset.range (T+1-M), (rank q D ℓ : ℝ)) ≤
        (D:ℝ)/(1-q) := by exact_mod_cast hgeom
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sum]
  have hsub : ((T+1-M:ℕ):ℝ) = (T:ℝ)+1-M := by
    rw [Nat.cast_sub hM, Nat.cast_add, Nat.cast_one]
  rw [hsub]
  linarith

theorem shifted_polynomial_geometric_sum_bound
    {M T : ℕ} {x : ℝ} (hM : M ≤ T+1) (hx : 0 < x) (hx1 : x < 1)
    (k : ℕ) :
    (∑ j : Fin (T+1),
      (if M ≤ j.val then
        ((j.val-M+1:ℕ):ℝ)^k*x^(j.val-M) else 0)) ≤
      polynomialBudget x k := by
  classical
  let F : ℕ → ℝ := fun j =>
    if M ≤ j then ((j-M+1:ℕ):ℝ)^k*x^(j-M) else 0
  have hsum := Fin.sum_univ_eq_sum_range F (T+1)
  rw [hsum]
  have hsplit := Finset.sum_range_add_sum_Ico F hM
  rw [← hsplit]
  have hlow : (∑ j ∈ Finset.range M, F j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    simp [F, Nat.not_le_of_gt hjM]
  rw [hlow, zero_add]
  have hhigh : (∑ j ∈ Finset.Ico M (T+1), F j) =
      ∑ ℓ ∈ Finset.range (T+1-M), ((ℓ+1:ℕ):ℝ)^k*x^ℓ := by
    refine Finset.sum_bij (s := Finset.Ico M (T+1))
      (t := Finset.range (T+1-M)) (f := F)
      (g := fun ℓ => ((ℓ+1:ℕ):ℝ)^k*x^ℓ) (fun j _ => j-M) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]
      omega
    · intro j hj k hk hjk
      simp only [Finset.mem_Ico] at hj hk
      omega
    · intro ℓ hℓ
      simp only [Finset.mem_range] at hℓ
      refine ⟨M+ℓ, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp [F, hj.1]
  rw [hhigh]
  have hs := summable_polynomial_geometric hx hx1 k
  have hsumle := hs.sum_le_tsum (s := Finset.range (T+1-M))
    (fun ℓ hℓ => by positivity)
  simpa [polynomialBudget] using hsumle

private theorem sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x^n) = (Real.sqrt x)^n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

theorem periodic_nikolsky_allocated_grade_error_bound
    {d M j : ℕ} {ρ q L lam G : ℝ} (hd : 1≤d) (hM : 0<M)
    (hρ : 0<ρ) (hq : 0<q) (hρq : ρ<q) (hL : 0<L) (hlam : 0<lam)
    (hgrade : M≤j)
    (D : ℕ → ℕ)
    (hD : (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j-M)/2 ≤ (D (j):ℝ))
    (hG : 0≤G) (hlog : G ≤ L*((M+1:ℕ):ℝ))
    (hρpow : ρ^M/(2:ℝ)^M=lam^2) :
    Real.sqrt (((j+1:ℕ):ℝ)^(d-1)) *
      Real.sqrt ((4*(10000:ℝ)^2 *
        (2*(5:ℝ)^d*((j+1:ℕ):ℝ)^(d-1)*ρ^j) *
        G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))) ≤
      Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
        polynomialBudget (ρ/q) (d-1)) * lam *
        Real.sqrt (((M+1:ℕ):ℝ)^d) *
        ((j-M+1:ℕ):ℝ)^(d-1) * (Real.sqrt (ρ/q))^(j-M) := by
  classical
  let k := d-1
  let ℓ := j-M
  let u : ℝ := ((j+1:ℕ):ℝ)
  let v : ℝ := ((M+1:ℕ):ℝ)
  let z : ℝ := ((ℓ+1:ℕ):ℝ)
  let P := polynomialBudget (ρ/q) k
  let B0 : ℝ := 4*(10000:ℝ)^2*(2*(5:ℝ)^d)
  let B1 : ℝ := 2*B0*L*P
  have hj : j=M+ℓ := by dsimp [ℓ]; omega
  have hu : 0≤u := by dsimp [u]; positivity
  have hv : 0≤v := by dsimp [v]; positivity
  have hz : 0≤z := by dsimp [z]; positivity
  have hshape : u≤v*z := by
    dsimp [u,v,z,ℓ]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    have hcast : (j:ℝ)=(M:ℝ)+((j-M:ℕ):ℝ) := by
      exact_mod_cast (Nat.add_sub_of_le hgrade).symm
    rw [hcast]
    push_cast
    have hm : 0≤(M:ℝ) := by positivity
    have hℓ : 0≤((j-M:ℕ):ℝ) := by positivity
    nlinarith [mul_nonneg hm hℓ]
  have hshapePow : u^(2*k)≤(v*z)^(2*k) :=
    pow_le_pow_left₀ hu hshape _
  have hDpos : 0<(D j:ℝ) := by
    have : 0<(2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j-M)/2 := by positivity
    exact this.trans_le hD
  have hbasePos : 0<(2:ℝ)^M*v^k*q^ℓ/2 := by positivity
  have hratio : 0<ρ/q := div_pos hρ hq
  have hP : 0≤P := polynomialBudget_nonneg hratio.le k
  have hsplit : ρ^j=ρ^M*ρ^ℓ := by rw [hj, pow_add]
  have hprod :
      u^k*(B0*u^k*ρ^j*G/(D j:ℝ)*P) ≤
        B1*lam^2*v^d*z^(2*k)*(ρ/q)^ℓ := by
    have hnum : 0≤ B0*u^(2*k)*ρ^M*ρ^ℓ*G*P := by
      dsimp [B0]; positivity
    have hnumBound :
      B0*u^(2*k)*ρ^M*ρ^ℓ*G*P ≤
        B0*(v*z)^(2*k)*ρ^M*ρ^ℓ*(L*v)*P := by
      calc
        _ ≤ B0*(v*z)^(2*k)*ρ^M*ρ^ℓ*G*P := by gcongr
        _ ≤ _ := by gcongr
    calc
      u^k*(B0*u^k*ρ^j*G/(D j:ℝ)*P) =
          (B0*u^(2*k)*ρ^M*ρ^ℓ*G*P)/(D j:ℝ) := by
            rw [hsplit]
            ring
      _ ≤ (B0*(v*z)^(2*k)*ρ^M*ρ^ℓ*(L*v)*P)/
            (D j:ℝ) := by
          exact div_le_div_of_nonneg_right hnumBound hDpos.le
      _ ≤ (B0*(v*z)^(2*k)*ρ^M*ρ^ℓ*(L*v)*P)/
            ((2:ℝ)^M*v^k*q^ℓ/2) :=
              div_le_div_of_nonneg_left (by positivity) hbasePos hD
      _ = B1*lam^2*v^d*z^(2*k)*(ρ/q)^ℓ := by
          dsimp [B0,B1,k]
          have hvpow : v^(2*k)*v = v^(d+k) := by
            dsimp [k]
            rw [← pow_succ]
            congr 1
            omega
          have hρM : ρ^M=lam^2*(2:ℝ)^M := by
            exact (div_eq_iff (by positivity : (2:ℝ)^M ≠ 0)).mp hρpow
          apply (div_eq_iff (ne_of_gt hbasePos)).2
          dsimp [B0,B1,k]
          rw [show (v*z)^(2*(d-1))=v^(2*(d-1))*z^(2*(d-1)) by rw [mul_pow], hρM]
          rw [div_pow]
          have hqpow0 : 0<q^ℓ := pow_pos hq _
          field_simp [ne_of_gt hqpow0]
          calc
            v^(2*(d-1))*z^(2*(d-1))*v*P =
                (v^(2*(d-1))*v)*z^(2*(d-1))*P := by ring
            _ = v^(d+(d-1))*z^(2*(d-1))*P := by
                rw [hvpow]
            _ = z^(2*(d-1))*P*v^d*v^(d-1) := by
                rw [pow_add]
                ring
            _ = _ := by ring
  have hroot := Real.sqrt_le_sqrt hprod
  have hleft :
      Real.sqrt (u^k)*Real.sqrt
        (B0*u^k*ρ^j*G/(D j:ℝ)*P) =
      Real.sqrt (u^k*(B0*u^k*ρ^j*G/(D j:ℝ)*P)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ u^k)]
  have hxpow : Real.sqrt ((ρ/q)^ℓ)=(Real.sqrt (ρ/q))^ℓ :=
    sqrt_pow_nat hratio.le ℓ
  have hright :
      Real.sqrt (B1*lam^2*v^d*z^(2*k)*(ρ/q)^ℓ) =
        Real.sqrt B1*lam*Real.sqrt (v^d)*z^k*(Real.sqrt (ρ/q))^ℓ := by
    rw [show B1*lam^2*v^d*z^(2*k)*(ρ/q)^ℓ =
        (B1)*(lam^2)*(v^d)*(z^(2*k))*((ρ/q)^ℓ) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam]
    have hzpow : Real.sqrt (z^(2*k)) = z^k := by
      have hpow : 2*k=k*2 := by omega
      rw [hpow, pow_mul, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hz k)]
    rw [hzpow, hxpow]
  calc
    Real.sqrt (((j+1:ℕ):ℝ)^(d-1)) *
        Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((j+1:ℕ):ℝ)^(d-1)*ρ^j)*
          G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))) =
      Real.sqrt (u^k)*Real.sqrt
        (B0*u^k*ρ^j*G/(D j:ℝ)*P) := by
          congr 1
          simp [u,k,P,B0]
          ring
    _ = Real.sqrt (u^k*(B0*u^k*ρ^j*G/(D j:ℝ)*P)) := hleft
    _ ≤ Real.sqrt (B1*lam^2*v^d*z^(2*k)*(ρ/q)^ℓ) := hroot
    _ = _ := by simpa [B1, B0, u, v, z, k, P, ℓ, mul_assoc, mul_left_comm, mul_comm]
      using hright

/-- Sum of the stochastic part of the allocated grade errors. The activation
predicate may be the nonempty-grade filter from the finite block theorem; it
only needs to imply `M ≤ grade`. -/
theorem periodic_nikolsky_allocated_stochastic_sum_bound
    {d M T : ℕ} {ρ q L lam G : ℝ}
    (hd : 2≤d) (hM : 0<M) (hMT : M≤T+1)
    (hρ : 0<ρ) (hq : 0<q) (hρq : ρ<q) (hL : 0<L) (hlam : 0<lam)
    (hG : 0≤G) (hlog : G ≤ L*((M+1:ℕ):ℝ))
    (hρpow : ρ^M/(2:ℝ)^M=lam^2)
    (D : Fin (T+1) → ℕ)
    (hD : ∀ j : Fin (T+1), M≤j.val →
      (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j.val-M)/2 ≤ (D j:ℝ))
    (active : Fin (T+1) → Prop) [DecidablePred active]
    (hactive : ∀ j, active j → M≤j.val) :
    (∑ j : Fin (T+1), if active j then
      Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
        Real.sqrt ((4*(10000:ℝ)^2 *
          (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
          G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1)))
      else 0) ≤
    Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
      polynomialBudget (ρ/q) (d-1)) * lam *
      Real.sqrt (((M+1:ℕ):ℝ)^d) *
      polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
  classical
  have hratio : 0<ρ/q := div_pos hρ hq
  have hx : 0<Real.sqrt (ρ/q) := Real.sqrt_pos.2 hratio
  have hx1 : Real.sqrt (ρ/q)<1 := by
    have hquot : ρ/q<1 := (div_lt_one hq).2 hρq
    have hsqrt : 0≤Real.sqrt (ρ/q) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hratio.le]
  let C : ℝ := Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
      polynomialBudget (ρ/q) (d-1)) * lam *
      Real.sqrt (((M+1:ℕ):ℝ)^d)
  have hC : 0≤C := by dsimp [C]; positivity
  have hterm : ∀ j : Fin (T+1),
      (if active j then
        Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
          Real.sqrt ((4*(10000:ℝ)^2 *
            (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
            G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1)))
       else 0) ≤
      C * (if M≤j.val then
        ((j.val-M+1:ℕ):ℝ)^(d-1)*(Real.sqrt (ρ/q))^(j.val-M) else 0) := by
    intro j
    by_cases ha : active j
    · have hjM := hactive j ha
      have hjD := hD j hjM
      let DD : ℕ → ℕ := fun i => if hi : i≤T then D ⟨i, by omega⟩ else 1
      have hjT : j.val≤T := Nat.lt_succ_iff.mp j.isLt
      have hDj : (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j.val-M)/2 ≤ (DD j.val:ℝ) := by
        simpa [DD, hjT] using hjD
      have hd1 : 1≤d := by omega
      have hgrade := periodic_nikolsky_allocated_grade_error_bound
        hd1 hM hρ hq hρq hL hlam hjM DD hDj hG hlog hρpow
      simpa [C, DD, hjM, ha, hjT, mul_assoc] using hgrade
    · simp [ha]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ j : Fin (T+1), C * (if M≤j.val then
          ((j.val-M+1:ℕ):ℝ)^(d-1)*(Real.sqrt (ρ/q))^(j.val-M) else 0) :=
        Finset.sum_le_sum (by intro j hj; exact hterm j)
    _ = C * ∑ j : Fin (T+1), (if M≤j.val then
          ((j.val-M+1:ℕ):ℝ)^(d-1)*(Real.sqrt (ρ/q))^(j.val-M) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ C * polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact shifted_polynomial_geometric_sum_bound hMT hx hx1 (d-1)
    _ = _ := by ring

/-- Separates the active-grade error sum into the high-grid term and the
stochastic envelope needed for the outer dyadic parameter choice. -/
theorem periodic_nikolsky_active_grade_error_sum_bound
    {d M T H : ℕ} {ρ q L lam G : ℝ}
    (hd : 2≤d) (hM : 0<M) (hMT : M≤T+1)
    (hρ : 0<ρ) (hq : 0<q) (hρq : ρ<q) (hL : 0<L) (hlam : 0<lam)
    (hG : 0≤G) (hlog : G≤L*((M+1:ℕ):ℝ))
    (hρpow : ρ^M/(2:ℝ)^M=lam^2)
    (D : Fin (T+1) → ℕ)
    (hD : ∀ j : Fin (T+1), M≤j.val →
      (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j.val-M)/2 ≤ (D j:ℝ))
    (active : Fin (T+1) → Prop) [DecidablePred active]
    (hactive : ∀ j, active j → M≤j.val) :
    (∑ j : Fin (T+1), if active j then
      Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
        (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
          (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
          G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))))
      else 0) ≤
    ((2:ℝ)^H)⁻¹ *
      (∑ j : Fin (T+1), if M≤j.val then
        Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) +
    Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
      polynomialBudget (ρ/q) (d-1)) * lam *
      Real.sqrt (((M+1:ℕ):ℝ)^d) *
      polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
  classical
  let gridTerm : Fin (T+1) → ℝ := fun j =>
    if active j then Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1))*((2:ℝ)^H)⁻¹ else 0
  let stochTerm : Fin (T+1) → ℝ := fun j =>
    if active j then Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
      Real.sqrt ((4*(10000:ℝ)^2 *
        (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
        G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))) else 0
  have hdecomp :
      (∑ j : Fin (T+1), if active j then
        Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
          (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
            (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
            G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))))
        else 0) =
      (∑ j : Fin (T+1), gridTerm j) + (∑ j : Fin (T+1), stochTerm j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ha : active j <;> simp [gridTerm, stochTerm, ha, mul_add]
  have hgrid :
      (∑ j : Fin (T+1), gridTerm j) ≤ ((2:ℝ)^H)⁻¹ *
        (∑ j : Fin (T+1), if M≤j.val then
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) := by
    calc
      _ = ((2:ℝ)^H)⁻¹ * ∑ j : Fin (T+1),
          (if active j then Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases ha : active j <;> simp [gridTerm, ha] <;> ring
      _ ≤ ((2:ℝ)^H)⁻¹ * ∑ j : Fin (T+1),
          (if M≤j.val then Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j hj
        by_cases ha : active j
        · have hjM := hactive j ha
          simp [ha, hjM]
        · simp [ha]
          split_ifs <;> positivity
  have hstoch :
      (∑ j : Fin (T+1), stochTerm j) ≤
        Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
          polynomialBudget (ρ/q) (d-1)) * lam *
          Real.sqrt (((M+1:ℕ):ℝ)^d) *
          polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
    simpa [stochTerm] using periodic_nikolsky_allocated_stochastic_sum_bound
      hd hM hMT hρ hq hρq hL hlam hG hlog hρpow D hD active hactive
  rw [hdecomp]
  exact add_le_add hgrid hstoch

/-- The exact finite-window error side condition from the uniform KGG
approximation reduces to its tail, low-grid, high-grid, and stochastic pieces.
The active grades are precisely the nonempty simplex grade slices. -/
theorem periodic_nikolsky_exact_error_components
    {d M T H : ℕ} {ρ q L lam G Tail : ℝ}
    (hd : 2≤d) (hM : 0<M) (hMT : M≤T+1)
    (hρ : 0<ρ) (hq : 0<q) (hρq : ρ<q) (hL : 0<L) (hlam : 0<lam)
    (hG : 0≤G) (hlog : G≤L*((M+1:ℕ):ℝ))
    (hρpow : ρ^M/(2:ℝ)^M=lam^2)
    (D : Fin (T+1) → ℕ)
    (hD : ∀ j : Fin (T+1), M≤j.val →
      (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j.val-M)/2 ≤ (D j:ℝ)) :
    Tail + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
      (∑ j : Fin (T+1),
        if (periodicShapeSimplex (d:=d) T).filter
            (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val) = ∅ then 0 else
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
            (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
              (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
              G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1)))) ) ≤
    Tail + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
      ((2:ℝ)^H)⁻¹ *
        (∑ j : Fin (T+1), if M≤j.val then
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) +
      Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
        polynomialBudget (ρ/q) (d-1)) * lam *
        Real.sqrt (((M+1:ℕ):ℝ)^d) *
        polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
  classical
  let active : Fin (T+1) → Prop := fun j =>
    (periodicShapeSimplex (d:=d) T).filter
      (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val) ≠ ∅
  have hactive : ∀ j, active j → M≤j.val := by
    intro j hj
    have hmem : ∃ s∈periodicShapeSimplex (d:=d) T,
        M≤∑ k,s k ∧ (∑ k,s k)=j.val := by
      simpa [active] using hj
    obtain ⟨s,hs,hsinfo⟩ := hmem
    exact hsinfo.1.trans_eq hsinfo.2
  have hsum := periodic_nikolsky_active_grade_error_sum_bound
    (H:=H) hd hM hMT hρ hq hρq hL hlam hG hlog hρpow D hD active hactive
  let gradeFilter : Fin (T+1) → Finset (Fin d → ℕ) := fun j =>
    (periodicShapeSimplex (d:=d) T).filter
      (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val)
  let gradeError : Fin (T+1) → ℝ := fun j =>
    Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) *
      (((2:ℝ)^H)⁻¹ + Real.sqrt ((4*(10000:ℝ)^2 *
        (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val)) *
        G/(D j:ℝ)*polynomialBudget (ρ/q) (d-1))))
  have hsumEq :
      (∑ j : Fin (T+1), if gradeFilter j=∅ then 0 else gradeError j) =
        (∑ j : Fin (T+1), if active j then gradeError j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : gradeFilter j=∅
    · have hact : ¬ active j := by
        change ¬ gradeFilter j ≠ ∅
        exact fun hne => hne he
      rw [if_pos he, if_neg hact]
    · have hact : active j := by
        change gradeFilter j ≠ ∅
        exact he
      rw [if_neg he, if_pos hact]
  calc
    _ = Tail + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
        (∑ j : Fin (T+1), if active j then gradeError j else 0) := by
          change Tail + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
            (∑ j : Fin (T+1), if gradeFilter j=∅ then 0 else gradeError j) = _
          rw [hsumEq]
    _ ≤ Tail + Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ +
        (((2:ℝ)^H)⁻¹ * (∑ j : Fin (T+1), if M≤j.val then
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) +
          Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
            polynomialBudget (ρ/q) (d-1)) * lam *
            Real.sqrt (((M+1:ℕ):ℝ)^d) *
            polynomialBudget (Real.sqrt (ρ/q)) (d-1)) := by
          have h := add_le_add_left hsum (Tail +
            Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹)
          simpa [gradeError, add_comm, add_left_comm, add_assoc] using h
    _ = _ := by ring

end BrownianSharp.AlignmentExponentialNikolskyWidth
