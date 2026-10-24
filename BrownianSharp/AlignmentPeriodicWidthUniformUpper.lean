import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.AlignmentPeriodicTail
import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.KolmogorovWidth
import BrownianSharp.LayerIndex
import BrownianSharp.ShapeGrowth
import BrownianSharp.AlignmentEndpointWidthExtraction
import BrownianSharp.AlignmentContinuousLInfinity
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentPeriodicUpperReduction

/-! A uniform-source form of the periodic Sobolev feature approximation. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace Topology
open Filter
open MeasureTheory

namespace BrownianSharp.AlignmentPeriodicWidthUniformUpper

open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.AlignmentPeriodicWidthRealification
open BrownianSharp.AlignmentTorusSampling
open BrownianSharp.AlignmentPeriodicRealEnergy
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPeriodicTail
open BrownianSharp.AlignmentAmbientWidth
open HaarQuarter.TheoremD.Width
open BrownianSharp
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open BrownianSharp.AlignmentEndpointWidthExtraction
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

/-- Uniform feature approximation before evaluating at a Sobolev source.
Unlike the pointwise-in-source wrapper, the approximating subspace is selected
once and works for every unit Euclidean source vector. -/
theorem periodic_uniform_feature_KGG
    {d L M : ℕ} (hd : 0<d) (S : Finset (Fin d → ℕ)) (r : ℝ)
    {G : Type} [Fintype G]
    (φ : G → C(UnitAddTorus (Fin d), ℝ))
    (a : G → UnitAddTorus (Fin d))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ}
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖periodicFeatureVector S r t-periodicFeatureVector S r (a i)‖ ≤ δ)
    (σ : (FourierCoeffIndex S × Fin 2) → Option (Fin L))
    (hgrade : ∀ i j, σ i = some j → coefficientGrade i.1 = M+j.val)
    (hcount : ∀ j : Fin L,
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i=some j)).card ≤
        2*5^d*2^(M+j.val)*(M+j.val+1)^(d-1))
    {q ρ : ℝ} (hρ : 0<ρ) (hq : 0<q) (hq1 : q<1) (hρq : ρ<q)
    (hρeq : ρ=(2:ℝ)^(1-2*r))
    (D : ℕ) (hD : 0<D)
    (hlow : Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i=none} ≤ D) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤ (D*Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
      ∀ x : EuclideanSpace ℝ (FourierCoeffIndex S × Fin 2), ‖x‖≤1 →
        ∃ y ∈ W, ∀ t, |⟪x,periodicFeatureVector S r t⟫-y t| ≤ δ+
          Real.sqrt ((4*(10000:ℝ)^2*
            (2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
            Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ))*
            polynomialBudget (ρ/q) (d-1)) := by
  classical
  let v : UnitAddTorus (Fin d) → EuclideanSpace ℝ (FourierCoeffIndex S × Fin 2) :=
    fun x => periodicFeatureVector S r x
  let R : Fin L → ℝ := fun j =>
    Real.sqrt (((2*5^d*2^(M+j.val)*(M+j.val+1)^(d-1):ℕ):ℝ)) *
      (2:ℝ)^(-r*((M+j.val):ℝ))
  let A₀ : ℝ := 2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M
  have hA₀ : 0≤A₀ := by dsimp [A₀]; positivity
  have hR : ∀ j, 0≤R j := by intro j; dsimp [R]; positivity
  have hrow : ∀ j g, ‖coordinateLayerMask σ (some j) (v (a g))‖≤R j := by
    intro j g
    have hrad := periodicFeature_layer_radius S r (a g) σ (some j) (M+j.val)
      (fun i hij => hgrade i j hij) (hcount j)
    simpa [v,R] using hrad
  have henergy : ∀ j, (R j)^2≤A₀*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val) := by
    intro j
    have hid := periodic_feature_radius_energy_identity d (d-1) (M+j.val) r
    have hidR : (R j)^2 =
        (2*(5:ℝ)^d)*((M+j.val+1:ℕ):ℝ)^(d-1)*ρ^(M+j.val) := by
      simpa [R,hρeq,Nat.cast_add] using hid
    have hpoly : ((M+j.val+1:ℕ):ℝ)^(d-1) ≤
        ((M+1:ℕ):ℝ)^(d-1)*((j.val+1:ℕ):ℝ)^(d-1) := by
      have hb : ((M+j.val+1:ℕ):ℝ) ≤ ((M+1)*(j.val+1):ℕ) := by
        exact_mod_cast (show M+j.val+1≤(M+1)*(j.val+1) by nlinarith)
      rw [Nat.cast_mul] at hb
      have hp := pow_le_pow_left₀ (by positivity) hb (d-1)
      rw [mul_pow] at hp
      exact hp
    have hρpow : ρ^(M+j.val)=ρ^M*ρ^(j.val) := by rw [pow_add]
    have hcombined :
        ((M+j.val+1:ℕ):ℝ)^(d-1)*ρ^M ≤
          ((M+1:ℕ):ℝ)^(d-1)*((j.val+1:ℕ):ℝ)^(d-1)*ρ^M := by
      calc
        _ ≤ ((M+1:ℕ):ℝ)^(d-1)*((j.val+1:ℕ):ℝ)^(d-1)*ρ^M :=
          mul_le_mul_of_nonneg_right hpoly (pow_nonneg hρ.le _)
        _ = _ := by ring
    have hmul :
        (2*(5:ℝ)^d)*((M+j.val+1:ℕ):ℝ)^(d-1)*ρ^M*ρ^(j.val) ≤
        (2*(5:ℝ)^d)*((M+1:ℕ):ℝ)^(d-1)*((j.val+1:ℕ):ℝ)^(d-1)*ρ^M*ρ^(j.val) := by
      calc
        _ = (2*(5:ℝ)^d) * (((M+j.val+1:ℕ):ℝ)^(d-1) * ρ^M) * ρ^(j.val) := by ring
        _ ≤ (2*(5:ℝ)^d) * (((M+1:ℕ):ℝ)^(d-1)*((j.val+1:ℕ):ℝ)^(d-1)*ρ^M) * ρ^(j.val) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcombined (by positivity)) (pow_nonneg hρ.le _)
        _ = _ := by ring
    calc
      (R j)^2 = (2*(5:ℝ)^d)*((M+j.val+1:ℕ):ℝ)^(d-1)*ρ^(M+j.val) := hidR
      _ = (2*(5:ℝ)^d)*((M+j.val+1:ℕ):ℝ)^(d-1)*ρ^M*ρ^(j.val) := by rw [hρpow]; ring
      _ ≤ A₀*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val) := by
        simpa [A₀, mul_assoc, mul_left_comm, mul_comm] using hmul
  have happ := partition_geometric_hilbert_layer_approximation
    v φ a hφ hsum σ R hR hrow (A₀:=A₀) (ρ:=ρ) (q:=q) (k:=d-1)
    hA₀ hρ hq hq1 hρq henergy D hD hlow hosc
  obtain ⟨W,hW,happ⟩ := happ
  refine ⟨W,hW,?_⟩
  intro x hx
  obtain ⟨y,hy,he⟩ := happ x hx
  refine ⟨y,hy,?_⟩
  intro t
  exact he t

/-- Actual Sobolev-2 approximation on a finite coordinate box with one common
subspace for the entire unit ball. The omitted-block estimate is explicit as
a premise so it can be instantiated by the summable geometric-tail theorem. -/
theorem periodic_sobolev_box_uniform_approximation
    {d M T H K : ℕ} (hd : 0<d) (r : ℝ) (hr : 1/2<r)
    {ε q ρ : ℝ} (htail : ∀ f : RealPeriodic d, SobolevUnitBall 2 r f →
      ∑' s : ((periodicShapeBox (d:=d) T)ᶜ : Set (Fin d → ℕ)),
        ‖block s.1 f‖ ≤ ε)
    (hρ : 0<ρ) (hq : 0<q) (hq1 : q<1) (hρq : ρ<q)
    (hρeq : ρ=(2:ℝ)^(1-2*r))
    (hK : 0<K) (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ)) :
    ∃ W : Submodule ℝ C(UnitAddTorus (Fin d),ℝ),
      Module.rank ℝ W ≤
        ((2*5^d*(M+1)^(d-1)*2^M)*Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
      ∀ f : RealPeriodic d, SobolevUnitBall 2 r f →
        ∃ y ∈ W, ∀ t, |f t-y t| ≤ ε+((2:ℝ)^H)⁻¹+
          Real.sqrt ((4*(10000:ℝ)^2*
            (2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
            (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
              (d:ℝ)*(((d+2)*(M+(d*T+1))+H:ℕ):ℝ)*Real.log 2) /
              ((2*5^d*(M+1)^(d-1)*2^M):ℝ)) *
            polynomialBudget (ρ/q) (d-1)) := by
  classical
  let S : Finset (Fin d → ℕ) := periodicShapeBox T
  let L : ℕ := d*T+1
  have hS : ∀ s∈S, ∑ j,s j ≤ M+L := by
    intro s hs
    have hb := periodic_box_grade_le hs
    dsimp [L]
    omega
  let σ : (FourierCoeffIndex S × Fin 2) → Option (Fin L) := fun i =>
    if hg : M ≤ coefficientGrade i.1 then
      some ⟨coefficientGrade i.1-M, by
        have hshape := i.1.1.2
        have hgmax := periodic_box_grade_le hshape
        unfold coefficientGrade at hgmax ⊢
        dsimp [L]
        omega⟩
    else none
  have hgrade : ∀ i j, σ i=some j → coefficientGrade i.1=M+j.val := by
    intro i j hj
    dsimp [σ] at hj
    split at hj
    · rename_i hg
      injection hj with hj'
      have hval := congrArg Fin.val hj'
      dsimp [L] at hval
      omega
    · contradiction
  have hbelow : ∀ i, σ i=none → coefficientGrade i.1<M := by
    intro i hi
    dsimp [σ] at hi
    split at hi
    · contradiction
    · omega
  let τ : (FourierCoeffIndex S × Fin 2) → Option ℕ := fun i => (σ i).map Fin.val
  have hbelowτ : ∀ i, τ i=none → coefficientGrade i.1<M := by
    intro i hi
    have hs : σ i=none := by simpa [τ] using hi
    exact hbelow i hs
  have hlow : Fintype.card {i : FourierCoeffIndex S × Fin 2 // τ i=none} ≤
      2*5^d*(M+1)^(d-1)*2^M := by
    exact periodic_low_frequency_card_le_sharp hd S τ hbelowτ
  have hlowσ : Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i=none} ≤
      2*5^d*(M+1)^(d-1)*2^M := by
    have he : {i : FourierCoeffIndex S × Fin 2 // σ i=none} ≃
        {i : FourierCoeffIndex S × Fin 2 // τ i=none} :=
      Equiv.subtypeEquivRight (by intro i; simp [τ])
    rw [Fintype.card_congr he]
    exact hlow
  have hD : 0 < 2*5^d*(M+1)^(d-1)*2^M := by positivity
  obtain ⟨φ,hφ,hsum,hosc⟩ :=
    AlignmentTorusSampling.periodic_sampling_grid S r (by linarith) hS K H hK hKC
  let a : (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K (M+L) H+1)) →
      UnitAddTorus (Fin d) := AlignmentTorusSampling.torusGridPoint
  have hcount : ∀ j : Fin L,
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i=some j)).card ≤
        2*5^d*2^(M+j.val)*(M+j.val+1)^(d-1) := by
    intro j
    let τ : (FourierCoeffIndex S × Fin 2) → Option ℕ := fun i => (σ i).map Fin.val
    have hτ : ∀ i n, τ i=some n → coefficientGrade i.1=M+n := by
      intro i n hi
      simp [τ] at hi
      rcases hi with ⟨j', hj', hv⟩
      rw [hgrade i j' hj', hv]
    have hc := periodic_grade_coordinate_count_le S hd τ M hτ j.val
      (shape_grade_card_le_power_pred hd S (M+j.val))
    have heq :
      Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i=some j) =
      Finset.univ.filter (fun i => τ i=some j.val) := by
      ext i
      constructor
      · intro hi
        have hσ := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        constructor
        · simp
        · simpa [τ,hσ]
      · intro hi
        have hτeq := (Finset.mem_filter.mp hi).2
        simp [τ] at hτeq
        rcases hτeq with ⟨j', hj', hv⟩
        have h' : j'=j := Fin.ext hv
        apply Finset.mem_filter.mpr
        constructor
        · simp
        · simpa [h'] using hj'
    rw [heq]
    exact hc
  have hosc' : ∀ i t, φ i t≠0 →
      ‖periodicFeatureVector S r t-periodicFeatureVector S r (a i)‖ ≤ ((2:ℝ)^H)⁻¹ := by
    intro i t hi
    have h := hosc i t hi
    simpa [a, one_div] using h
  obtain ⟨W,hW,hgeom⟩ := periodic_uniform_feature_KGG
    hd S r φ a hφ hsum hosc' σ hgrade hcount hρ hq hq1 hρq hρeq
    (2*5^d*(M+1)^(d-1)*2^M) hD hlowσ
  refine ⟨W,?_,?_⟩
  · calc
      Module.rank ℝ W ≤
          (2*5^d*(M+1)^(d-1)*2^M:ℕ) * Nat.ceil (1+(1-q)⁻¹) := by
            simpa only [Nat.cast_mul] using hW
      _ = ((2*5^d*(M+1)^(d-1)*2^M)*Nat.ceil (1+(1-q)⁻¹):Cardinal) := by
        push_cast
        ring
  intro f hf
  have hsource : ‖periodicSourceVector S r f‖≤1 := by
    have hsq := periodicSourceVector_norm_sq S r f
    have hE := sobolev_two_finite_real_energy_le_one r f hf S
    have hnormsq : ‖periodicSourceVector S r f‖^2≤1 := by rw [hsq]; exact hE
    have hnn := norm_nonneg (periodicSourceVector S r f)
    nlinarith [sq_nonneg (‖periodicSourceVector S r f‖-1)]
  obtain ⟨y,hy,hyerr⟩ := hgeom (periodicSourceVector S r f) hsource
  refine ⟨y,hy,?_⟩
  intro t
  have hfinite := hyerr t
  norm_num only [Nat.cast_ofNat] at hfinite
  have hpair := periodicSourceVector_feature_pairing S r f t
  rw [hpair] at hfinite
  have htail' := real_periodic_block_tail_error r hr f hf S (htail f hf) t
  simp only [complexifyContinuous, ContinuousMap.coe_mk] at htail'
  let logBound : ℝ := Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
    (d:ℝ)*(((d+2)*(M+(d*T+1))+H:ℕ):ℝ)*Real.log 2
  have hlog : Real.log (2*(Fintype.card
      (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K (M+L) H+1)):ℝ)+2) ≤
      logBound := by
    dsimp [logBound, L]
    exact AlignmentTorusSampling.samplingGridSize_log_card d K (M+(d*T+1)) H
  have hcoeff :
      (4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
        Real.log (2*(Fintype.card
          (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K (M+L) H+1)):ℝ)+2) /
        ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1) ≤
      (4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*logBound /
        ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1) := by
    calc
      _ = ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)/
          ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1)) *
          Real.log (2*(Fintype.card
            (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K (M+L) H+1)):ℝ)+2) := by ring
      _ ≤ ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)/
          ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1))*logBound :=
        mul_le_mul_of_nonneg_left hlog (by
        apply mul_nonneg
        · positivity
        · exact polynomialBudget_nonneg (by positivity) (d-1))
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_sqrt hcoeff
  have hfiniteBound : |(∑ s∈S,(block s f t).re)-y t| ≤
      ((2:ℝ)^H)⁻¹ + Real.sqrt
        ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*logBound /
          ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1)) := by
    calc
      _ ≤ (((2:ℝ)^H)⁻¹) + Real.sqrt
        ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
          Real.log (2*(Fintype.card
            (Fin d → Fin (AlignmentTorusSampling.samplingGridSize d K (M+L) H+1)):ℝ)+2) /
          ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1)) := by
        convert hfinite using 1 <;> norm_num
      _ ≤ _ := by simpa [add_comm] using add_le_add_left hsqrt (((2:ℝ)^H)⁻¹)
  have hsplit := abs_sub_le (f t) (∑ s∈S,(block s f t).re) (y t)
  calc
    |f t-y t| ≤ |f t-∑ s∈S,(block s f t).re|+
        |(∑ s∈S,(block s f t).re)-y t| := hsplit
    _ ≤ ε+(((2:ℝ)^H)⁻¹+
        Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
          logBound /
              ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1))) := by
      exact add_le_add htail' hfiniteBound
    _ = _ := by ring

theorem periodicShapeBox_complement_grade {d T : ℕ}
    (s : Fin d → ℕ) (hs : s ∉ periodicShapeBox (d:=d) T) :
    T ≤ ∑ i,s i := by
  classical
  by_contra h
  have hsum : ∑ i,s i ≤ T := by omega
  apply hs
  unfold periodicShapeBox
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_range.mpr
  have hcoord := Finset.single_le_sum
    (fun i hi => Nat.zero_le (s i)) (Finset.mem_univ j)
  omega

theorem periodic_sobolev_rank_le_layer_index {d n G : ℕ} (hd : 2≤d)
    (hG : 0<G) :
    2*5^d*(n+1)^(d-1)*2^n*G ≤
      (2*5^d*Nat.factorial (d-1)*G)*Fintype.card (LayerIndex d n) := by
  have hfact : 0<(Nat.factorial (d-1):ℝ) := by positivity
  have hGR : (0:ℝ)≤(G:ℝ) := by exact_mod_cast (Nat.zero_le G)
  have hlow := hyperbolicCount_lower_shift (show 1≤d by omega) n
  have hmain :
      (2:ℝ)*5^d*((n+1:ℕ):ℝ)^(d-1)*(2:ℝ)^n*(G:ℝ) ≤
        (2:ℝ)*5^d*(Nat.factorial (d-1):ℝ)*(G:ℝ)*
          (Fintype.card (LayerIndex d n):ℝ) := by
    rw [layerIndex_card d n (by omega : 0<d)]
    simp only [Nat.cast_mul, Nat.cast_pow]
    have hchoose : (Nat.choose (n+d-1) (d-1):ℝ)=hyperbolicCount d n := by
      simp [hyperbolicCount]
    rw [hchoose]
    have hlow' : ((n+1:ℕ):ℝ)^(d-1)/(Nat.factorial (d-1):ℝ) ≤
        hyperbolicCount d n := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlow
    have hpoly : ((n+1:ℕ):ℝ)^(d-1) ≤
        hyperbolicCount d n*(Nat.factorial (d-1):ℝ) :=
      (div_le_iff₀ hfact).mp hlow'
    let C : ℝ := (2:ℝ)*5^d*(2:ℝ)^n*(G:ℝ)
    have hC : 0≤C := by dsimp [C]; positivity
    calc
      (2:ℝ)*5^d*((n+1:ℕ):ℝ)^(d-1)*(2:ℝ)^n*(G:ℝ) =
          C*((n+1:ℕ):ℝ)^(d-1) := by dsimp [C]; ring
      _ ≤ C*(hyperbolicCount d n*(Nat.factorial (d-1):ℝ)) :=
        mul_le_mul_of_nonneg_left hpoly hC
      _ = (2:ℝ)*5^d*(Nat.factorial (d-1):ℝ)*(G:ℝ)*
          ((2:ℝ)^n*hyperbolicCount d n) := by dsimp [C]; ring
  exact_mod_cast hmain

/-- A cutoff multiple that makes the geometric omitted-block tail decay at
least like the target Sobolev scale. -/
theorem exists_periodic_tail_cutoff {r : ℝ} (hr : 1/2<r) :
    ∃ q' : ℝ, ∃ C : ℕ,
      (2:ℝ)^(1/2-r)<q' ∧ q'<1 ∧ 0<C ∧
      (((2:ℝ)^(1/2-r))/q')^C ≤ (2:ℝ)^(-r) := by
  let q₀ : ℝ := (2:ℝ)^(1/2-r)
  have hq₀pos : 0<q₀ := by dsimp [q₀]; positivity
  have hq₀one : q₀<1 := by
    dsimp [q₀]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  let q' : ℝ := (q₀+1)/2
  have hq'low : q₀<q' := by dsimp [q']; linarith
  have hq'high : q'<1 := by dsimp [q']; linarith
  let γ : ℝ := q₀/q'
  have hγpos : 0<γ := div_pos hq₀pos (by linarith)
  have hγone : γ<1 := (div_lt_one (by linarith)).2 hq'low
  have hpow : Tendsto (fun n : ℕ => γ^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγpos.le hγone
  have hev : ∀ᶠ n : ℕ in atTop, γ^n < (2:ℝ)^(-r) :=
    hpow.eventually (Iio_mem_nhds (by positivity : 0<(2:ℝ)^(-r)))
  obtain ⟨C,hC⟩ := eventually_atTop.1 hev
  have hCpos : 0<C := by
    by_contra h
    have hC0 : C=0 := by omega
    subst C
    have h0 : (2:ℝ)^(-r)<1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2)
      linarith
    have hbad := hC 0 le_rfl
    dsimp [γ] at hbad
    norm_num at hbad
    linarith
  refine ⟨q',C,hq'low,hq'high,hCpos,?_⟩
  have hγC : γ^C < (2:ℝ)^(-r) := hC C le_rfl
  simpa [γ,q₀] using hγC.le

private theorem periodic_rho_power_ratio {r : ℝ} (n : ℕ) :
    ((2:ℝ)^(1-2*r))^n/(2:ℝ)^n=(2:ℝ)^(-2*r*(n:ℝ)) := by
  have hnum : ((2:ℝ)^(1-2*r))^n=(2:ℝ)^((1-2*r)*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have hden : (2:ℝ)^n=(2:ℝ)^(n:ℝ) := by
    exact (Real.rpow_natCast (2:ℝ) n).symm
  rw [hnum,hden,div_eq_mul_inv]
  rw [← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  push_cast
  ring

/-- The geometric omitted-block tail is discharged for the concrete box.
This gives an unconditional actual C-space width estimate with only explicit
integer cutoffs and a free geometric ratio `q'`. -/
theorem periodic_sobolev_box_width_upper
    {d M T H K m : ℕ} (hd : 0<d) (r : ℝ) (hr : 1/2<r)
    {q ρ q' : ℝ} (hρ : 0<ρ) (hq : 0<q) (hq1 : q<1) (hρq : ρ<q)
    (hρeq : ρ=(2:ℝ)^(1-2*r))
    (hqq' : (2:ℝ)^(1/2-r)<q') (hq' : q'<1)
    (hK : 0<K) (hKC : 2*AlignmentTorusSampling.samplingConstant d ≤ (K:ℝ))
    (hε : 0≤ Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^T *
      ∑' s : Fin d → ℕ, q'^(∑ i,s i))
    (hrank :
      2*5^d*(M+1)^(d-1)*2^M*Nat.ceil (1+(1-q)⁻¹) ≤ m) :
    kolmogorovWidth {f : RealPeriodic d | SobolevUnitBall 2 r f} m ≤
      ENNReal.ofReal (
        Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^T *
          ∑' s : Fin d → ℕ, q'^(∑ i,s i) + ((2:ℝ)^H)⁻¹ +
          Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
            (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
              (d:ℝ)*(((d+2)*(M+(d*T+1))+H:ℕ):ℝ)*Real.log 2) /
              ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*
            polynomialBudget (ρ/q) (d-1))) := by
  classical
  let tail : ℝ := Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^T *
      ∑' s : Fin d → ℕ, q'^(∑ i,s i)
  have htail : ∀ f : RealPeriodic d, SobolevUnitBall 2 r f →
      ∑' s : ((periodicShapeBox (d:=d) T)ᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖ ≤ tail := by
    intro f hf
    exact sobolev_two_uniform_tail (periodicShapeBox (d:=d) T) r hr q' hqq' hq'
      (periodicShapeBox_complement_grade) f hf
  obtain ⟨W,hW,happrox⟩ := periodic_sobolev_box_uniform_approximation
    (d:=d) (M:=M) (T:=T) (H:=H) (K:=K) hd r hr htail hρ hq hq1 hρq hρeq hK hKC
  have hWCard : Module.rank ℝ W ≤
      ((2*5^d*(M+1)^(d-1)*2^M)*Nat.ceil (1+(1-q)⁻¹):Cardinal) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hW
  have hrankCard :
      ((2*5^d*(M+1)^(d-1)*2^M)*Nat.ceil (1+(1-q)⁻¹):Cardinal) ≤ (m:Cardinal) := by
    exact_mod_cast hrank
  have hWm : Module.rank ℝ W ≤ (m:Cardinal) := hWCard.trans hrankCard
  have hE : 0 ≤ tail+((2:ℝ)^H)⁻¹+
      Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((M+1:ℕ):ℝ)^(d-1)*ρ^M)*
        (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
          (d:ℝ)*(((d+2)*(M+(d*T+1))+H:ℕ):ℝ)*Real.log 2) /
            ((2*5^d*(M+1)^(d-1)*2^M):ℝ))*polynomialBudget (ρ/q) (d-1)) := by
    exact add_nonneg (add_nonneg hε (inv_nonneg.mpr (by positivity))) (Real.sqrt_nonneg _)
  unfold kolmogorovWidth
  refine le_trans (iInf_le (fun V : {V : Submodule ℝ C(UnitAddTorus (Fin d),ℝ) //
      Module.rank ℝ V ≤ (m:Cardinal)} => approximationError
        {f : RealPeriodic d | SobolevUnitBall 2 r f} V.1) ⟨W,hWm⟩) ?_
  apply approximationError_le_of_pointwise _ W hE
  intro f hf
  obtain ⟨y,hy,hyerr⟩ := happrox f hf
  refine ⟨y,hy,?_⟩
  apply (ContinuousMap.norm_le (f-y) hE).2
  intro t
  have ht := hyerr t
  simpa [Real.norm_eq_abs] using ht

/-- Sobolev-2 periodic widths on the hyperbolic layer scale have the sharp
dyadic upper bound. This is the quantitative bridge from the finite Fourier
feature construction to the all-index endpoint extraction. -/
theorem periodic_sobolev_dyadic_width_upper
    {d : ℕ} (hd : 2≤d) {r : ℝ} (hr : 1/2<r) :
    ∃ A : ℕ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ n : ℕ,
      kolmogorovWidth {f : RealPeriodic d | SobolevUnitBall 2 r f}
        (A*Fintype.card (LayerIndex d n)) ≤
        ENNReal.ofReal (B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^(1/2:ℝ)) := by
  classical
  obtain ⟨q',CT,hq'lo,hq'hi,hCTpos,hCT⟩ := exists_periodic_tail_cutoff hr
  obtain ⟨K,hK,hKC⟩ := AlignmentTorusSampling.exists_sampling_integer d
  have hq'pos : 0<q' := by
    have hq0pos : 0<(2:ℝ)^(1/2-r) := Real.rpow_pos_of_pos (by norm_num) _
    exact hq0pos.trans hq'lo
  let ρ : ℝ := (2:ℝ)^(1-2*r)
  let q : ℝ := (1+ρ)/2
  let G : ℕ := Nat.ceil (1+(1-q)⁻¹)
  let A : ℕ := 2*5^d*Nat.factorial (d-1)*G
  let CH : ℕ := Nat.ceil r
  let logCoeff : ℝ := Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
      (d:ℝ)*((d+2)*(2+d*CT)+CH)*Real.log 2
  let tailCoeff : ℝ := Real.sqrt ((5:ℝ)^d)*
      ∑' s : Fin d → ℕ, q'^(∑ i,s i)
  let mainCoeff : ℝ := Real.sqrt
      (4*(10000:ℝ)^2*logCoeff*polynomialBudget (ρ/q) (d-1))
  let B : ℝ := tailCoeff+1+mainCoeff
  have hρpos : 0<ρ := by dsimp [ρ]; positivity
  have hρone : ρ<1 := by
    dsimp [ρ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hqρ : ρ<q := by dsimp [q]; linarith
  have hq0 : 0<q := by dsimp [q]; linarith
  have hq1 : q<1 := by dsimp [q]; linarith
  have hG : 0<G := by
    dsimp [G]
    have hden : 0<1-q := by linarith
    have hinv : 0<(1-q)⁻¹ := inv_pos.mpr hden
    exact Nat.ceil_pos.mpr (by linarith)
  have hA : 0<A := by dsimp [A]; positivity
  have hlogCoeff : 0<logCoeff := by
    dsimp [logCoeff]
    have hlog4 : 0<Real.log 4 := Real.log_pos (by norm_num)
    have hlogK : 0≤Real.log ((K:ℝ)+1) := Real.log_nonneg (by norm_cast; omega)
    have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hbudget : 0≤polynomialBudget (ρ/q) (d-1) :=
    polynomialBudget_nonneg (by positivity) (d-1)
  have hmainCoeff : 0≤mainCoeff := by dsimp [mainCoeff]; positivity
  have htailCoeff : 0≤tailCoeff := by
    dsimp [tailCoeff]
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply tsum_nonneg
    intro s
    exact pow_nonneg hq'pos.le _
  have hB : 0<B := by dsimp [B]; linarith
  refine ⟨A,hA,B,hB,?_⟩
  intro n
  let T : ℕ := CT*n
  let H : ℕ := CH*n
  have hH : r*(n:ℝ)≤(H:ℝ) := by
    dsimp [H]
    have hceil : r≤(Nat.ceil r:ℝ) := by exact_mod_cast (Nat.le_ceil r)
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hceil (by positivity)
  have hgrid : ((2:ℝ)^H)⁻¹ ≤ (2:ℝ)^(-r*(n:ℝ)) := by
    have hid : ((2:ℝ)^H)⁻¹=(2:ℝ)^(-(H:ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [hid]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    linarith
  have htailPow : (((2:ℝ)^(1/2-r))/q')^T ≤
      (2:ℝ)^(-r*(n:ℝ)) := by
    dsimp [T]
    have hbase : 0≤(((2:ℝ)^(1/2-r))/q') := by positivity
    have hpow := pow_le_pow_left₀ (by positivity : 0≤(((2:ℝ)^(1/2-r))/q')^CT) hCT n
    have hiden : ((2:ℝ)^(-r))^n=(2:ℝ)^(-r*(n:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    calc
      _ = ((((2:ℝ)^(1/2-r))/q')^CT)^n := by rw [pow_mul]
      _ ≤ ((2:ℝ)^(-r))^n := hpow
      _ = _ := hiden
  have hlogbound :
      Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
        (d:ℝ)*(((d+2)*(n+(d*T+1))+H:ℕ):ℝ)*Real.log 2 ≤
      logCoeff*((n:ℝ)+1) := by
    dsimp [logCoeff,T,H]
    have hn : 0≤(n:ℝ) := by positivity
    have hcoef : 0≤((d+2)*(2+d*CT)+CH:ℕ) := by positivity
    have hshape :
        (d+2)*(n+(d*(CT*n)+1))+CH*n ≤
          ((d+2)*(2+d*CT)+CH)*(n+1) := by
      calc
        (d+2)*(n+(d*(CT*n)+1))+CH*n ≤
            (d+2)*(n+(d*(CT*n)+1))+CH*n+((d+2)*(n+1+d*CT)+CH) := Nat.le_add_right _ _
        _ = ((d+2)*(2+d*CT)+CH)*(n+1) := by ring
    have hshapeR :
        (((d+2)*(n+(d*(CT*n)+1))+CH*n:ℕ):ℝ) ≤
          (((d+2)*(2+d*CT)+CH:ℕ):ℝ)*((n:ℝ)+1) := by exact_mod_cast hshape
    have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hshapeR' := mul_le_mul_of_nonneg_left hshapeR (by positivity : 0≤(d:ℝ))
    have hmul := mul_le_mul_of_nonneg_right hshapeR' hlog
    have hlog4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    have hlogK : 0≤(d:ℝ)*Real.log ((K:ℝ)+1) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_cast; omega))
    have hconst : 0≤Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1) := by positivity
    have hn1 : 1≤(n:ℝ)+1 := by linarith
    calc
      _ ≤ Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
          ((d:ℝ)*(((d+2)*(2+d*CT)+CH:ℕ):ℝ)*Real.log 2)*((n:ℝ)+1) := by
            nlinarith [hmul]
      _ ≤ (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1))*((n:ℝ)+1)+
          ((d:ℝ)*(((d+2)*(2+d*CT)+CH:ℕ):ℝ)*Real.log 2)*((n:ℝ)+1) := by
            apply add_le_add
            · calc
                _ = (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1))*1 := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left hn1 hconst
            · exact le_rfl
      _ = logCoeff*((n:ℝ)+1) := by dsimp [logCoeff]; push_cast; ring_nf
  have htail_nonneg : 0≤tailCoeff := htailCoeff
  have hrank :
      2*5^d*(n+1)^(d-1)*2^n*G ≤ A*Fintype.card (LayerIndex d n) := by
    dsimp [A]
    exact periodic_sobolev_rank_le_layer_index hd hG
  have hε : 0≤Real.sqrt ((5:ℝ)^d)*
      (((2:ℝ)^(1/2-r))/q')^T*∑'s:Fin d→ℕ,q'^(∑i,s i) := by
    apply mul_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by positivity) _)
    · apply tsum_nonneg
      intro s
      exact pow_nonneg hq'pos.le _
  have hρeq : ρ=(2:ℝ)^(1-2*r) := rfl
  have hbox := periodic_sobolev_box_width_upper
    (d:=d) (M:=n) (T:=T) (H:=H) (K:=K)
    (m:=A*Fintype.card (LayerIndex d n)) (by omega) r hr
    hρpos hq0 hq1 hqρ hρeq hq'lo hq'hi hK hKC hε hrank
  let lam : ℝ := (2:ℝ)^(-r*(n:ℝ))
  let logBound : ℝ := Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
    (d:ℝ)*(((d+2)*(n+(d*T+1))+H:ℕ):ℝ)*Real.log 2
  let rad : ℝ := (4*(10000:ℝ)^2*
      (2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n)*logBound/
      (2*(5:ℝ)^d*((n:ℝ)+1)^(d-1)*(2:ℝ)^n))*
      polynomialBudget (ρ/q) (d-1)
  have hLamPos : 0<lam := by dsimp [lam]; positivity
  have hsn : 1≤Real.sqrt ((n:ℝ)+1) := by
    have hsquare := Real.sq_sqrt (show 0≤(n:ℝ)+1 by positivity)
    nlinarith [Real.sqrt_nonneg ((n:ℝ)+1), hsquare]
  have htailErr :
      Real.sqrt ((5:ℝ)^d)*(((2:ℝ)^(1/2-r))/q')^T*
          ∑'s:Fin d→ℕ,q'^(∑i,s i) ≤ tailCoeff*lam := by
    dsimp [tailCoeff]
    calc
      _ ≤ Real.sqrt ((5:ℝ)^d)*lam*∑'s:Fin d→ℕ,q'^(∑i,s i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htailPow (Real.sqrt_nonneg _)) (by
            apply tsum_nonneg
            intro s
            exact pow_nonneg hq'pos.le _)
      _ = _ := by ring
  have hgridErr : ((2:ℝ)^H)⁻¹ ≤ lam*Real.sqrt ((n:ℝ)+1) := by
    calc
      _ ≤ lam := hgrid
      _ ≤ lam*Real.sqrt ((n:ℝ)+1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsn hLamPos.le
  have hheadpos : 0<(2*5^d*(n+1)^(d-1)*2^n:ℕ) := by positivity
  have hratio : ρ^n/(2:ℝ)^n=lam^2 := by
    rw [hρeq, periodic_rho_power_ratio]
    have hLamSq : lam^2=(2:ℝ)^(-2*r*(n:ℝ)) := by
      dsimp [lam]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      congr 1
      push_cast
      ring
    exact hLamSq.symm
  have hmainSq : mainCoeff^2=4*(10000:ℝ)^2*logCoeff*polynomialBudget (ρ/q) (d-1) := by
    dsimp [mainCoeff]
    exact Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) hlogCoeff.le) hbudget)
  have hradEq : rad =
      4*(10000:ℝ)^2*(ρ^n/(2:ℝ)^n)*logBound*
        polynomialBudget (ρ/q) (d-1) := by
    dsimp [rad]
    have hcast : ((n+1:ℕ):ℝ)=(n:ℝ)+1 := by norm_num
    rw [hcast]
    have hden : (0:ℝ)<(2*5^d*((n:ℝ)+1)^(d-1)*(2:ℝ)^n) := by positivity
    field_simp
    <;> push_cast
    <;> ring_nf
  have hradle : rad ≤ (mainCoeff*lam*Real.sqrt ((n:ℝ)+1))^2 := by
    rw [hradEq, hratio]
    have hlog := hlogbound
    calc
      _ ≤ 4*(10000:ℝ)^2*lam^2*(logCoeff*((n:ℝ)+1))*
          polynomialBudget (ρ/q) (d-1) := by
            gcongr
      _ = (mainCoeff*lam*Real.sqrt ((n:ℝ)+1))^2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (show 0≤(n:ℝ)+1 by positivity), hmainSq]
            ring
  have hmainErr : Real.sqrt rad ≤ mainCoeff*lam*Real.sqrt ((n:ℝ)+1) := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, hradle⟩
  have hErr :
      Real.sqrt ((5:ℝ)^d)*(((2:ℝ)^(1/2-r))/q')^T*
          ∑'s:Fin d→ℕ,q'^(∑i,s i) + ((2:ℝ)^H)⁻¹ + Real.sqrt rad ≤
        B*lam*Real.sqrt ((n:ℝ)+1) := by
    dsimp [B]
    calc
      _ ≤ tailCoeff*lam*Real.sqrt ((n:ℝ)+1)+
          lam*Real.sqrt ((n:ℝ)+1)+
          mainCoeff*lam*Real.sqrt ((n:ℝ)+1) := by
            apply add_le_add
            · exact add_le_add
                (htailErr.trans (calc
                  tailCoeff*lam ≤ tailCoeff*lam*Real.sqrt ((n:ℝ)+1) := by
                    calc
                      _ = tailCoeff*lam*1 := by ring
                      _ ≤ _ := mul_le_mul_of_nonneg_left hsn
                        (mul_nonneg htailCoeff hLamPos.le))) hgridErr
            · exact hmainErr
      _ = _ := by ring
  have hErr' :
      (Real.sqrt ((5:ℝ)^d)*(((2:ℝ)^(1/2-r))/q')^T*
          ∑'s:Fin d→ℕ,q'^(∑i,s i) + ((2:ℝ)^H)⁻¹ +
        Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n)*logBound/
          (2*(5:ℝ)^d*((n:ℝ)+1)^(d-1)*(2:ℝ)^n))*
          polynomialBudget (ρ/q) (d-1))) ≤
      B*lam*Real.sqrt ((n:ℝ)+1) := by
    simpa [rad,logBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hErr
  have hErr'' :
      (Real.sqrt ((5:ℝ)^d)*(((2:ℝ)^(1/2-r))/q')^T*
          ∑'s:Fin d→ℕ,q'^(∑i,s i) + ((2:ℝ)^H)⁻¹ +
        Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n)*
          (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
            (d:ℝ)*(((d+2)*(n+(d*T+1))+H:ℕ):ℝ)*Real.log 2)/
          (2*(5:ℝ)^d*((n:ℝ)+1)^(d-1)*(2:ℝ)^n))*
          polynomialBudget (ρ/q) (d-1))) ≤
      B*lam*Real.sqrt ((n:ℝ)+1) := by
    simpa [logBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hErr'
  have hErr''' :
      (Real.sqrt ((5:ℝ)^d)*(((2:ℝ)^(1/2-r))/q')^T*
          ∑'s:Fin d→ℕ,q'^(∑i,s i) + ((2:ℝ)^H)⁻¹ +
        Real.sqrt ((4*(10000:ℝ)^2*(2*(5:ℝ)^d*((n+1:ℕ):ℝ)^(d-1)*ρ^n)*
          (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
            (d:ℝ)*(((d+2)*(n+(d*T+1))+H:ℕ):ℝ)*Real.log 2)/
          (2*(5:ℝ)^d*((n:ℝ)+1)^(d-1)*(2:ℝ)^n))*
          polynomialBudget (ρ/q) (d-1))) ≤
      B*lam*((n:ℝ)+1)^(1/2:ℝ) := by
    calc
      _ ≤ B*lam*Real.sqrt ((n:ℝ)+1) := hErr''
      _ = _ := by rw [Real.sqrt_eq_rpow]
  have hwidth : kolmogorovWidth {f : RealPeriodic d | SobolevUnitBall 2 r f}
      (A*Fintype.card (LayerIndex d n)) ≤
      ENNReal.ofReal (B*lam*((n:ℝ)+1)^(1/2:ℝ)) :=
    hbox.trans (ENNReal.ofReal_le_ofReal hErr''')
  simpa [lam,Real.sqrt_eq_rpow] using hwidth

/-- The same dyadic width estimate in the actual L-infinity image space.
The comparison uses the isometric continuous-to-L-infinity embedding under
the full-support torus volume measure. -/
theorem periodic_sobolev_dyadic_width_upper_linf
    {d : ℕ} (hd : 2≤d) (r : ℝ) (hr : 1/2<r) :
    ∃ A : ℕ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ n : ℕ,
      kolmogorovWidth
        ((ContinuousMap.toLp ⊤ (volume : Measure (UnitAddTorus (Fin d))) ℝ) ''
          {f : RealPeriodic d | SobolevUnitBall 2 r f})
        (A*Fintype.card (LayerIndex d n)) ≤
          ENNReal.ofReal (B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^(1/2:ℝ)) := by
  obtain ⟨A,hA,B,hB,hupper⟩ :=
    periodic_sobolev_dyadic_width_upper (d:=d) hd (r:=r) hr
  refine ⟨A,hA,B,hB,?_⟩
  intro n
  have hle := continuous_width_ge_LInfinity_width
    (μ:= (volume : Measure (UnitAddTorus (Fin d))))
    ({f : RealPeriodic d | SobolevUnitBall 2 r f})
    (A*Fintype.card (LayerIndex d n))
  have h := hle.trans (hupper n)
  simpa [AlignmentAmbientWidth.continuousToLInfinity,
    BrownianSharp.Latest.periodicLInfinityImage] using h

/-- Sharp all-index Sobolev-2 width upper bound in the manuscript's actual
L-infinity target space. -/
theorem periodic_sobolev_linf_all_index_width_upper
    {d : ℕ} (hd : 2≤d) (r : ℝ) (hr : 1/2<r) :
    ∃ C : ℝ, 0<C ∧ ∃ m₁ : ℕ, 8*1 ≤ m₁ ∧ ∀ m : ℕ, m₁≤m →
      kolmogorovWidth
        (BrownianSharp.Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall 2 r f}) m ≤
        ENNReal.ofReal (C*logarithmicIndexRate r
          (r*((d-1:ℕ):ℝ)+(1/2:ℝ)) m) := by
  obtain ⟨A,hA,B,hB,hdyad⟩ :=
    periodic_sobolev_dyadic_width_upper_linf (d:=d) hd r hr
  have hrpos : 0<r := by linarith
  obtain ⟨C,hC,m₁,hm₁,hupper⟩ := all_index_width_rate_of_dyadic_layer_bound hd
    (BrownianSharp.Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall 2 r f})
    A hA r (1/2) B hrpos (by norm_num) hB 0 (by
      intro n hn
      exact hdyad n)
  refine ⟨C,hC,m₁,?_ ,hupper⟩
  have hAone : 1≤A := by omega
  omega

/-- Every finite periodic Sobolev exponent `p≥2` inherits the same upper
bound from the Hilbert ball on the probability torus. -/
theorem periodic_sobolev_linf_all_index_width_upper_finite_p
    {d : ℕ} (hd : 2≤d) (p : ENNReal) (hp : 2≤p) (hptop : p≠⊤)
    (r : ℝ) (hr : 1/2<r) :
    ∃ C : ℝ, 0<C ∧ ∃ m₁ : ℕ, 8≤m₁ ∧ ∀ m : ℕ, m₁≤m →
      kolmogorovWidth
        (BrownianSharp.Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall p.toReal r f}) m ≤
        ENNReal.ofReal (C*logarithmicIndexRate r
          (r*((d-1:ℕ):ℝ)+(1/2:ℝ)) m) := by
  obtain ⟨C,hC,m₁,hm₁,hupper⟩ :=
    periodic_sobolev_linf_all_index_width_upper hd r hr
  have hpR : 2≤p.toReal := by
    have h2top : (2:ENNReal)≠⊤ := by norm_num
    have hreal := (ENNReal.toReal_le_toReal h2top hptop).2 hp
    simpa using hreal
  have hsub :
      BrownianSharp.Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall p.toReal r f} ⊆
      BrownianSharp.Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall 2 r f} := by
    rintro y ⟨f,hf,rfl⟩
    exact ⟨f,AlignmentPeriodicUpperReduction.sobolevUnitBall_two_of_two_le
      hpR r f hf,rfl⟩
  refine ⟨C,hC,m₁,hm₁,?_⟩
  intro m hm
  exact AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set hsub m |>.trans
    (hupper m hm)

end BrownianSharp.AlignmentPeriodicWidthUniformUpper
