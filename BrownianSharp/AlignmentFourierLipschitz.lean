import BrownianSharp.AlignmentTorusSampling
import BrownianSharp.AlignmentPeriodicWidthRealification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open scoped BigOperators
open Set
namespace BrownianSharp.AlignmentTorusSampling
open UnitAddTorus

theorem fourier_point_add (n : ℤ) (x y : AddCircle (1:ℝ)) :
    fourier n (x+y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_sub_one_bound (n : ℤ) (x : AddCircle (1:ℝ)) :
    ‖fourier n x - 1‖ ≤ 2*Real.pi*|(n:ℝ)| *‖x‖ := by
  let z : ℝ := AddCircle.equivIco (1:ℝ) (-(1/2:ℝ)) x
  have hzlo : -(1/2:ℝ) ≤ z := (AddCircle.equivIco (1:ℝ) (-(1/2:ℝ)) x).property.1
  have hzhi : z < (1/2:ℝ) := by
    have h := (AddCircle.equivIco (1:ℝ) (-(1/2:ℝ)) x).property.2
    dsimp [z] at *
    linarith
  have hzabs : |z| ≤ (1/2:ℝ) := abs_le.mpr ⟨hzlo, hzhi.le⟩
  have heq : (z : AddCircle (1:ℝ)) = x := AddCircle.coe_equivIco
  have hnorm : ‖x‖ = |z| := by
    have hn := (AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero).2 (by simpa using hzabs)
    exact heq ▸ hn
  have he : fourier n x = Complex.exp (Complex.I * ((2*Real.pi*(n:ℝ)*z:ℝ):ℂ)) := by
    calc
      fourier n x = fourier n (z : AddCircle (1:ℝ)) :=
        congrArg (fourier n) heq.symm
      _ = _ := by
        rw [fourier_coe_apply]
        congr 1
        push_cast
        ring
  rw [he]
  calc
    ‖Complex.exp (Complex.I * ((2*Real.pi*(n:ℝ)*z:ℝ):ℂ))-1‖ ≤ ‖(2*Real.pi*(n:ℝ)*z:ℝ)‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2*Real.pi*|(n:ℝ)| *‖x‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2), hnorm]

theorem fourier_dist_bound (n : ℤ) (x y : AddCircle (1:ℝ)) :
    ‖fourier n x-fourier n y‖ ≤
      2*Real.pi*|(n:ℝ)| *dist x y := by
  have heq : fourier n x =
      fourier n (x-y)*fourier n y := by
    rw [← fourier_point_add]
    simp
  have hn : ‖fourier n y‖ = 1 := by
    simp only [fourier_apply, Circle.norm_coe]
  calc
    ‖fourier n x-fourier n y‖ =
        ‖(fourier n (x-y)-1)*fourier n y‖ := by
      congr 1
      rw [heq]
      ring
    _ = ‖fourier n (x-y)-1‖ := by rw [norm_mul, hn, mul_one]
    _ ≤ _ := by simpa only [dist_eq_norm] using fourier_sub_one_bound n (x-y)


theorem norm_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℂ) (hf : ∀ i, ‖f i‖=1) (hg : ∀ i, ‖g i‖=1) :
    ‖(∏ i ∈ s, f i)-(∏ i ∈ s, g i)‖ ≤ ∑ i ∈ s, ‖f i-g i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hid : f a*(∏ i ∈ s,f i)-g a*(∏ i ∈ s,g i) =
        (f a-g a)*(∏ i ∈ s,f i)+g a*((∏ i ∈ s,f i)-(∏ i ∈ s,g i)) := by ring
    rw [hid]
    calc
      ‖(f a-g a)*(∏ i ∈ s,f i)+g a*((∏ i ∈ s,f i)-(∏ i ∈ s,g i))‖ ≤
          ‖(f a-g a)*(∏ i ∈ s,f i)‖+‖g a*((∏ i ∈ s,f i)-(∏ i ∈ s,g i))‖ := norm_add_le _ _
      _ = ‖f a-g a‖+‖(∏ i ∈ s,f i)-(∏ i ∈ s,g i)‖ := by
        simp only [norm_mul, norm_prod, hf, hg, Finset.prod_const_one, mul_one, one_mul]
      _ ≤ _ := add_le_add le_rfl ih

theorem mFourier_dist_bound {d : ℕ} (n : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    ‖mFourier n x-mFourier n y‖ ≤
      (2*Real.pi*(∑ i, |(n i:ℝ)|))*dist x y := by
  classical
  change ‖(∏ i, fourier (n i) (x i))-(∏ i, fourier (n i) (y i))‖ ≤ _
  calc
    _ ≤ ∑ i, ‖fourier (n i) (x i)-fourier (n i) (y i)‖ :=
      norm_prod_sub_prod_le_sum Finset.univ _ _
        (fun _ => Circle.norm_coe _) (fun _ => Circle.norm_coe _)
    _ ≤ ∑ i, 2*Real.pi*|(n i:ℝ)| *dist x y := by
      apply Finset.sum_le_sum
      intro i _
      exact (fourier_dist_bound (n i) (x i) (y i)).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

open BrownianSharp.AlignmentPeriodicWidthRealification

theorem complexFeatureVector_sub {ι : Type*} [Fintype ι] (z w : ι → ℂ) :
    complexFeatureVector z-complexFeatureVector w =
      complexFeatureVector (fun i => z i-w i) := by
  ext p
  change complexFeatureCoord (z p.1) p.2-complexFeatureCoord (w p.1) p.2 =
    complexFeatureCoord (z p.1-w p.1) p.2
  rcases p with ⟨i,b⟩
  fin_cases b <;> simp [complexFeatureCoord] <;> ring

theorem complexFeatureVector_norm_le_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖complexFeatureVector z‖ ≤ ∑ i, ‖z i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).1
  rw [complexFeatureVector_norm_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

def periodicFeatureLipschitzConstant {d : ℕ} (S : Finset (Fin d → ℕ)) (r : ℝ) : ℝ := by
  classical
  exact ∑ i : BrownianSharp.AlignmentPeriodicWidthRealification.FourierCoeffIndex S,
    (2:ℝ)^(-r*∑ j, (i.1.1 j:ℝ))*(2*Real.pi*(∑ j, |(i.2.1 j:ℝ)|))

theorem periodicFeature_dist_bound {d : ℕ} (S : Finset (Fin d → ℕ)) (r : ℝ)
    (x y : UnitAddTorus (Fin d)) :
    ‖periodicFeatureVector S r x-periodicFeatureVector S r y‖ ≤
      periodicFeatureLipschitzConstant S r * dist x y := by
  classical
  rw [periodicFeatureVector, periodicFeatureVector, complexFeatureVector_sub]
  calc
    _ ≤ ∑ i : FourierCoeffIndex S,
        ‖((Real.rpow (2:ℝ) (-r*∑ j,(i.1.1 j:ℝ)):ℝ):ℂ)*mFourier i.2.1 x-
          ((Real.rpow (2:ℝ) (-r*∑ j,(i.1.1 j:ℝ)):ℝ):ℂ)*mFourier i.2.1 y‖ :=
      complexFeatureVector_norm_le_sum _
    _ ≤ ∑ i : FourierCoeffIndex S,
        ((2:ℝ)^(-r*∑ j,(i.1.1 j:ℝ))*(2*Real.pi*(∑ j,|(i.2.1 j:ℝ)|)))*dist x y := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by exact Real.rpow_nonneg (by norm_num) _ : 0 ≤ Real.rpow 2 (-r*∑ j,(i.1.1 j:ℝ)))]
      exact (mul_le_mul_of_nonneg_left (mFourier_dist_bound i.2.1 x y)
        (Real.rpow_nonneg (by norm_num) _)).trans_eq (by ring)
    _ = _ := by simp only [periodicFeatureLipschitzConstant, Finset.sum_mul]


theorem periodicFeatureLipschitzConstant_nonneg {d : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) :
    0 ≤ periodicFeatureLipschitzConstant S r := by
  classical
  unfold periodicFeatureLipschitzConstant
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem periodic_grid_partition {d : ℕ} (S : Finset (Fin d → ℕ)) (r : ℝ)
    (N : ℕ) (hN : 0<N) :
    ∃ φ : (Fin d → Fin (N+1)) → C(UnitAddTorus (Fin d),ℝ),
      (∀ j t, 0 ≤ φ j t) ∧ (∀ t, ∑ j, φ j t=1) ∧
      (∀ j t, φ j t ≠ 0 →
        ‖periodicFeatureVector S r t-periodicFeatureVector S r (torusGridPoint j)‖ ≤
          periodicFeatureLipschitzConstant S r*(2/(N:ℝ))) := by
  obtain ⟨φ,hφ,hsum,hsupport⟩ := torus_grid_partition N hN
  refine ⟨φ,hφ,hsum,?_⟩
  intro j t ht
  exact (periodicFeature_dist_bound S r t (torusGridPoint j)).trans
    (mul_le_mul_of_nonneg_left (hsupport j t ht).le
      (periodicFeatureLipschitzConstant_nonneg S r))

open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicReconstruction

theorem frequencyBox_coord_abs_le {d : ℕ} (s : Fin d → ℕ)
    (k : frequencyBox s) (j : Fin d) :
    |(k.val j:ℝ)| ≤ (2:ℝ)^(s j+1) := by
  classical
  have hk := Fintype.mem_piFinset.mp k.property j
  have hk' := Finset.mem_Icc.mp hk
  exact_mod_cast abs_le.mpr hk'

theorem grade_shape_card_le {d L : ℕ} (S : Finset (Fin d → ℕ))
    (hS : ∀ s∈S, ∑ j,s j ≤ L) : S.card ≤ (L+1)^d := by
  classical
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range (L+1)) := by
    intro s hs
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Finset.mem_range.mpr
    have hj : s j ≤ ∑ j,s j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hgrade := hS s hs
    omega
  have hc := Finset.card_le_card hsub
  simpa [Fintype.card_piFinset] using hc

theorem finite_fourier_index_card_le {d L : ℕ} (S : Finset (Fin d → ℕ))
    (hS : ∀ s∈S, ∑ j,s j ≤ L) :
    Fintype.card (FourierCoeffIndex S) ≤ (L+1)^d*5^d*2^L := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ s : S, Fintype.card (frequencyBox s.val) ≤
        ∑ _s : S, 5^d*2^L := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [Fintype.card_coe] using
        (frequencyBox_card_le s.val).trans
          (Nat.mul_le_mul_left (5^d) (Nat.pow_le_pow_right (by omega) (hS s.val s.property)))
    _ = S.card*(5^d*2^L) := by simp
    _ ≤ (L+1)^d*(5^d*2^L) := Nat.mul_le_mul_right _ (grade_shape_card_le S hS)
    _ = _ := by ring

theorem periodicFeatureLipschitzConstant_le {d L : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) (hr : 0≤r)
    (hS : ∀ s∈S, ∑ j,s j ≤ L) :
    periodicFeatureLipschitzConstant S r ≤
      (((L+1)^d*5^d*2^L:ℕ):ℝ)*(2*Real.pi*(d:ℝ)*(2:ℝ)^(L+1)) := by
  classical
  have hi : ∀ i : FourierCoeffIndex S,
      (2:ℝ)^(-r*∑ j,(i.1.1 j:ℝ))*(2*Real.pi*∑ j,|(i.2.1 j:ℝ)|) ≤
      2*Real.pi*(d:ℝ)*(2:ℝ)^(L+1) := by
    intro i
    have hweight : (2:ℝ)^(-r*∑ j,(i.1.1 j:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)))
    have hfreq : ∑ j,|(i.2.1 j:ℝ)| ≤ (d:ℝ)*(2:ℝ)^(L+1) := by
      calc
        ∑ j,|(i.2.1 j:ℝ)| ≤ ∑ _j : Fin d,(2:ℝ)^(L+1) := by
          apply Finset.sum_le_sum
          intro j _
          have hj : i.1.1 j ≤ L :=
            (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
              (hS i.1.1 i.1.2)
          exact (frequencyBox_coord_abs_le i.1.1 i.2 j).trans
            (pow_le_pow_right₀ (by norm_num) (by omega))
        _ = _ := by simp
    calc
      _ ≤ 1*(2*Real.pi*∑ j,|(i.2.1 j:ℝ)|) :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ 1*(2*Real.pi*((d:ℝ)*(2:ℝ)^(L+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfreq (by positivity)) (by norm_num)
      _ = _ := by ring
  unfold periodicFeatureLipschitzConstant
  calc
    _ ≤ ∑ _i : FourierCoeffIndex S, 2*Real.pi*(d:ℝ)*(2:ℝ)^(L+1) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card (FourierCoeffIndex S):ℝ)*(2*Real.pi*(d:ℝ)*(2:ℝ)^(L+1)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast finite_fourier_index_card_le S hS) (by positivity)


theorem succ_le_two_pow (L : ℕ) : L+1 ≤ 2^L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by norm_num)
    rw [pow_succ]
    omega

def samplingConstant (d : ℕ) : ℝ := 1+4*Real.pi*(d:ℝ)*(5:ℝ)^d

theorem samplingConstant_ge_one (d : ℕ) : 1 ≤ samplingConstant d := by
  unfold samplingConstant
  exact le_add_of_nonneg_right (by positivity)

theorem periodicFeatureLipschitzConstant_exp_bound {d L : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) (hr : 0≤r)
    (hS : ∀ s∈S, ∑ j,s j ≤ L) :
    periodicFeatureLipschitzConstant S r ≤
      samplingConstant d*(2:ℝ)^((d+2)*L) := by
  have hpoly : (L+1)^d ≤ 2^(d*L) := by
    calc
      (L+1)^d ≤ (2^L)^d := Nat.pow_le_pow_left (succ_le_two_pow L) d
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hpolyr : ((L+1:ℕ):ℝ)^d ≤ (2:ℝ)^(d*L) := by exact_mod_cast hpoly
  have hbound := periodicFeatureLipschitzConstant_le S r hr hS
  have halgebra :
      (((L+1)^d*5^d*2^L:ℕ):ℝ)*(2*Real.pi*(d:ℝ)*(2:ℝ)^(L+1)) =
      (((L+1:ℕ):ℝ)^d)*((4*Real.pi*(d:ℝ)*(5:ℝ)^d)*(2:ℝ)^(2*L)) := by
    push_cast
    rw [show 2*L=L+L by omega,pow_add,pow_succ]
    ring
  have hbase : 4*Real.pi*(d:ℝ)*(5:ℝ)^d ≤ samplingConstant d := by
    unfold samplingConstant
    linarith
  calc
    _ ≤ _ := hbound
    _ = _ := halgebra
    _ ≤ (2:ℝ)^(d*L)*((4*Real.pi*(d:ℝ)*(5:ℝ)^d)*(2:ℝ)^(2*L)) :=
      mul_le_mul_of_nonneg_right hpolyr (by positivity)
    _ = (4*Real.pi*(d:ℝ)*(5:ℝ)^d)*(2:ℝ)^((d+2)*L) := by
      rw [show (d+2)*L=d*L+2*L by ring,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (by positivity)

end BrownianSharp.AlignmentTorusSampling
