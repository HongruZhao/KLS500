import EntropyPolynomialProfile
import Mathlib.Analysis.Calculus.MeanValue

open Set
noncomputable section
namespace KLS.ConstantReduction

theorem entropyProfile_deriv_bound {s : ℝ} (hs : |s| ≤ 1) :
    |deriv entropyProfile s| ≤ 3 := by
  rw [entropyProfile_deriv]
  have ht1 : |(-2349/2000 : ℝ)*s^1| ≤ |(-2349/2000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht2 : |(-21141/80000 : ℝ)*s^3| ≤ |(-21141/80000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht3 : |(-190269/1280000 : ℝ)*s^5| ≤ |(-190269/1280000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht4 : |(-5137263/51200000 : ℝ)*s^7| ≤ |(-5137263/51200000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht5 : |(-601059771/8192000000 : ℝ)*s^9| ≤ |(-601059771/8192000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht6 : |(-91962144963/1638400000000 : ℝ)*s^11| ≤ |(-91962144963/1638400000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht7 : |(-5793615132669/131072000000000 : ℝ)*s^13| ≤ |(-5793615132669/131072000000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht8 : |(-7448933742003/209715200000000 : ℝ)*s^15| ≤ |(-7448933742003/209715200000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht9 : |(-1944171706662783/67108864000000000 : ℝ)*s^17| ≤ |(-1944171706662783/67108864000000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have ht10 : |(-64157666319871839/2684354560000000000 : ℝ)*s^19| ≤ |(-64157666319871839/2684354560000000000 : ℝ)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg s) hs)
  have htri : |entropyProfileD1 s| ≤ |(-2349/2000 : ℝ)| + |(-21141/80000 : ℝ)| + |(-190269/1280000 : ℝ)| + |(-5137263/51200000 : ℝ)| + |(-601059771/8192000000 : ℝ)| + |(-91962144963/1638400000000 : ℝ)| + |(-5793615132669/131072000000000 : ℝ)| + |(-7448933742003/209715200000000 : ℝ)| + |(-1944171706662783/67108864000000000 : ℝ)| + |(-64157666319871839/2684354560000000000 : ℝ)| := by
    unfold entropyProfileD1
    exact ((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7 + (-601059771/8192000000 : ℝ)*s^9 + (-91962144963/1638400000000 : ℝ)*s^11 + (-5793615132669/131072000000000 : ℝ)*s^13 + (-7448933742003/209715200000000 : ℝ)*s^15 + (-1944171706662783/67108864000000000 : ℝ)*s^17) ((-64157666319871839/2684354560000000000 : ℝ)*s^19)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7 + (-601059771/8192000000 : ℝ)*s^9 + (-91962144963/1638400000000 : ℝ)*s^11 + (-5793615132669/131072000000000 : ℝ)*s^13 + (-7448933742003/209715200000000 : ℝ)*s^15) ((-1944171706662783/67108864000000000 : ℝ)*s^17)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7 + (-601059771/8192000000 : ℝ)*s^9 + (-91962144963/1638400000000 : ℝ)*s^11 + (-5793615132669/131072000000000 : ℝ)*s^13) ((-7448933742003/209715200000000 : ℝ)*s^15)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7 + (-601059771/8192000000 : ℝ)*s^9 + (-91962144963/1638400000000 : ℝ)*s^11) ((-5793615132669/131072000000000 : ℝ)*s^13)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7 + (-601059771/8192000000 : ℝ)*s^9) ((-91962144963/1638400000000 : ℝ)*s^11)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5 + (-5137263/51200000 : ℝ)*s^7) ((-601059771/8192000000 : ℝ)*s^9)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3 + (-190269/1280000 : ℝ)*s^5) ((-5137263/51200000 : ℝ)*s^7)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1 + (-21141/80000 : ℝ)*s^3) ((-190269/1280000 : ℝ)*s^5)).trans (add_le_add (((abs_add_le ((-2349/2000 : ℝ)*s^1) ((-21141/80000 : ℝ)*s^3)).trans (add_le_add (ht1) ht2))) ht3))) ht4))) ht5))) ht6))) ht7))) ht8))) ht9))) ht10))
  norm_num at htri ⊢
  linarith only [htri]

theorem entropyProfile_concave : ConcaveOn ℝ (Icc (-1 : ℝ) 1) entropyProfile := by
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _) entropyProfile_contDiff.continuous.continuousOn
    (entropyProfile_contDiff.differentiable (by simp)).differentiableOn
  · rw [entropyProfile_deriv]
    exact (entropyProfileD1_contDiff.differentiable (by simp)).differentiableOn
  · intro x hx
    have hx' := interior_subset hx
    have ha : |x| ≤ 1 := abs_le.mpr hx'
    have hp : 0 < entropyProfile x := lt_of_lt_of_le (by norm_num) (entropyProfile_bounds ha).1
    have hc := entropyProfile_curvature ha
    change deriv (deriv entropyProfile) x ≤ 0
    nlinarith only [hp,hc]

theorem entropyProfile_tangent {s u : ℝ} (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    entropyProfile u ≤ entropyProfile s+deriv entropyProfile s*(u-s) := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
  have hu' : u ∈ Icc (-1 : ℝ) 1 := abs_le.mp hu
  rcases lt_trichotomy s u with hlt|rfl|hgt
  · have hh := entropyProfile_concave.slope_le_deriv hs' hu' hlt
      ((entropyProfile_contDiff.differentiable (by simp)).differentiableAt)
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hlt)).mp hh
    linarith only [hh']
  · simp
  · have hh := entropyProfile_concave.deriv_le_slope hu' hs' hgt
      ((entropyProfile_contDiff.differentiable (by simp)).differentiableAt)
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hgt)).mp hh
    nlinarith only [hh']

def scaledEntropyProfile (B s : ℝ) : ℝ := B*entropyProfile (s/B)

theorem scaledEntropyProfile_contDiff (B : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledEntropyProfile B) := by
  unfold scaledEntropyProfile
  exact contDiff_const.mul (entropyProfile_contDiff.comp (contDiff_id.div_const B))

theorem scaledEntropyProfile_hasDerivAt {B : ℝ} (hB : 0 < B) (s : ℝ) :
    HasDerivAt (scaledEntropyProfile B) (entropyProfileD1 (s/B)) s := by
  convert ((entropyProfile_hasDerivAt (s/B)).comp s ((hasDerivAt_id s).div_const B)).const_mul B using 1
  · rfl
  · field_simp

theorem scaledEntropyProfile_deriv {B : ℝ} (hB : 0 < B) :
    deriv (scaledEntropyProfile B) = fun s => entropyProfileD1 (s/B) := by
  exact funext fun s => (scaledEntropyProfile_hasDerivAt hB s).deriv

theorem scaledEntropyProfile_second_deriv {B : ℝ} (hB : 0 < B) :
    deriv (deriv (scaledEntropyProfile B)) = fun s => entropyProfileD2 (s/B)/B := by
  rw [scaledEntropyProfile_deriv hB]
  funext s
  simpa only [Function.comp_def,id_eq,mul_one,div_eq_mul_inv,one_mul] using
    ((entropyProfileD1_hasDerivAt (s/B)).comp s ((hasDerivAt_id s).div_const B)).deriv

theorem scaledEntropyProfile_bounds {B s : ℝ} (hB : 0 < B) (hs : |s| ≤ B) :
    3*B/20 ≤ scaledEntropyProfile B s ∧ scaledEntropyProfile B s ≤ 87*B/100 := by
  have ha : |s/B| ≤ 1 := by
    rw [abs_div,abs_of_pos hB]
    exact (div_le_one hB).mpr hs
  have hb := entropyProfile_bounds ha
  unfold scaledEntropyProfile
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hb.1 hB.le]
  · nlinarith only [mul_le_mul_of_nonneg_left hb.2 hB.le]

theorem scaledEntropyProfile_abs_bound {B s : ℝ} (hB : 0 < B) (hs : |s| ≤ B) :
    |scaledEntropyProfile B s| ≤ 87*B/100 := by
  rw [abs_of_nonneg (le_trans (by positivity) (scaledEntropyProfile_bounds hB hs).1)]
  exact (scaledEntropyProfile_bounds hB hs).2

theorem scaledEntropyProfile_deriv_bound {B s : ℝ} (hB : 0 < B) (hs : |s| ≤ B) :
    |deriv (scaledEntropyProfile B) s| ≤ 3 := by
  rw [scaledEntropyProfile_deriv hB]
  rw [← entropyProfile_deriv]
  apply entropyProfile_deriv_bound
  rw [abs_div,abs_of_pos hB]
  exact (div_le_one hB).mpr hs

theorem scaledEntropyProfile_curvature {B s : ℝ} (hB : 0 < B) (hs : |s| ≤ B) :
    1 ≤ scaledEntropyProfile B s*(-deriv (deriv (scaledEntropyProfile B)) s) := by
  have ha : |s/B| ≤ 1 := by
    rw [abs_div,abs_of_pos hB]
    exact (div_le_one hB).mpr hs
  have hc := entropyProfile_curvature ha
  rw [entropyProfile_second_deriv] at hc
  rw [scaledEntropyProfile_second_deriv hB]
  unfold scaledEntropyProfile
  convert hc using 1
  field_simp

theorem scaledEntropyProfile_tangent {B s u : ℝ} (hB : 0 < B) (hs : |s| ≤ B) (hu : |u| ≤ B) :
    scaledEntropyProfile B u ≤ scaledEntropyProfile B s+deriv (scaledEntropyProfile B) s*(u-s) := by
  have ha (z : ℝ) (hz : |z| ≤ B) : |z/B| ≤ 1 := by
    rw [abs_div,abs_of_pos hB]
    exact (div_le_one hB).mpr hz
  have ht := mul_le_mul_of_nonneg_left (entropyProfile_tangent (ha s hs) (ha u hu)) hB.le
  rw [entropyProfile_deriv] at ht
  rw [scaledEntropyProfile_deriv hB]
  unfold scaledEntropyProfile
  convert ht using 1
  field_simp

theorem scaledEntropyProfile_lipschitz {B s u : ℝ} (hB : 0 < B) (hs : |s| ≤ B) (hu : |u| ≤ B) :
    |scaledEntropyProfile B u-scaledEntropyProfile B s| ≤ 3*|u-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc (-B) B) => ((scaledEntropyProfile_contDiff B).differentiable (by simp)).differentiableAt)
    (fun x (hx : x ∈ Icc (-B) B) => by
      simpa only [Real.norm_eq_abs] using scaledEntropyProfile_deriv_bound hB (abs_le.mpr hx))
    (convex_Icc (-B) B) (abs_le.mp hs) (abs_le.mp hu)
  simpa only [Real.norm_eq_abs] using hh

end KLS.ConstantReduction
end
