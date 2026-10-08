import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

noncomputable section
open scoped RealInnerProductSpace
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma trilinear_apply_smul (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (a b c : ℝ) (x y z : E) :
    T (a • x) (b • y) (c • z) = a * b * c * T x y z := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

lemma cubic_unit_bound_scale_first (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {M : ℝ}
    (h : ∀ x z : E, ‖x‖ = 1 → ‖z‖ = 1 → |T x x z| ≤ M)
    (x z : E) (hz : ‖z‖ = 1) : |T x x z| ≤ M * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    simp [norm_smul, hn]
  have hb := h ((‖x‖⁻¹ : ℝ) • x) z hu hz
  have he : T ((‖x‖⁻¹ : ℝ) • x) ((‖x‖⁻¹ : ℝ) • x) z =
      ‖x‖⁻¹ ^ 2 * T x x z := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)] at hb
  have hp : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero hn
  have hi : (‖x‖⁻¹)^2 * ‖x‖^2 = 1 := by field_simp
  calc
    |T x x z| = (‖x‖⁻¹ ^ 2 * ‖x‖^2) * |T x x z| := by rw [hi, one_mul]
    _ = (‖x‖⁻¹ ^ 2 * |T x x z|) * ‖x‖^2 := by ring
    _ ≤ M * ‖x‖^2 := mul_le_mul_of_nonneg_right hb (le_of_lt hp)

lemma exists_cubic_diagonal_max [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    (a : E) (ha : ‖a‖ = 1) :
    ∃ x : E, ‖x‖ = 1 ∧ ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 →
      T u u v ≤ T x x x := by
  let K : Set (E × E) := Metric.sphere 0 1 ×ˢ Metric.sphere 0 1
  let f : E × E → ℝ := fun p => T p.1 p.1 p.2
  let g : E × E → ℝ := fun p => ‖(2 : ℝ) • p.1 + p.2‖ ^ 2
  have hK : IsCompact K := (isCompact_sphere (0 : E) 1).prod (isCompact_sphere 0 1)
  have hmem : ∀ u v : E, (u,v) ∈ K ↔ ‖u‖=1 ∧ ‖v‖=1 := by
    intro u v; simp [K]
  have hf : Continuous f := ((T.continuous.comp continuous_fst).clm_apply continuous_fst).clm_apply continuous_snd
  have hg : Continuous g := by dsimp [g]; fun_prop
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨(a,a), (hmem a a).mpr ⟨ha,ha⟩⟩ hf.continuousOn
  let S : Set (E × E) := K ∩ {q | f q = f p}
  have hS : IsCompact S := hK.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨q, hq, hsecond⟩ := hS.exists_isMaxOn ⟨p,hp,rfl⟩ hg.continuousOn
  obtain ⟨x,z⟩ := q
  have hx : ‖x‖=1 := ((hmem x z).mp hq.1).1
  have hz : ‖z‖=1 := ((hmem x z).mp hq.1).2
  let M := T x x z
  have hMmax : ∀ u v : E, ‖u‖=1 → ‖v‖=1 → T u u v ≤ M := by
    intro u v hu hv
    have h := hmax ((hmem u v).mpr ⟨hu,hv⟩)
    change f (u,v) ≤ f p at h
    rw [← hq.2] at h
    exact h
  have habs : ∀ u v : E, ‖u‖=1 → ‖v‖=1 → |T u u v| ≤ M := by
    intro u v hu hv
    apply abs_le.mpr
    refine ⟨?_, hMmax u v hu hv⟩
    have h := hMmax u (-v) hu (by simpa using hv)
    simpa only [map_neg, neg_le] using h
  have hscaled := cubic_unit_bound_scale_first T habs
  have hdiag : x=z := by
    by_contra hne
    by_cases hadd : x+z=0
    · have hez : z = -x := eq_neg_of_add_eq_zero_right hadd
      have hval : T (-x) (-x) (-x) = M := by
        dsimp [M]; rw [hez]; simp
      have hs : (-x,-x) ∈ S := by
        refine ⟨(hmem _ _).mpr ⟨by simpa using hx, by simpa using hx⟩, ?_⟩
        change T (-x) (-x) (-x) = f p
        exact hval.trans hq.2
      have h := hsecond hs
      change ‖(2 : ℝ) • (-x) + (-x)‖^2 ≤ ‖(2 : ℝ) • x+z‖^2 at h
      have he1 : (2 : ℝ) • (-x)+(-x) = (-3 : ℝ) • x := by module
      have he2 : (2 : ℝ) • x+z=x := by rw [hez]; module
      rw [he1,he2,norm_smul,hx] at h
      norm_num at h
    · let c : ℝ := ‖x+z‖
      have hc : 0<c := norm_pos_iff.mpr hadd
      have hc2 : c<2 := by
        have hsub : 0 < ‖x-z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
        have hsum := norm_add_sq_real x z
        have hdiff := norm_sub_sq_real x z
        rw [hx,hz] at hsum hdiff
        change c^2 = _ at hsum
        nlinarith
      let u : E := c⁻¹ • (x+z)
      have hu : ‖u‖=1 := by
        change ‖c⁻¹ • (x+z)‖=1
        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hc]
        exact inv_mul_cancel₀ (ne_of_gt hc)
      have hcxz : c • u = x+z := by
        dsimp [u]; rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
      have hpx := hscaled (x+z) x hx
      have hmx := hscaled (x-z) x hx
      have hpol : T (x+z) (x+z) x - T (x-z) (x-z) x = 4*M := by
        simp only [map_add, map_sub, add_apply, sub_apply]
        rw [h12 z x x, h23 x z x]
        dsimp [M]
        ring
      have hpar : ‖x+z‖^2 + ‖x-z‖^2 = 4 := by
        rw [norm_add_sq_real,norm_sub_sq_real,hx,hz]; ring
      have hpval : T (x+z) (x+z) x = M*c^2 := by
        have hpl := (abs_le.mp hpx).2
        have hml := (abs_le.mp hmx).1
        have hmpar := congrArg (fun t : ℝ => M*t) hpar
        dsimp [c]
        nlinarith only [hpl,hml,hpol,hmpar]
      have huval : T u u x = M := by
        have he : T (x+z) (x+z) x = c^2 * T u u x := by
          rw [← hcxz]
          simp only [map_smul,smul_apply,smul_eq_mul]
          ring
        rw [he] at hpval
        nlinarith [sq_pos_of_pos hc]
      have hs : (u,x) ∈ S := by
        refine ⟨(hmem _ _).mpr ⟨hu,hx⟩, ?_⟩
        change T u u x = f p
        exact huval.trans hq.2
      have h := hsecond hs
      change ‖(2 : ℝ) • u+x‖^2 ≤ ‖(2 : ℝ) • x+z‖^2 at h
      have hold : (2 : ℝ) • x+z = c • u+x := by rw [hcxz]; module
      rw [hold,norm_add_sq_real,norm_add_sq_real] at h
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos (by norm_num : (0:ℝ)<2),
        hu,hx,real_inner_smul_left] at h
      have hi := (abs_le.mp (abs_real_inner_le_norm u x)).1
      rw [hu,hx] at hi
      have hpos : 0 < (2-c)*(2+c+2*(inner ℝ u x)) := mul_pos (by linarith) (by linarith)
      nlinarith
  subst z
  exact ⟨x,hx,hMmax⟩

/-- Banach's diagonal norm principle for a symmetric real cubic tensor,
restricted to the repeated-slot form needed for the covariance-noise bound. -/
theorem symmetric_cubic_mixed_bound [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    {C : ℝ} (hdiag : ∀ x : E, |T x x x| ≤ C * ‖x‖^3)
    (x z : E) : |T x x z| ≤ C * ‖x‖^2 * ‖z‖ := by
  by_cases hx : x=0
  · subst x; simp
  by_cases hz : z=0
  · subst z; simp
  have hnx : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have hnz : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have ha : ‖(‖x‖⁻¹ : ℝ) • x‖=1 := by simp [norm_smul,hnx]
  obtain ⟨a,ha,hmax⟩ := exists_cubic_diagonal_max T h12 h23 _ ha
  have had := hdiag a
  rw [ha] at had
  have hunit : ∀ u v : E, ‖u‖=1 → ‖v‖=1 → |T u u v|≤C := by
    intro u v hu hv
    have hupper := (hmax u v hu hv).trans (le_abs_self _)
    have hlower := (hmax u (-v) hu (by simpa using hv)).trans (le_abs_self _)
    simp only [map_neg] at hlower
    apply abs_le.mpr
    constructor <;> nlinarith [had]
  have huz : ‖(‖z‖⁻¹ : ℝ) • z‖=1 := by simp [norm_smul,hnz]
  have hb := cubic_unit_bound_scale_first T hunit x _ huz
  rw [map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))] at hb
  calc
    |T x x z| = (‖z‖⁻¹ * ‖z‖) * |T x x z| := by rw [inv_mul_cancel₀ hnz,one_mul]
    _ = (‖z‖⁻¹ * |T x x z|) * ‖z‖ := by ring
    _ ≤ (C * ‖x‖^2) * ‖z‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg z)

end KLS.ConstantReduction
end
