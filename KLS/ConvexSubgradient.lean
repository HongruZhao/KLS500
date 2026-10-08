import KLS.MomentMapFiniteDifference
import Mathlib.Analysis.LocallyConvex.Separation

/-! Actual Euclidean support-plane subgradients. These form the set-valued
foundation needed before a weak gradient transport can be interpreted as an
Alexandrov Monge--Ampere equation. No differentiability or regularity theorem
is assumed in the existence or compact-image results. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff NNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def convexSubgradient (φ : Space n → ℝ) (x : Space n) : Set (Space n) :=
  {p | ∀ y, φ x + inner ℝ p (y - x) ≤ φ y}

def convexSubgradientImage (φ : Space n → ℝ) (S : Set (Space n)) : Set (Space n) :=
  {p | ∃ x ∈ S, p ∈ convexSubgradient φ x}

theorem convexSubgradient_nonempty {φ : Space n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) (x : Space n) :
    (convexSubgradient φ x).Nonempty := by
  let E : Set (Space n × ℝ) := {z | φ z.1 < z.2}
  have hEc : Convex ℝ E := by
    simpa only [mem_univ, true_and] using hc.convex_strict_epigraph
  have hEo : IsOpen E := isOpen_lt (hφ.comp continuous_fst) continuous_snd
  obtain ⟨F, hF⟩ := geometric_hahn_banach_point_open hEc hEo
    (show (x, φ x) ∉ E by dsimp [E]; exact lt_irrefl _)
  let l : Space n →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)
  let r : ℝ := F (0, 1)
  have hsplit (y : Space n) (t : ℝ) : F (y, t) = l y + r * t := by
    have he : (y, t) = (y, 0) + t • (0, (1 : ℝ)) := by ext <;> simp
    rw [he, map_add, map_smul]
    change l y + t * r = l y + r * t
    ring
  have hr : 0 < r := by
    have hh := hF (x, φ x + 1) (by dsimp [E]; linarith)
    rw [hsplit, hsplit] at hh
    nlinarith
  have hbound (y : Space n) : l x + r * φ x ≤ l y + r * φ y := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hF (y, φ y + ε / r) (by dsimp [E]; linarith [div_pos hε hr])
    rw [hsplit, hsplit, mul_add, mul_div_cancel₀ _ hr.ne'] at hh
    simpa only [add_assoc] using hh.le
  let p := (InnerProductSpace.toDual ℝ (Space n)).symm ((-r⁻¹) • l)
  refine ⟨p, fun y => ?_⟩
  have hip : inner ℝ p (y - x) = -r⁻¹ * (l y - l x) := by
    rw [show inner ℝ p (y - x) = ((-r⁻¹) • l) (y - x) from
      InnerProductSpace.toDual_symm_apply]
    simp
  rw [hip]
  apply (mul_le_mul_iff_right₀ hr).mp
  have hcancel : r * (φ x + -r⁻¹ * (l y - l x)) = r * φ x - (l y - l x) := by
    field_simp
    ring
  rw [hcancel]
  linarith [hbound y]

theorem gradient_mem_convexSubgradient {φ : Space n → ℝ}
    (hc : ConvexOn ℝ univ φ) {x : Space n} (hφ : DifferentiableAt ℝ φ x) :
    gradient φ x ∈ convexSubgradient φ x := by
  intro y
  have hd : HasDerivAt (fun t : ℝ => φ (x + t • (y - x)))
      (fderiv ℝ φ x (y - x)) 0 := by
    have hf : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • (y - x)) := by
      simpa only [zero_smul, add_zero] using hφ.hasFDerivAt
    exact hf.comp_hasDerivAt 0 (hasDerivAt_affine_line x (y - x) 0)
  have hh := (convexOn_affine_line hc x (y - x)).le_slope_of_hasDerivAt
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) hd
  simp only [slope_def_field, zero_smul, add_zero, one_smul, add_sub_cancel,
    sub_zero, div_one] at hh
  rw [inner_gradient_left]
  linarith

theorem eq_gradient_of_mem_convexSubgradient {φ : Space n → ℝ}
    {x p : Space n} (hφ : DifferentiableAt ℝ φ x)
    (hp : p ∈ convexSubgradient φ x) : p = gradient φ x := by
  have hm : IsLocalMin (fun y => φ y - inner ℝ p y) x := by
    apply Filter.Eventually.of_forall
    intro y
    have hh := hp y
    simp only [inner_sub_right] at hh
    linarith
  have hd : HasFDerivAt (fun y => φ y - inner ℝ p y)
      (fderiv ℝ φ x - innerSL ℝ p) x :=
    hφ.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
  have hz := hm.hasFDerivAt_eq_zero hd
  apply ext_inner_right ℝ
  intro y
  have hh := congrArg (fun F : Space n →L[ℝ] ℝ => F y) hz
  change fderiv ℝ φ x y - inner ℝ p y = 0 at hh
  rw [inner_gradient_left]
  linarith

theorem convexSubgradient_eq_singleton_of_differentiableAt {φ : Space n → ℝ}
    (hc : ConvexOn ℝ univ φ) {x : Space n} (hφ : DifferentiableAt ℝ φ x) :
    convexSubgradient φ x = {gradient φ x} := by
  ext p
  constructor
  · exact fun hp => eq_gradient_of_mem_convexSubgradient hφ hp
  · rintro rfl
    exact gradient_mem_convexSubgradient hc hφ

theorem norm_le_of_mem_convexSubgradient {φ : Space n → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {x p : Space n} (hp : p ∈ convexSubgradient φ x) :
    ‖p‖ ≤ L := by
  have hs := hp (x + p)
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  have hh := hφ.dist_le_mul (x + p) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hh
  have hu := (le_abs_self (φ (x + p) - φ x)).trans hh
  nlinarith [norm_nonneg p, L.property]

theorem isClosed_convexSubgradient_graph {φ : Space n → ℝ} (hφ : Continuous φ) :
    IsClosed {z : Space n × Space n | z.2 ∈ convexSubgradient φ z.1} := by
  change IsClosed {z : Space n × Space n | ∀ y, φ z.1 + inner ℝ z.2 (y - z.1) ≤ φ y}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro y
  exact isClosed_le ((hφ.comp continuous_fst).add
    (continuous_snd.inner (continuous_const.sub continuous_fst))) continuous_const

theorem isCompact_convexSubgradientImage {φ : Space n → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {S : Set (Space n)} (hS : IsCompact S) :
    IsCompact (convexSubgradientImage φ S) := by
  let G : Set (Space n × Space n) :=
    (S ×ˢ Metric.closedBall 0 (L : ℝ)) ∩ {z | z.2 ∈ convexSubgradient φ z.1}
  have hG : IsCompact G :=
    (hS.prod (isCompact_closedBall _ _)).inter_right
      (isClosed_convexSubgradient_graph hφ.continuous)
  have heq : Prod.snd '' G = convexSubgradientImage φ S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hq, rfl⟩
      exact ⟨x, hq.1.1, hq.2⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨(x, p), ⟨⟨hx, by simpa using norm_le_of_mem_convexSubgradient hφ hp⟩, hp⟩, rfl⟩
  rw [← heq]
  exact hG.image continuous_snd

theorem convexSubgradient_monotone {φ : Space n → ℝ} {x y p q : Space n}
    (hp : p ∈ convexSubgradient φ x) (hq : q ∈ convexSubgradient φ y) :
    0 ≤ inner ℝ (p - q) (x - y) := by
  have hh := hp y
  have hk := hq x
  simp only [inner_sub_left, inner_sub_right] at hh hk ⊢
  linarith

end KLS
end

#print axioms KLS.convexSubgradient_nonempty
#print axioms KLS.convexSubgradient_eq_singleton_of_differentiableAt
#print axioms KLS.isCompact_convexSubgradientImage
