import KLS.ResolventVarianceComparison

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The variance comparison uses two genuinely constructed resolvents,
of the actual squared gradient and of the actual squared forcing. -/
theorem weightedMassResolvent_exists_variance_pair
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {t : ℝ} (ht : 0 < t)
    {f g : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf2 : MemLp f 2 (potentialMeasure φ))
    (hF2 : MemLp (fun x => ‖gradient f x‖ ^ 2) 2 (potentialMeasure φ))
    (hG2 : MemLp (fun x => g x ^ 2) 2 (potentialMeasure φ))
    (heq : ∀ x, f x - t * weightedDiffusion φ f x = g x) :
    ∃ v w : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ ContDiff ℝ (⊤ : ℕ∞) w ∧
      MemLp v 2 (potentialMeasure φ) ∧ MemLp w 2 (potentialMeasure φ) ∧
      v =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht (hF2.toLp (fun x => ‖gradient f x‖ ^ 2)) : Space n → ℝ) ∧
      w =ᵐ[potentialMeasure φ]
        (weightedMassResolvent φ ht (hG2.toLp (fun x => g x ^ 2)) : Space n → ℝ) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=‖gradient f x‖ ^ 2) ∧
      (∀ x, w x-t*weightedDiffusion φ w x=g x ^ 2) ∧
      ∀ x, f x ^ 2+2*t*v x ≤ w x := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖gradient f x‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  obtain ⟨v,hv,hv2,hdv,_,hvμ,_,hev⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hF hF2
  obtain ⟨w,hw,hw2,hdw,_,hwμ,_,hew⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht (hg.pow 2) hG2
  have hgradf : MemLp (gradient f) 2 (potentialMeasure φ) :=
    (memLp_two_iff_integrable_sq_norm
      (continuous_gradient_of_contDiff (hf.of_le (by simp))).aestronglyMeasurable).mpr
      (hF2.integrable (by norm_num))
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgw := (memLp_gradient_of_coordinateDerivative (hw.of_le (by simp)) hdw).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact ⟨v,w,hv,hw,hv2,hw2,hvμ,hwμ,hev,hew,resolvent_variance_of_equations
    (hφ.of_le (by simp)) (hf.of_le (by simp)) (hv.of_le (by simp)) (hw.of_le (by simp))
    ht heq hev hew hf2 hgradf (hv2.integrable (by norm_num)) (hw2.integrable (by norm_num)) hgv hgw⟩

/-- Bounded smooth forcing with bounded actual gradient yields the concrete
resolvent variance bound by its supremum alone. The squared-gradient forcing
is proved to lie in the actual L2 resolvent domain. -/
theorem weightedMassResolvent_exists_bounded_variance_pair
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∃ f : Space n → ℝ,
      ∃ hF2 : MemLp (fun x => ‖gradient f x‖ ^ 2) 2 (potentialMeasure φ),
      ∃ v : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
        MemLp f 2 (potentialMeasure φ) ∧ MemLp v 2 (potentialMeasure φ) ∧
        f =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hg2.toLp g) : Space n → ℝ) ∧
        v =ᵐ[potentialMeasure φ]
          (weightedMassResolvent φ ht (hF2.toLp (fun x => ‖gradient f x‖ ^ 2)) : Space n → ℝ) ∧
        (∀ x, f x-t*weightedDiffusion φ f x=g x) ∧
        (∀ x, v x-t*weightedDiffusion φ v x=‖gradient f x‖ ^ 2) ∧
        ∀ x, f x ^ 2+2*t*v x ≤ B ^ 2 := by
  obtain ⟨f,hf,hf2,_,hfμ,_,heq,hfM⟩ :=
    weightedMassResolvent_exists_gradient_bounded_representative hφ hconv ht hg hg2 hM hgM
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖gradient f x‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by simp)
  have hF2 : MemLp (fun x => ‖gradient f x‖ ^ 2) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hF.continuous.aestronglyMeasurable (M ^ 2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 (hfM x)
  have hgSq (x : Space n) : g x ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (hgB x)
  have hG2 : MemLp (fun x => g x ^ 2) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound (hg.pow 2).continuous.aestronglyMeasurable (B ^ 2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hgSq x
  obtain ⟨v,w,hv,hw,hv2,_,hvμ,hwμ,hev,_,hvar⟩ :=
    weightedMassResolvent_exists_variance_pair hφ ht hf hg hf2 hF2 hG2 heq
  have hwB : ∀ x, w x ≤ B ^ 2 := by
    apply weightedMassResolvent_upper_bound_of_representative
      (hφ.of_le (by simp)) ht (hG2.toLp (fun x => g x ^ 2)) (hw.of_le (by simp)) hwμ
    filter_upwards [hG2.coeFn_toLp] with x hx
    rw [hx]
    exact hgSq x
  exact ⟨f,hF2,v,hf,hv,hf2,hv2,hfμ,hvμ,heq,hev,fun x => (hvar x).trans (hwB x)⟩

end KLS
end
