import KLS.HessianConvexConverse

/-! The literal BKL suspension potential is convex when its Hessian
perturbation coefficient fits under the original positive curvature. -/

open Set Matrix
open scoped BigOperators ContDiff
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

def suspensionPotential (V f : E → ℝ) (β σ c : ℝ) (p : ℝ × (I → E)) : ℝ :=
  (∑ i, V (p.2 i)) + β * |σ * p.1 - c * ∑ i, f (p.2 i)|

lemma convexOn_sum_coordinates_add_linear {g : E → ℝ}
    (hg : ConvexOn ℝ univ g) (a : ℝ) :
    ConvexOn ℝ univ (fun p : ℝ × (I → E) => (∑ i, g (p.2 i)) + a * p.1) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ u v hu hv huv
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hg.2 (mem_univ (p.2 i)) (mem_univ (q.2 i)) hu hv huv)
  simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change (∑ i, g (u • p.2 i + v • q.2 i)) + a * (u * p.1 + v * q.1) ≤ _
  change _ ≤ u * ((∑ i, g (p.2 i)) + a * p.1) +
    v * ((∑ i, g (q.2 i)) + a * q.1)
  nlinarith

lemma add_mul_abs_eq_max (A B β : ℝ) (hβ : 0 ≤ β) :
    A + β * |B| = max (A + β * B) (A - β * B) := by
  by_cases hB : 0 ≤ B
  · rw [abs_of_nonneg hB, max_eq_left]
    nlinarith [mul_nonneg hβ hB]
  · have hB' : B ≤ 0 := le_of_not_ge hB
    rw [abs_of_nonpos hB', max_eq_right]
    · ring
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hB']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma suspensionPotential_eq_max (V f : E → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (σ c : ℝ) (p : ℝ × (I → E)) :
    suspensionPotential V f β σ c p =
      max ((∑ i, (V (p.2 i) + (-β * c) * f (p.2 i))) + β * σ * p.1)
          ((∑ i, (V (p.2 i) + (β * c) * f (p.2 i))) + (-β * σ) * p.1) := by
  unfold suspensionPotential
  rw [add_mul_abs_eq_max _ _ _ hβ]
  congr 1 <;> simp only [Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring

theorem convexOn_suspensionPotential {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) {κ M β σ c : ℝ}
    (hlower : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hbound : ∀ x v, |fderiv ℝ (fderiv ℝ f) x v v| ≤ M * ‖v‖ ^ 2)
    (hβ : 0 ≤ β) (hsmall : β * |c| * M ≤ κ) :
    ConvexOn ℝ univ (suspensionPotential (I := I) V f β σ c) := by
  have hplus : ConvexOn ℝ univ (fun x => V x + (β * c) * f x) :=
    convexOn_univ_add_small_hessian hV hf hlower hbound (by
      simpa only [abs_mul, abs_of_nonneg hβ] using hsmall)
  have hminus : ConvexOn ℝ univ (fun x => V x + (-β * c) * f x) :=
    convexOn_univ_add_small_hessian hV hf hlower hbound (by
      simpa only [abs_mul, abs_neg, abs_of_nonneg hβ] using hsmall)
  have h := (convexOn_sum_coordinates_add_linear (I := I) hminus (β * σ)).sup
    (convexOn_sum_coordinates_add_linear (I := I) hplus (-β * σ))
  have he : suspensionPotential (I := I) V f β σ c =
      (fun p => (∑ i, (V (p.2 i) + (-β * c) * f (p.2 i))) + β * σ * p.1) ⊔
      (fun p => (∑ i, (V (p.2 i) + (β * c) * f (p.2 i))) + (-β * σ) * p.1) := by
    funext p
    exact suspensionPotential_eq_max V f hβ σ c p
  rwa [he]

theorem convexOn_suspensionPotential_of_opNorm {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) {κ M β σ c : ℝ}
    (hlower : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hβ : 0 ≤ β) (hsmall : β * |c| * M ≤ κ) :
    ConvexOn ℝ univ (suspensionPotential (I := I) V f β σ c) :=
  convexOn_suspensionPotential hV hf hlower (secondFrechet_abs_le_of_opNorm hbound) hβ hsmall

/-- The number of independent copies can always make the genuine curvature
perturbation as small as required. -/
lemma exists_suspension_copy_count {κ β M : ℝ} (hκ : 0 < κ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ β * |(Real.sqrt N)⁻¹| * M ≤ κ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((β * M / κ) ^ 2 + 1)
  have hNr : 0 < (N : ℝ) := by nlinarith [sq_nonneg (β * M / κ)]
  have hNs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hq : 0 ≤ β * M / κ := div_nonneg (mul_nonneg hβ hM) hκ.le
  have hroot : β * M / κ ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hNr.le]
  have hprod := (div_le_iff₀ hκ).1 hroot
  refine ⟨N, by exact_mod_cast hNr, ?_⟩
  calc
    _ = (β * M) / Real.sqrt N := by
      rw [abs_of_pos (inv_pos.2 hNs)]
      ring
    _ ≤ κ := (div_le_iff₀ hNs).2 (by nlinarith)

/-- The actual uniformly convex coordinate potential admits a convex suspension
with the paper's coefficient `1 / sqrt N`, for every positive noise rate. -/
theorem exists_convex_suspensionPotential {n : ℕ} {V f : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) {κ M β : ℝ}
    (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hβ : 0 ≤ β) :
    ∃ N : ℕ, 0 < N ∧ ∀ σ : ℝ,
      ConvexOn ℝ univ (suspensionPotential (I := Fin N) V f β σ (Real.sqrt N)⁻¹) := by
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hbound 0)
  obtain ⟨N, hN, hsmall⟩ := exists_suspension_copy_count hκ hβ hM
  exact ⟨N, hN, fun σ => convexOn_suspensionPotential_of_opNorm hV hf
    (secondFrechet_lower_of_coordinateHessian hV hlower) hbound hβ hsmall⟩

end KLS
end
#print axioms KLS.convexOn_suspensionPotential
#print axioms KLS.convexOn_suspensionPotential_of_opNorm

#print axioms KLS.exists_suspension_copy_count
#print axioms KLS.exists_convex_suspensionPotential
