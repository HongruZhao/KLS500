import KLS.WeightedPerturbativeC2Regularity

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS

/-- The geometric interpolation exponent is strictly positive. -/
lemma geometric_holder_exponent {s θ : ℝ} (hs : 0 < s) (hsone : s < 1)
    (hθ : 0 < θ) (hθone : θ < 1) (hsθ : s ≤ θ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ s ^ γ = θ := by
  have hls : Real.log s < 0 := Real.log_neg hs hsone
  have hlθ : Real.log θ < 0 := Real.log_neg hθ hθone
  refine ⟨Real.log θ / Real.log s, div_pos_of_neg_of_neg hlθ hls, ?_, ?_⟩
  · rw [div_le_iff_of_neg hls]
    simpa only [one_mul] using Real.log_le_log hs hsθ
  · rw [Real.rpow_def_of_pos hs]
    rw [mul_div_cancel₀ _ hls.ne]
    exact Real.exp_log hθ

/-- A modulus controlled at every geometric distance scale is Holder.
The proof chooses an actual scale for each nonzero distance. -/
theorem holder_bound_of_geometric_modulus {X : Type*} [PseudoMetricSpace X]
    {F : X → ℝ} {S : Set X} {K s θ γ : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hsone : s < 1) (hθ : 0 < θ)
    (hγ : 0 < γ) (hscale : s ^ γ = θ)
    (hb : ∀ j : ℕ, ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ s ^ j →
      |F x - F y| ≤ K * θ ^ j)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) (hxy : 0 < dist x y)
    (hxyone : dist x y ≤ 1) :
    |F x - F y| ≤ (K / θ) * dist x y ^ γ := by
  obtain ⟨j, hjlow, hjhigh⟩ := exists_nat_pow_near_of_lt_one hxy hxyone hs hsone
  have hp : θ ^ (j + 1) ≤ dist x y ^ γ := by
    calc
      θ ^ (j + 1) = (s ^ (j + 1)) ^ γ := by
        rw [← Real.rpow_natCast_mul hs.le, mul_comm, Real.rpow_mul_natCast hs.le, hscale]
      _ ≤ dist x y ^ γ := Real.rpow_le_rpow (pow_nonneg hs.le _) hjlow.le hγ.le
  calc
    |F x - F y| ≤ K * θ ^ j := hb j x hx y hy hjhigh
    _ = (K / θ) * θ ^ (j + 1) := by rw [pow_succ]; field_simp
    _ ≤ (K / θ) * dist x y ^ γ := mul_le_mul_of_nonneg_left hp (div_nonneg hK hθ.le)

end KLS
end
