import KLS.LocalHarmonicWeakGradient
import EllipticPdes.Regularity.Local.Evans

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

lemma coordinateLaplacian_add {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    coordinateLaplacian (f + g) x = coordinateLaplacian f x + coordinateLaplacian g x := by
  simp only [coordinateLaplacian, coordinateHessian_add hf hg, Finset.sum_add_distrib]

/-- Testing against nonnegative compact functions already determines the full
harmonic distribution: a genuine smooth cutoff dominates each signed test. -/
theorem integral_mul_laplacian_eq_zero_of_nonneg_tests {v : Space n → ℝ}
    (hv : MemLp v 2 volume) {U : Set (Space n)} (hU : IsOpen U)
    (hdist : ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) → (∫ x, v x * coordinateLaplacian φ x) = 0)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) : (∫ x, v x * coordinateLaplacian ψ x) = 0 := by
  obtain ⟨ζ, hζ, hζ1, hζ01⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hc hU hs
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let b : Space n → ℝ := C • ζ
  have hb : ContDiff ℝ 2 b := (hζ.1.of_le (by simp)).const_smul C
  have hbc : HasCompactSupport b := hζ.2.1.smul_left
  have hbs : tsupport b ⊆ U := (tsupport_smul_subset_right (fun _ => C) ζ).trans hζ.2.2
  have hb0 : ∀ x, 0 ≤ b x := fun x => mul_nonneg hC0 (hζ01 x).1
  have hplus0 : ∀ x, 0 ≤ (b + ψ) x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hz := hζ1.self_of_nhdsSet x hx
      have hp : -C ≤ ψ x := by
        have ha : |ψ x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
        exact (abs_le.mp ha).1
      change 0 ≤ C * ζ x + ψ x
      rw [hz, mul_one]
      linarith
    · simpa only [Pi.add_apply, image_eq_zero_of_notMem_tsupport hx, add_zero] using hb0 x
  have hplusc : HasCompactSupport (b + ψ) := hbc.add hc
  have hpluss : tsupport (b + ψ) ⊆ U := (tsupport_add b ψ).trans (union_subset hbs hs)
  have hz := hdist b hb hbc hbs hb0
  have hzplus := hdist (b + ψ) (hb.add hψ) hplusc hpluss hplus0
  have hi {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
      Integrable (fun x => v x * coordinateLaplacian f x) :=
    hv.integrable_mul (show MemLp (coordinateLaplacian f) 2 volume from (continuous_coordinateLaplacian hf).memLp_of_hasCompactSupport
      (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordinateLaplacian_subset f)))
  simp_rw [coordinateLaplacian_add hb hψ, mul_add] at hzplus
  rw [integral_add (hi hb hbc) (hi hψ hc), hz, zero_add] at hzplus
  exact hzplus

end KLS
end
