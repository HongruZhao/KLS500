import KLS.LocalHarmonicGradientBounds
import KLS.WeightedLocalSobolev
import EllipticPdes.Embedding.WeakGradient

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding
variable {n : ℕ}

/-- The actual compact localization of a distribution-harmonic L2 function
has an L2 weak derivative, obtained from its concrete mollifications. -/
theorem distribution_harmonic_cutoff_hasWeakDerivative {v χ : Space n → ℝ}
    (hv : MemLp v 2 volume) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    {c : Space n} {r R : ℝ} (hrR : r < R) (hχs : tsupport χ ⊆ closedBall c r)
    (hdist : ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball c R → (∀ x, 0 ≤ φ x) →
      (∫ x, v x * coordinateLaplacian φ x) = 0) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * v x) i g := by
  have hloc := hv.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he := eventually_laplacian_mollify_eq_zero_on_closedBall hloc hrR hdist
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have heq : ∀ k x, x ∈ tsupport χ → coordinateLaplacian (mollify (k + N) v) x = 0 :=
    fun k x hx => hN (k + N) (Nat.le_add_left N k) x (hχs hx)
  obtain ⟨M, hM, hb⟩ := exists_uniform_derivative_sq_compact_mul_shifted_harmonic_mollify hχ hc hv N heq
  have hU : MemLp (fun x => χ x * v x) 2 volume :=
    (hχ.continuous.memLp_top_of_hasCompactSupport hc volume).mul hv
  have hconv := (eLpNorm_compact_mul_mollify_sub_tendsto_zero hχ.continuous hc
    (fun K _ => hv.restrict K)).comp (tendsto_add_atTop_nat N)
  obtain ⟨g, -, hg⟩ := exists_weak_coordinateDerivative_of_approximation
    (f := fun k x => χ x * mollify (k + N) v x)
    (fun k => hχ.mul ((mollify_contDiff hloc _).of_le (by simp)))
    (fun _ => hc.mul_right) hU hconv i hM (fun k => hb k i)
  exact ⟨g, hg⟩

/-- Weak derivatives of a cutoff product are the local weak gradient where
the actual cutoff equals one. -/
theorem hasWeakGradOn_of_cutoff_eq_one {v χ : Space n → ℝ} {U : Set (Space n)}
    {g : Fin n → Lp ℝ 2 (volume : Measure (Space n))}
    (hg : ∀ i, HasWeakCoordinateDerivative (fun x => χ x * v x) i (g i))
    (hχ : ∀ x ∈ U, χ x = 1) :
    HasWeakGradOn U v (fun i => g i) := by
  intro ψ hψ hc hs i
  have hψ0 : ∀ x ∉ U, ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hdψ0 : ∀ x ∉ U, coordinateDerivative ψ i x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hs (tsupport_coordinateDerivative_subset ψ i ht)))
  have he := hg i ψ (hψ.of_le (by simp)) hc
  have hp : (∫ x, χ x * v x * coordinateDerivative ψ i x) =
      ∫ x, v x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ U
      · rw [hχ x hx, one_mul]
      · rw [hdψ0 x hx, mul_zero, mul_zero]
  rw [hp] at he
  change (∫ x in U, v x * coordinateDerivative ψ i x) = -(∫ x in U, g i x * ψ x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hdψ0 x hx, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hψ0 x hx, mul_zero])]
  exact he

end KLS
end
