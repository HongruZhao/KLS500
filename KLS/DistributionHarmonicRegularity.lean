import KLS.HarmonicDistributionSignedTests
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff ENNReal Topology
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

/-- The actual Euclidean Laplace operator in the verified local elliptic API. -/
def laplaceSmoothOpOn (U : Set (Space n)) : SmoothOpOn n U where
  a _ := (1 : Matrix (Fin n) (Fin n) ℝ)
  lam := 1
  lam_pos := zero_lt_one
  contDiffOn _ _ := contDiffOn_const
  elliptic := Eventually.of_forall fun x ξ => by simp [Matrix.one_apply, ite_mul, pow_two]
  b _ _ := 0
  c _ := 0
  b_smooth _ := contDiffOn_const
  c_smooth := contDiffOn_const

lemma localWeakSol_laplace_of_distribution {v : Space n → ℝ}
    (hv : MemLp v 2 volume) {U : Set (Space n)}
    {G : Fin n → Space n → ℝ} (hgrad : HasWeakGradOn U v G)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, v x * coordinateLaplacian ψ x) = 0) :
    LocalWeakSol U (laplaceSmoothOpOn U).a (laplaceSmoothOpOn U).b
      (laplaceSmoothOpOn U).c (fun _ => 0) v G := by
  intro ψ hψ hc hs
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hi (i : Fin n) : Integrable (fun x => v x * coordinateHessian ψ x i i) :=
    hv.integrable_mul (show MemLp (fun x => coordinateHessian ψ x i i) 2 volume from (contDiff_coordinateHessian hψ2 (m := 0) (by norm_num) i i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateHessian hc i i))
  have hdi (i : Fin n) : (∫ x in U, v x * coordinateHessian ψ x i i) =
      -(∫ x in U, G i x * partialD i ψ x) := by
    exact hgrad (coordinateDerivative ψ i)
      (contDiff_coordinateDerivative hψ (m := (⊤ : ℕ∞)) (by simp) i)
      (hasCompactSupport_coordinateDerivative hc i)
      ((tsupport_coordinateDerivative_subset ψ i).trans hs) i
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hdi i)
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => (hi i).restrict)] at hsum
  have hleft : (∫ x in U, ∑ i, v x * coordinateHessian ψ x i i) = 0 := by
    simp_rw [← Finset.mul_sum]
    change (∫ x in U, v x * coordinateLaplacian ψ x) = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx
        (hs (tsupport_coordinateLaplacian_subset ψ ht))), mul_zero])]
    exact hdist ψ hψ2 hc hs
  rw [hleft] at hsum
  have hdiag (i j : Fin n) :
      (∫ x in U, (1 : Matrix (Fin n) (Fin n) ℝ) i j * G i x * partialD j ψ x) =
      if i = j then (∫ x in U, G i x * partialD i ψ x) else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  change (∑ i, ∑ j, ∫ x in U, (1 : Matrix (Fin n) (Fin n) ℝ) i j * G i x * partialD j ψ x) +
    (∑ i, ∫ x in U, 0 * G i x * ψ x) + (∫ x in U, 0 * v x * ψ x) = ∫ x in U, 0 * ψ x
  simp only [hdiag, Finset.sum_ite_eq, Finset.mem_univ, ite_true, zero_mul, integral_zero,
    Finset.sum_const_zero, add_zero]
  exact neg_eq_zero.mp hsum.symm

/-- A continuous L2 distribution-harmonic function is actually smooth on
strictly smaller balls. Its Sobolev membership is concluded from mollification,
not required as a premise. -/
theorem contDiffOn_of_memLp_continuous_distribution_harmonic
    {v : Space n → ℝ} (hv : MemLp v 2 volume) {c : Space n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcont : ContinuousOn v (ball c R))
    (hdist : ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball c R → (∀ x, 0 ≤ φ x) →
      (∫ x, v x * coordinateLaplacian φ x) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) v (ball c r) := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  let χ : ContDiffBump c := ⟨r, s, hr, hrs⟩
  have hex (i : Fin n) : ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * v x) i g :=
    distribution_harmonic_cutoff_hasWeakDerivative hv (χ.contDiff : ContDiff ℝ 1 (χ : Space n → ℝ))
      χ.hasCompactSupport hsR (by rw [χ.tsupport_eq]) hdist i
  choose G hG using hex
  have hgrad : HasWeakGradOn (ball c r) v (fun i => G i) :=
    hasWeakGradOn_of_cutoff_eq_one hG (fun x hx => χ.one_of_mem_closedBall (ball_subset_closedBall hx))
  have hdist' : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c r → (∫ x, v x * coordinateLaplacian ψ x) = 0 := by
    intro ψ hψ hc hs
    exact integral_mul_laplacian_eq_zero_of_nonneg_tests hv isOpen_ball hdist hψ hc
      (hs.trans (ball_subset_ball hrR.le))
  have hsol := localWeakSol_laplace_of_distribution hv hgrad hdist'
  obtain ⟨v', hv', hae⟩ := exists_contDiffOn_of_localWeakSol isOpen_ball
    (laplaceSmoothOpOn (ball c r)) (f := fun _ => 0) contDiffOn_const
    (fun K _ _ => hv.restrict K) (fun i K _ _ => (Lp.memLp (G i)).restrict K) hgrad hsol
  have heq : EqOn v' v (ball c r) := Measure.eqOn_open_of_ae_eq hae isOpen_ball hv'.continuousOn
    (hcont.mono (ball_subset_ball hrR.le))
  exact hv'.congr heq.symm

end KLS
end
