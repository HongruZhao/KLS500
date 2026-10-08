import KLS.WeightedTaylorFirstMoment

/-! A direct L2 contraction from the actual directional second-moment bound. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def firstMixedMomentVector (μ : Measure (Space n)) (f : Space n → ℝ) : Space n :=
  WithLp.toLp 2 (fun j => ∫ x, f x * x j ∂μ)

theorem firstMixedMomentVector_norm_sq_le_one {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hcoord : ∀ j : Fin n, MemLp (fun x : Space n => x j) 2 μ)
    (hunit : ∫ x, f x ^ 2 ∂μ = 1)
    (hsecond : ∀ v : Space n, (∫ x, inner ℝ v x ^ 2 ∂μ) ≤ ‖v‖ ^ 2) :
    ‖firstMixedMomentVector μ f‖ ^ 2 ≤ 1 := by
  let M := firstMixedMomentVector μ f
  let g : Space n → ℝ := fun x => inner ℝ M x
  have hg : MemLp g 2 μ := by
    convert memLp_finsetSum Finset.univ (fun j _ => (hcoord j).const_mul (M j)) using 1
    funext x
    simpa only [g, mul_comm] using inner_eq_coordinate_sum M x
  have hcross : (∫ x, f x * g x ∂μ) = ‖M‖ ^ 2 := by
    dsimp only [g]
    simp_rw [inner_eq_coordinate_sum, Finset.mul_sum]
    have hi (j : Fin n) : Integrable (fun x => f x * (x j * M j)) μ := by
      convert (hf.integrable_mul (hcoord j)).const_mul (M j) using 1
      funext x
      simp only [Pi.mul_apply]
      ring
    rw [integral_finsetSum Finset.univ (fun j _ => hi j), EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∫ x, f x * (x j * M j) ∂μ) = M j * (∫ x, f x * x j ∂μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun x => by ring
      _ = M j ^ 2 := by change (M j) * (M j) = _; ring
  have hi : (∫ x, (f x - g x) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - 2 * (∫ x, f x * g x ∂μ) + (∫ x, g x ^ 2 ∂μ) := by
    have he : (fun x => (f x - g x) ^ 2) = fun x =>
        (f x ^ 2 - 2 * (f x * g x)) + g x ^ 2 := by funext x; ring
    have hadd := integral_add (hf.integrable_sq.sub ((hf.integrable_mul hg).const_mul 2)) hg.integrable_sq
    have hsub := integral_sub hf.integrable_sq ((hf.integrable_mul hg).const_mul 2)
    simp only [Pi.sub_apply, Pi.mul_apply] at hadd hsub
    rw [he, hadd, hsub, integral_const_mul]
  have hp : 0 ≤ ∫ x, (f x - g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [hi, hunit, hcross] at hp
  have hb : (∫ x, g x ^ 2 ∂μ) ≤ ‖M‖ ^ 2 := hsecond M
  change ‖M‖ ^ 2 ≤ 1
  linarith

end KLS
end
#print axioms KLS.firstMixedMomentVector_norm_sq_le_one
