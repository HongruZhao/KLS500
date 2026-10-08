import KLS.SuspensionMixedCumulants
import KLS.SuspensionTensorRestriction
import KLS.WeightedTiltTaylorTensor

/-! The pure-block estimate for genuine suspension cumulants, and its
conditional consequence for normalized smooth affine-orthogonal signals.
The universal directional cumulant estimate remains an explicit premise. -/

open MeasureTheory Matrix
open scoped ENNReal ContDiff BigOperators
noncomputable section
namespace KLS

/-- Squared Hilbert--Schmidt norm of the actual cumulant with its last
argument fixed. -/
def directionalCumulantSquare {n : ℕ} (μ : Measure (Space n)) (d : ℕ) (u : Space n) : ℝ :=
  ∑ a : Fin d → Fin n, cumulantTensor μ (d + 1)
    (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u) ^ 2

/-- The remaining universal analytic premise, on the original isotropic
log-concave class in every dimension and with actual cumulant derivatives. -/
def UniversalDirectionalCumulantBound (d : ℕ) (b : ℝ) : Prop :=
  ∀ n : ℕ, ∀ μ : Measure (Space n), IsKLSMeasure μ → ∀ u : Space n,
    directionalCumulantSquare μ d u ≤ b * ‖u‖ ^ 2

theorem suspension_Taylor_sum_le_directionalCumulant {n N d : ℕ}
    {V f : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hμ : NormExponentialDomain (potentialMeasure V) (fun _ => 1))
    (hf : Measurable f) {A B : ℝ} (hbound : ∀ x, |f x| ≤ A + B * ‖x‖)
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0) {β σ : ℝ}
    (hβ : 0 < β) (hσ : σ ≠ 0) (hN : 0 < N) (hd : 0 < d) :
    ((d.factorial : ℝ) ^ 2 / σ ^ 2) *
      (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      directionalCumulantSquare (euclideanSuspensionLaw (N := N) (potentialMeasure V)
        f β σ (Real.sqrt N)⁻¹) d (suspensionNoiseDirection n N) := by
  let ν := euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹
  let T : (Fin d → SuspensionIndex n N) → ℝ := fun a => cumulantTensor ν (d + 1)
    (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin (suspensionDimension n N)) ℝ
      (Fintype.equivFin (SuspensionIndex n N) (a j))) (suspensionNoiseDirection n N))
  have hentry (i : Fin N) (a : Fin d → Fin n) :
      T (pureSuspensionBlock (i, a)) = ((d.factorial : ℝ) / (σ * Real.sqrt N)) *
        exponentialTiltCoordinateTaylor V f d a := by
    have hi := cumulantTensor_suspension_Taylor hμ hf hbound hmean hβ σ i
      (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j))
    simp_rw [suspensionBlockEmbedding_basisFun] at hi
    simpa only [T, ν, pureSuspensionBlock,
      exponentialTiltCoordinateTaylor, EuclideanSpace.basisFun_apply] using hi
  have hh := suspensionTensor_norm_bound hN hd T (exponentialTiltCoordinateTaylor V f d) hσ hentry
  have he : (∑ a, T a ^ 2) = directionalCumulantSquare ν d (suspensionNoiseDirection n N) := by
    unfold directionalCumulantSquare
    rw [← (Equiv.piCongrRight (fun _ : Fin d => Fintype.equivFin (SuspensionIndex n N))).sum_comp]
    rfl
  rwa [he] at hh

/-- The normalized smooth part of the suspension argument. The actual copy
count is constructed for each Laplace rate, then that rate tends to infinity. -/
theorem Taylor_sum_le_of_universalCumulant_normalized {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hfC : ContDiff ℝ 2 f)
    (hf : MemLp f 2 (potentialMeasure V))
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    (hfsq : (∫ x, (f x) ^ 2 ∂potentialMeasure V) = 1)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂potentialMeasure V) = 0)
    {κ M A B b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hHess : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hgrowth : ∀ x, |f x| ≤ A + B * ‖x‖) (hd : 0 < d) (hb : 0 ≤ b)
    (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      b / (d.factorial : ℝ) ^ 2 := by
  have hfac : 0 < (d.factorial : ℝ) ^ 2 := by positivity
  have hExp : NormExponentialDomain (potentialMeasure V) (fun _ => 1) :=
    normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (memLp_const (1 : ℝ))
  apply le_of_all_laplace_variance_factors (div_nonneg hb hfac.le)
  intro β hβ
  obtain ⟨N, hN, hν⟩ := exists_isKLSMeasure_euclideanSuspensionLaw hV hfC hμ hf
    hmean hfsq hforth hκ hlower hHess hβ
  let σ := suspensionNormalization β
  have hσ : 0 < σ := suspensionNormalization_pos β
  have hnorm : ‖suspensionNoiseDirection n N‖ = 1 := by simp [suspensionNoiseDirection]
  have hbound := hglobal (suspensionDimension n N) _ hν (suspensionNoiseDirection n N)
  rw [hnorm, one_pow, mul_one] at hbound
  have hlow := suspension_Taylor_sum_le_directionalCumulant hExp hfC.continuous.measurable
    hgrowth hmean hβ hσ.ne' hN hd
  have hh := hlow.trans hbound
  have hh' : (d.factorial : ℝ) ^ 2 *
      (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤ b * σ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hσ)).mp (by simpa only [div_mul_eq_mul_div] using hh)
  have hh'' : (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      σ ^ 2 * (b / (d.factorial : ℝ) ^ 2) := by
    have ht : (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
        b * σ ^ 2 / (d.factorial : ℝ) ^ 2 :=
      (le_div_iff₀ hfac).mpr (by simpa only [mul_comm] using hh')
    convert ht using 1
    ring
  have he : σ ^ 2 = 1 + 2 / β ^ 2 := Real.sq_sqrt (by positivity)
  simpa only [he] using hh''

end KLS
end
#print axioms KLS.suspension_Taylor_sum_le_directionalCumulant
#print axioms KLS.Taylor_sum_le_of_universalCumulant_normalized
