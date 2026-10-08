import KLS.LogConcavityMoments

/-! Uniform dimension-dependent tails for the actual compact-set log-concave
class. Isotropy supplies a fixed second-moment radius, and actual log-concavity
then supplies a fixed geometric ratio. No universal Poincare bound is used. -/
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A convenient fixed radius, chosen to avoid any dimension-zero exception. -/
def isotropicTailRadius (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1)

theorem isotropicTailRadius_pos (n : ℕ) : 0 < isotropicTailRadius n := by
  unfold isotropicTailRadius
  positivity

/-- Markov applied to the genuine isotropic norm second moment. -/
theorem IsIsotropic.norm_tail_fixed_radius_le {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hiso : IsIsotropic μ) :
    μ.real {x | isotropicTailRadius n < ‖x‖} ≤ 1 / 4 := by
  let R := isotropicTailRadius n
  have hR : 0 < R := isotropicTailRadius_pos n
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x : Space n => sq_nonneg ‖x‖)
    hiso.integrable_norm_sq (R ^ 2)
  rw [hiso.integral_norm_sq] at hmark
  have hsub : μ.real {x | R < ‖x‖} ≤ μ.real {x | R ^ 2 ≤ ‖x‖ ^ 2} := by
    exact measureReal_mono (fun x hx => pow_le_pow_left₀ hR.le hx.le 2)
  calc
    μ.real {x | R < ‖x‖} ≤ (n : ℝ) / R ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hsub (sq_nonneg R)).trans hmark
    _ ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
      dsimp [R, isotropicTailRadius]
      nlinarith [sq_nonneg (n : ℝ)]

/-- Every shell has the same certified geometric ratio 1/3 throughout the
entire isotropic log-concave class in a fixed dimension. -/
theorem measureLogConcave.isotropic_norm_tail_le {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) (hiso : IsIsotropic μ) (k : ℕ) :
    μ.real {x | (2 * (k : ℝ) + 1) * isotropicTailRadius n < ‖x‖} ≤
      (1 / 4 : ℝ) * (1 / 3 : ℝ) ^ k := by
  let R := isotropicTailRadius n
  let p := μ.real (closedBall (0 : Space n) R)
  let a := μ.real {x | R < ‖x‖}
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha : a ≤ 1 / 4 := hiso.norm_tail_fixed_radius_le
  have hap : a = 1 - p := by
    have hcomp : {x : Space n | R < ‖x‖} = (closedBall 0 R)ᶜ := by ext x; simp
    dsimp [a, p]
    rw [hcomp, measureReal_compl measurableSet_closedBall, probReal_univ]
  have hp : 0 < p := by linarith
  have hratio : a / p ≤ (1 / 3 : ℝ) := (div_le_iff₀ hp).mpr (by linarith)
  apply (hμ.norm_tail_toReal_le_geometric R hp k).trans
  exact mul_le_mul ha (pow_le_pow_left₀ (div_nonneg ha0 hp.le) hratio k)
    (pow_nonneg (div_nonneg ha0 hp.le) k) (by norm_num)

end KLS
end
#print axioms KLS.IsIsotropic.norm_tail_fixed_radius_le
#print axioms KLS.measureLogConcave.isotropic_norm_tail_le
