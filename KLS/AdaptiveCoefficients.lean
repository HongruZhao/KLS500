import KLS.AdaptiveFeatureTilt
import KLS.TiltCovariancePositive
import KLS.MatrixEntrySmooth

/-! Genuine adaptive localization coefficients. Full affine support derives
invertibility at every finite parameter; the inverse and drift are C-infinity. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem covariance_eq_covarianceMatrix (hμ : IsCompact μ.support) (p : Parameter n) :
    covariance μ p.1 p.2 = covarianceMatrix (law μ p.1 p.2) := by
  letI := law_isProbability hμ p.1 p.2
  have hid : MemLp (id : Space n → Space n) 2 (law μ p.1 p.2) := by
    apply MemLp.of_eval_piLp
    intro i
    exact memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop)
  ext i j
  exact (covarianceMatrix_apply hid i j).symm

theorem covariance_posDef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    (covariance μ p.1 p.2).PosDef := by
  rw [covariance_eq_covarianceMatrix hμ p]
  exact covarianceMatrix_tilted_posDef hμ hfull (continuous_exponent p.1 p.2)

theorem covariance_posDef_of_isotropic (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (p : Parameter n) : (covariance μ p.1 p.2).PosDef :=
  covariance_posDef hμ hiso.affineSpan_support_eq_top p

theorem contDiff_covariance_matrix (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Parameter n => covariance μ p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_covariance hμ i j

def inverseCovariance (μ : Measure (Space n)) (p : Parameter n) : Matrix (Fin n) (Fin n) ℝ :=
  (covariance μ p.1 p.2)⁻¹

def inverseSqrtCovariance (μ : Measure (Space n)) (p : Parameter n) : Matrix (Fin n) (Fin n) ℝ :=
  inverseSqrtMatrix (covariance μ p.1 p.2)

theorem inverseCovariance_posDef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    (inverseCovariance μ p).PosDef :=
  (covariance_posDef hμ hfull p).inv

theorem inverseSqrtCovariance_isSymm (p : Parameter n) :
    (inverseSqrtCovariance μ p).IsSymm :=
  inverseSqrtMatrix_isSymm _

theorem inverseSqrtCovariance_whitens (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    inverseSqrtCovariance μ p * covariance μ p.1 p.2 * (inverseSqrtCovariance μ p).transpose = 1 :=
  inverseSqrtMatrix_mul_self_mul_transpose (covariance_posDef hμ hfull p)

/-- The actual coefficient of dc: A^{-1} a. -/
def linearDrift (μ : Measure (Space n)) (p : Parameter n) : Fin n → ℝ :=
  inverseCovariance μ p *ᵥ mean μ p.1 p.2

/-- The actual finite-variation coefficients (A^{-1}a,A^{-1}). -/
def drift (μ : Measure (Space n)) (p : Parameter n) : Parameter n :=
  (linearDrift μ p, inverseCovariance μ p)

/-- The kth Brownian direction is (A^{-1/2} e_k,0). -/
def diffusion (μ : Measure (Space n)) (k : Fin n) (p : Parameter n) : Parameter n :=
  (fun i => inverseSqrtCovariance μ p i k, 0)

theorem contDiff_inverseCovariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (inverseCovariance μ) := by
  apply contDiff_inverse_of_entries (contDiff_covariance hμ)
  intro p
  exact (covariance_posDef hμ hfull p).det_pos.ne'

theorem contDiff_linearDrift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (linearDrift μ) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Parameter n =>
    ∑ j, inverseCovariance μ p i j * mean μ p.1 p.2 j)
  apply ContDiff.sum
  intro j _
  exact ((contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ (Fin n → ℝ) i).comp (contDiff_inverseCovariance hμ hfull))).mul
    ((contDiff_apply ℝ ℝ j).comp (contDiff_mean hμ))

theorem contDiff_drift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (drift μ) :=
  (contDiff_linearDrift hμ hfull).prodMk (contDiff_inverseCovariance hμ hfull)

theorem locallyLipschitz_inverseCovariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : LocallyLipschitz (inverseCovariance μ) :=
  ((contDiff_inverseCovariance hμ hfull).of_le (by simp)).locallyLipschitz

theorem locallyLipschitz_drift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : LocallyLipschitz (drift μ) :=
  ((contDiff_drift hμ hfull).of_le (by simp)).locallyLipschitz

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.covariance_posDef
#print axioms KLS.AdaptiveLocalization.contDiff_inverseCovariance
#print axioms KLS.AdaptiveLocalization.contDiff_drift
#print axioms KLS.AdaptiveLocalization.locallyLipschitz_drift
