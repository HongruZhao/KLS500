import KLS.LocalizationNormBridge
import KLS.TiltCumulants
import KLS.CovarianceMatrix

/-! The actual compact-support standard localization law and its moments. -/
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization

variable {n : ℕ}

def exponent (t : ℝ) (c : Fin n → ℝ) (x : Space n) : ℝ :=
  (∑ i, c i * x i) - t * ‖x‖ ^ 2 / 2

def law (μ : Measure (Space n)) (t : ℝ) (c : Fin n → ℝ) : Measure (Space n) :=
  μ.tilted (exponent t c)

def mean (μ : Measure (Space n)) (t : ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ x, x i ∂law μ t c

def covariance (μ : Measure (Space n)) (t : ℝ) (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ProbabilityTheory.covariance (fun x : Space n => x i) (fun x => x j) (law μ t c)

theorem exponent_eq_inner (t : ℝ) (c : Fin n → ℝ) (x : Space n) :
    exponent t c x = inner ℝ (toSpace c) x - t * ‖x‖ ^ 2 / 2 := by
  rw [exponent, inner_toSpace_eq]

theorem continuous_exponent :
    Continuous (fun p : (ℝ × (Fin n → ℝ)) × Space n => exponent p.1.1 p.1.2 p.2) := by
  unfold exponent
  fun_prop

theorem continuous_exponent_state (t : ℝ) (c : Fin n → ℝ) : Continuous (exponent t c) := by
  unfold exponent
  fun_prop

theorem law_eq_normalized_density (μ : Measure (Space n)) (t : ℝ) (c : Fin n → ℝ) :
    law μ t c = μ.withDensity (fun x => ENNReal.ofReal
      (Real.exp (inner ℝ (toSpace c) x - t * ‖x‖ ^ 2 / 2) /
        tiltPartition μ (exponent t c))) := by
  simp only [law, tilted_eq_normalized_density, exponent_eq_inner]

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem law_isProbability (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ) :
    IsProbabilityMeasure (law μ t c) :=
  tilted_isProbability_of_compact_support hμ (continuous_exponent_state t c)

theorem law_support (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ) :
    (law μ t c).support = μ.support :=
  tilted_support_eq hμ (continuous_exponent_state t c)

/-- Joint parameter continuity uses ordinary compact-support integration;
no time derivative and no finite-feature lift are needed. -/
theorem continuous_tiltAverage_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [LocallyCompactSpace A]
    (hμ : IsCompact μ.support) {q : A → Space n → ℝ}
    (hq : Continuous (Function.uncurry q)) {f : Space n → ℝ} (hf : Continuous f) :
    Continuous (fun p => tiltAverage μ (q p) f) := by
  have hnum : Continuous (fun p => ∫ x in μ.support, f x * Real.exp (q p x) ∂μ) :=
    continuous_parametric_integral_of_continuous
      ((hf.comp continuous_snd).mul (Real.continuous_exp.comp hq)) hμ
  have hden : Continuous (fun p => ∫ x in μ.support, Real.exp (q p x) ∂μ) :=
    continuous_parametric_integral_of_continuous (f := fun p x => Real.exp (q p x))
      (Real.continuous_exp.comp hq) hμ
  have hrest : μ.restrict μ.support = μ :=
    Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  rw [hrest] at hnum hden
  have hpos (p : A) : tiltPartition μ (q p) ≠ 0 :=
    (tiltPartition_pos hμ (hq.comp (continuous_const.prodMk continuous_id))).ne'
  simp_rw [tiltAverage_eq_ratio]
  convert hnum.div hden hpos using 1
  funext p
  rfl

theorem continuous_average (hμ : IsCompact μ.support) {f : Space n → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => ∫ x, f x ∂law μ p.1 p.2) :=
  continuous_tiltAverage_param hμ continuous_exponent hf

theorem continuous_mean (hμ : IsCompact μ.support) :
    Continuous (Function.uncurry (mean μ)) := by
  apply continuous_pi
  intro i
  exact continuous_average hμ (by fun_prop)

theorem covariance_eq_moments (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ)
    (i j : Fin n) :
    covariance μ t c i j = (∫ x, x i * x j ∂law μ t c) - mean μ t c i * mean μ t c j := by
  haveI := law_isProbability hμ t c
  exact ProbabilityTheory.covariance_eq_sub
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop))

theorem continuous_covariance (hμ : IsCompact μ.support) :
    Continuous (Function.uncurry (covariance μ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun p : ℝ × (Fin n → ℝ) => covariance μ p.1 p.2 i j)
  simp_rw [covariance_eq_moments hμ]
  exact (continuous_average hμ (by fun_prop)).sub
    ((continuous_average hμ (f := fun x => x i) (by fun_prop)).mul
      (continuous_average hμ (f := fun x => x j) (by fun_prop)))

/-- A support-radius bound transfers to every normalized localization law. -/
theorem ae_norm_le (hμ : IsCompact μ.support) {R : ℝ}
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (t : ℝ) (c : Fin n → ℝ) :
    ∀ᵐ x ∂law μ t c, ‖x‖ ≤ R := by
  haveI := law_isProbability hμ t c
  filter_upwards [(law μ t c).support_mem_ae] with x hx
  exact hR x ((law_support hμ t c) ▸ hx)

theorem norm_mean_le (hμ : IsCompact μ.support) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R) (t : ℝ) (c : Fin n → ℝ) : ‖mean μ t c‖ ≤ R := by
  haveI := law_isProbability hμ t c
  apply (pi_norm_le_iff_of_nonneg hR0).mpr
  intro i
  have hb : ∀ᵐ x ∂law μ t c, ‖x i‖ ≤ R :=
    (ae_norm_le hμ hR t c).mono fun x hx => (PiLp.norm_apply_le x i).trans hx
  simpa [mean] using norm_integral_le_of_norm_le_const hb

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.continuous_mean
#print axioms KLS.StandardLocalization.continuous_covariance
#print axioms KLS.StandardLocalization.norm_mean_le
