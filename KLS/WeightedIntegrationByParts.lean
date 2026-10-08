import KLS.Definitions

/-!+# Weighted integration by parts for a finite real potential

The measure is actually defined by its Lebesgue density `exp (-φ)`.
The four integrability conditions are retained in the theorem type. Neither
convexity nor probability normalization is needed for this integration identity.
No moment-map existence or Brascamp--Lieb inequality is assumed or proved here.
-/

open MeasureTheory Set Filter

noncomputable section
namespace KLS

def potentialMeasure {n : ℕ} (φ : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))

theorem integrable_potentialMeasure_iff {n : ℕ} {φ f : Space n → ℝ}
    (hφ : Measurable φ) : Integrable f (potentialMeasure φ) ↔
      Integrable (fun x => f x * Real.exp (-φ x)) volume := by
  unfold potentialMeasure
  simpa only [Pi.neg_apply, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    (integrable_withDensity_iff (hφ.neg.exp.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top))

theorem integral_potentialMeasure {n : ℕ} {φ : Space n → ℝ}
    (hφ : Measurable φ) (f : Space n → ℝ) :
    (∫ x, f x ∂potentialMeasure φ) = ∫ x, f x * Real.exp (-φ x) := by
  unfold potentialMeasure
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by
    simpa only [Pi.neg_apply] using hφ.neg.exp.ennreal_ofReal
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm] using
    (integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f)

theorem fderiv_exp_neg_apply {n : ℕ} {φ : Space n → ℝ} {x : Space n}
    (hφ : DifferentiableAt ℝ φ x) (v : Space n) :
    fderiv ℝ (fun y => Real.exp (-φ y)) x v =
      -(Real.exp (-φ x) * fderiv ℝ φ x v) := by
  have hd := congrArg (fun L : Space n →L[ℝ] ℝ => L v) hφ.hasFDerivAt.neg.exp.fderiv
  simpa only [Pi.neg_apply, smul_apply, neg_apply, smul_eq_mul, mul_neg] using hd

/-- The weighted integration-by-parts formula used in Letwin A.3. All
boundary/integrability requirements are made explicit as four L¹ hypotheses.
The proof uses the library's integrable Haar integration-by-parts theorem. -/
theorem integral_mul_fderiv_potentialMeasure {n : ℕ}
    {φ f g : Space n → ℝ} (hφ : Differentiable ℝ φ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : Space n)
    (hfg : Integrable (fun x => f x * g x) (potentialMeasure φ))
    (hdfg : Integrable (fun x => fderiv ℝ f x v * g x) (potentialMeasure φ))
    (hfdg : Integrable (fun x => f x * fderiv ℝ g x v) (potentialMeasure φ))
    (hfgdφ : Integrable (fun x => f x * g x * fderiv ℝ φ x v)
      (potentialMeasure φ)) :
    (∫ x, f x * fderiv ℝ g x v ∂potentialMeasure φ) =
      (∫ x, f x * g x * fderiv ℝ φ x v ∂potentialMeasure φ) -
      ∫ x, fderiv ℝ f x v * g x ∂potentialMeasure φ := by
  have hm := hφ.continuous.measurable
  have hfgW := (integrable_potentialMeasure_iff hm).1 hfg
  have hdfgW := (integrable_potentialMeasure_iff hm).1 hdfg
  have hfdgW := (integrable_potentialMeasure_iff hm).1 hfdg
  have hfgdφW := (integrable_potentialMeasure_iff hm).1 hfgdφ
  have hprod (x : Space n) : fderiv ℝ (fun y => f y * g y) x v =
      fderiv ℝ f x v * g x + f x * fderiv ℝ g x v := by
    have heq : (fun y => f y * g y) = f * g := by funext y; rfl
    rw [heq]
    have hd := congrArg (fun L : Space n →L[ℝ] ℝ => L v)
      ((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv
    simpa only [Pi.mul_apply, add_apply, smul_apply,
      smul_eq_mul, mul_comm, add_comm] using hd
  have hleft : Integrable (fun x =>
      fderiv ℝ (fun y => f y * g y) x v * Real.exp (-φ x)) volume := by
    convert hdfgW.add hfdgW using 1
    funext x
    dsimp only [Pi.add_apply]
    rw [hprod]
    ring
  have hright : Integrable (fun x =>
      (f x * g x) * fderiv ℝ (fun y => Real.exp (-φ y)) x v) volume := by
    convert hfgdφW.neg using 1
    funext x
    dsimp only [Pi.neg_apply]
    rw [fderiv_exp_neg_apply (hφ x)]
    ring
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hleft hright hfgW (fun x _ => (hf x).mul (hg x))
      (fun x _ => (hφ x).neg.exp)
  have hright_eq :
      (∫ x, (f x * g x) * fderiv ℝ (fun y => Real.exp (-φ y)) x v) =
      -(∫ x, (f x * g x * fderiv ℝ φ x v) * Real.exp (-φ x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [fderiv_exp_neg_apply (hφ x)]
      ring
  have hleft_eq :
      (∫ x, fderiv ℝ (fun y => f y * g y) x v * Real.exp (-φ x)) =
      (∫ x, (fderiv ℝ f x v * g x) * Real.exp (-φ x)) +
      ∫ x, (f x * fderiv ℝ g x v) * Real.exp (-φ x) := by
    rw [← integral_add hdfgW hfdgW]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hprod]
      ring
  rw [hright_eq, hleft_eq] at hibp
  simp only [integral_potentialMeasure hm]
  linarith

end KLS
end

#print axioms KLS.integrable_potentialMeasure_iff
#print axioms KLS.integral_potentialMeasure
#print axioms KLS.integral_mul_fderiv_potentialMeasure
