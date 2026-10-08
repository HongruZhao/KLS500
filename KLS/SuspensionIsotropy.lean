import KLS.SuspensionLogConcavity
import KLS.SuspensionCopyMoments
import KLS.SuspensionScalarMoments

/-! Isotropy of the literal product-copy suspension law. All coordinate
moments are derived on the actual independent product probability space. -/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators ContDiff
noncomputable section
namespace KLS

lemma isIsotropic_map_of_coordinateMoments {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {n : ℕ} {T : E → Space n}
    (hT : Measurable T) (hL2 : ∀ i, MemLp (fun x => T x i) 2 μ)
    (hmean : ∀ i, (∫ x, T x i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ x, T x i * T x j ∂μ) = if i = j then 1 else 0) :
    IsIsotropic (μ.map T) := by
  have hm : MemLp (fun x : Space n => x) 2 (μ.map T) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hT.aemeasurable).2
      (MemLp.of_eval_piLp hL2)
  have hi := hm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨hi, ?_, fun i j => (hm.eval_piLp i).integrable_mul (hm.eval_piLp j), ?_⟩
  · ext i
    have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hi
    change (∫ x : Space n, x i ∂μ.map T) = (∫ x : Space n, x ∂μ.map T) i at he
    rw [← he, integral_map hT.aemeasurable (by fun_prop), hmean]
    rfl
  · ext i j
    change (∫ x : Space n, x i * x j ∂μ.map T) = _
    rw [integral_map hT.aemeasurable (by fun_prop), hsecond]
    rfl

lemma euclideanSuspensionLaw_eq_product_map {n N : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (hf : Measurable f) (β σ c : ℝ) :
    euclideanSuspensionLaw (N := N) μ f β σ c =
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceNoiseLaw β)).map
        (fun p => suspensionCoordinates n N
          (p.1, suspensionExtra (fun x => c * ∑ i, f (x i)) σ p)) := by
  rw [euclideanSuspensionLaw, laplaceSuspensionLaw,
    Measure.map_map (suspensionCoordinates n N).measurable (by fun_prop)]
  rfl

lemma isIsotropic_euclideanSuspensionLaw {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) {f : Space n → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 μ) (hfmean : (∫ x, f x ∂μ) = 0)
    (hfsq : (∫ x, (f x) ^ 2 ∂μ) = 1)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂μ) = 0)
    {β σ c : ℝ} (hβ : 0 < β) (hc : c ^ 2 * (N : ℝ) = 1)
    (hσ : σ ^ 2 = 1 + 2 / β ^ 2) :
    IsIsotropic (euclideanSuspensionLaw (N := N) μ f β σ c) := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  let F : (Fin N → Space n) → ℝ := fun x => c * ∑ i, f (x i)
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  have hF : MemLp F 2 ν := (memLp_sum_copies hf).const_mul c
  have hFmean : (∫ x, F x ∂ν) = 0 := by
    rw [show F = (fun x => c * ∑ i, f (x i)) from rfl, integral_const_mul,
      integral_sum_copies (hf.integrable (by norm_num)), hfmean, mul_zero, mul_zero]
  have hFsq : (∫ x, F x ^ 2 ∂ν) = 1 := by
    have he (x : Fin N → Space n) : F x ^ 2 = c ^ 2 * (∑ i, f (x i)) ^ 2 := by
      dsimp [F]
      ring
    simp_rw [he]
    rw [integral_const_mul, integral_sq_sum_centered_copies hfm hf hfmean, hfsq, mul_one,
      Fintype.card_fin, hc]
  have hForth (i : Fin N) (j : Fin n) : (∫ x, x i j * F x ∂ν) = 0 := by
    have he (x : Fin N → Space n) : x i j * F x = c * (x i j * ∑ k, f (x k)) := by
      dsimp [F]
      ring
    simp_rw [he]
    rw [integral_const_mul, integral_coordinate_mul_sum_copies hμ hfm hf hforth, mul_zero]
  have hσne : σ ^ 2 ≠ 0 := by rw [hσ]; positivity
  let T : ((Fin N → Space n) × ℝ) → Space (suspensionDimension n N) := fun p =>
    suspensionCoordinates n N (p.1, suspensionExtra F σ p)
  have hTcoord (a : SuspensionIndex n N) (p : (Fin N → Space n) × ℝ) :
      T p (Fintype.equivFin _ a) =
        Option.elim a (suspensionExtra F σ p) (fun ij => p.1 ij.1 ij.2) :=
    suspensionCoordinates_apply n N _ a
  have hL2 (a : SuspensionIndex n N) :
      MemLp (fun p => T p (Fintype.equivFin _ a)) 2 (ν.prod (laplaceNoiseLaw β)) := by
    simp_rw [hTcoord]
    cases a with
    | none => exact memLp_suspensionExtra hF hβ σ
    | some ij => exact (memLp_copy (hμ.memLp_coordinate ij.2) ij.1).comp_fst _
  have hmean (a : SuspensionIndex n N) :
      (∫ p, T p (Fintype.equivFin _ a) ∂ν.prod (laplaceNoiseLaw β)) = 0 := by
    simp_rw [hTcoord]
    cases a with
    | none => exact integral_suspensionExtra (hF.integrable (by norm_num)) hFmean hβ σ
    | some ij =>
      simp only [Option.elim_some]
      rw [integral_fun_fst (fun x : Fin N → Space n => x ij.1 ij.2),
        integral_comp_eval (μ := fun _ : Fin N => μ) (i := ij.1)
          (f := fun x : Space n => x ij.2) (by fun_prop), hμ.integral_coordinate]
      simp
  have hsecond (a b : SuspensionIndex n N) :
      (∫ p, T p (Fintype.equivFin _ a) * T p (Fintype.equivFin _ b)
        ∂ν.prod (laplaceNoiseLaw β)) = if a = b then 1 else 0 := by
    simp_rw [hTcoord]
    cases a with
    | none =>
      cases b with
      | none =>
        simp only [Option.elim_none, ite_true, ← sq]
        rw [integral_sq_suspensionExtra hF hFsq hβ, ← hσ, div_self hσne]
      | some ij =>
        simp only [Option.elim_none, Option.elim_some, reduceCtorEq, ite_false]
        simp_rw [mul_comm]
        exact integral_mul_suspensionExtra hF (memLp_copy (hμ.memLp_coordinate ij.2) ij.1)
          (hForth ij.1 ij.2) hβ σ
    | some ij =>
      cases b with
      | none =>
        simp only [Option.elim_none, Option.elim_some, reduceCtorEq, ite_false]
        exact integral_mul_suspensionExtra hF (memLp_copy (hμ.memLp_coordinate ij.2) ij.1)
          (hForth ij.1 ij.2) hβ σ
      | some kl =>
        simp only [Option.elim_some, Option.some.injEq]
        rw [integral_fun_fst (fun x : Fin N → Space n => x ij.1 ij.2 * x kl.1 kl.2),
          integral_coordinate_mul_copy hμ]
        simp
  rw [euclideanSuspensionLaw_eq_product_map μ f hfm β σ c]
  apply isIsotropic_map_of_coordinateMoments (T := T) (by
    exact (suspensionCoordinates n N).measurable.comp (by dsimp [F, suspensionExtra]; fun_prop))
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective i
    exact hL2 a
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective i
    exact hmean a
  · intro i j
    obtain ⟨a, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective i
    obtain ⟨b, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective j
    simpa only [Equiv.apply_eq_iff_eq] using hsecond a b

def suspensionNormalization (β : ℝ) : ℝ := Real.sqrt (1 + 2 / β ^ 2)

lemma suspensionNormalization_pos (β : ℝ) : 0 < suspensionNormalization β := by
  unfold suspensionNormalization
  positivity

lemma isIsotropic_euclideanSuspensionLaw_normalized {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) {f : Space n → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 μ) (hfmean : (∫ x, f x ∂μ) = 0)
    (hfsq : (∫ x, (f x) ^ 2 ∂μ) = 1)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂μ) = 0)
    {β : ℝ} (hβ : 0 < β) (hN : 0 < N) :
    IsIsotropic (euclideanSuspensionLaw (N := N) μ f β
      (suspensionNormalization β) (Real.sqrt N)⁻¹) := by
  apply isIsotropic_euclideanSuspensionLaw hμ hfm hf hfmean hfsq hforth hβ
  · rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N), inv_mul_cancel₀]
    exact_mod_cast hN.ne'
  · exact Real.sq_sqrt (by positivity)

/-- The literal normalized suspension is a genuine member of the original
isotropic log-concave density class, for a constructed positive copy count. -/
theorem exists_isKLSMeasure_euclideanSuspensionLaw {n : ℕ} {V f : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (hfC : ContDiff ℝ 2 f)
    [IsProbabilityMeasure (potentialMeasure V)] (hμ : IsIsotropic (potentialMeasure V))
    (hf : MemLp f 2 (potentialMeasure V))
    (hfmean : (∫ x, f x ∂potentialMeasure V) = 0)
    (hfsq : (∫ x, (f x) ^ 2 ∂potentialMeasure V) = 1)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂potentialMeasure V) = 0)
    {κ M β : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hβ : 0 < β) :
    ∃ N : ℕ, 0 < N ∧ IsKLSMeasure (euclideanSuspensionLaw (N := N)
      (potentialMeasure V) f β (suspensionNormalization β) (Real.sqrt N)⁻¹) := by
  obtain ⟨N, hN, hlog⟩ := exists_logConcave_euclideanSuspensionLaw hV hfC hκ hlower hbound hβ
  have hd := hlog (suspensionNormalization β) (suspensionNormalization_pos β)
  refine ⟨N, hN, ?_⟩
  exact ⟨isProbabilityMeasure_euclideanSuspensionLaw _ _ hfC.continuous.measurable hβ,
    hd.absolutelyContinuousLebesgue, hd,
    isIsotropic_euclideanSuspensionLaw_normalized hμ hfC.continuous.measurable hf hfmean hfsq hforth hβ hN⟩

end KLS
end
#print axioms KLS.isIsotropic_euclideanSuspensionLaw
#print axioms KLS.exists_isKLSMeasure_euclideanSuspensionLaw
