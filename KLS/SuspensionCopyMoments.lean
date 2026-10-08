import KLS.LaplaceNoise
import KLS.DefinitionBridges

/-! Actual first and second moments of finite independent copies, including
cross moments of a centered signal orthogonal to the original coordinates. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace KLS

lemma integral_mul_distinct_copies {I E : Type*} [Fintype I] [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {g h : E → ℝ}
    (hg : Measurable g) (hh : Measurable h) {i j : I} (hij : i ≠ j) :
    (∫ x : I → E, g (x i) * h (x j) ∂Measure.pi (fun _ => μ)) =
      (∫ x, g x ∂μ) * ∫ x, h x ∂μ := by
  have hind := (iIndepFun_pi (μ := fun _ : I => μ)
    (X := fun _ : I => id) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hcomp : IndepFun (fun x : I → E => g (x i)) (fun x : I → E => h (x j))
      (Measure.pi (fun _ => μ)) := hind.comp hg hh
  rw [hcomp.integral_fun_mul_eq_mul_integral
    (hg.comp (measurable_pi_apply i)).aestronglyMeasurable
    (hh.comp (measurable_pi_apply j)).aestronglyMeasurable]
  rw [integral_comp_eval (μ := fun _ : I => μ) (i := i) hg.aestronglyMeasurable,
    integral_comp_eval (μ := fun _ : I => μ) (i := j) hh.aestronglyMeasurable]

lemma memLp_copy {I E : Type*} [Fintype I] [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ} (hg : MemLp g 2 μ) (i : I) :
    MemLp (fun x : I → E => g (x i)) 2 (Measure.pi (fun _ => μ)) :=
  hg.comp_measurePreserving (measurePreserving_eval (fun _ : I => μ) i)

lemma memLp_sum_copies {I E : Type*} [Fintype I] [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ} (hg : MemLp g 2 μ) :
    MemLp (fun x : I → E => ∑ i, g (x i)) 2 (Measure.pi (fun _ => μ)) := by
  exact memLp_finsetSum Finset.univ (fun i _ => memLp_copy hg i)

lemma integral_sum_copies {I E : Type*} [Fintype I] [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ} (hg : Integrable g μ) :
    (∫ x : I → E, ∑ i, g (x i) ∂Measure.pi (fun _ => μ)) =
      (Fintype.card I : ℝ) * ∫ x, g x ∂μ := by
  rw [integral_finsetSum Finset.univ (fun _ _ => integrable_comp_eval hg)]
  simp only [integral_comp_eval (μ := fun _ : I => μ) hg.aestronglyMeasurable,
    Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

lemma integral_sq_sum_centered_copies {I E : Type*} [Fintype I] [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ}
    (hgm : Measurable g) (hg : MemLp g 2 μ) (hmean : (∫ x, g x ∂μ) = 0) :
    (∫ x : I → E, (∑ i, g (x i)) ^ 2 ∂Measure.pi (fun _ => μ)) =
      (Fintype.card I : ℝ) * ∫ x, (g x) ^ 2 ∂μ := by
  classical
  have hint (i j : I) : Integrable (fun x : I → E => g (x i) * g (x j))
      (Measure.pi (fun _ => μ)) := (memLp_copy hg i).integrable_mul (memLp_copy hg j)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hint _ j)]
  have he (i j : I) :
      (∫ x : I → E, g (x i) * g (x j) ∂Measure.pi (fun _ => μ)) =
        if i = j then (∫ x, g x * g x ∂μ) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      exact integral_comp_eval (μ := fun _ : I => μ) (i := i)
        ((hgm.mul hgm).aestronglyMeasurable)
    · rw [ite_eq_right hij, integral_mul_distinct_copies hgm hgm hij, hmean, zero_mul]
  simp_rw [he]
  simp

lemma integral_coordinate_mul_copy {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (i k : Fin N) (j l : Fin n) :
    (∫ x : Fin N → Space n, x i j * x k l ∂Measure.pi (fun _ => μ)) =
      if (i, j) = (k, l) then 1 else 0 := by
  by_cases hik : i = k
  · subst k
    rw [integral_comp_eval (μ := fun _ : Fin N => μ) (i := i)
      (f := fun x : Space n => x j * x l) (by fun_prop)]
    have h := congrArg (fun A => A j l) hμ.2.2.2
    simpa [secondMomentMatrix, Matrix.one_apply] using h
  · rw [integral_mul_distinct_copies (μ := μ) (g := fun x : Space n => x j)
      (h := fun x : Space n => x l) (by fun_prop) (by fun_prop) hik,
      hμ.integral_coordinate j, zero_mul, ite_eq_right]
    exact fun he => hik (congrArg Prod.fst he)

lemma integral_coordinate_mul_sum_copies {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) {g : Space n → ℝ}
    (hgm : Measurable g) (hg : MemLp g 2 μ)
    (horth : ∀ j : Fin n, (∫ x, x j * g x ∂μ) = 0) (i : Fin N) (j : Fin n) :
    (∫ x : Fin N → Space n, x i j * ∑ k, g (x k) ∂Measure.pi (fun _ => μ)) = 0 := by
  classical
  have hint (k : Fin N) : Integrable (fun x : Fin N → Space n => x i j * g (x k))
      (Measure.pi (fun _ => μ)) :=
    (memLp_copy (hμ.memLp_coordinate j) i).integrable_mul (memLp_copy hg k)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun k _ => hint k)]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · subst k
    rw [integral_comp_eval (μ := fun _ : Fin N => μ) (i := i)
      (f := fun x : Space n => x j * g x) (by fun_prop), horth]
  · rw [integral_mul_distinct_copies (μ := μ) (g := fun x : Space n => x j)
      (by fun_prop) hgm hik,
      hμ.integral_coordinate j, zero_mul]

end KLS
end
#print axioms KLS.integral_sq_sum_centered_copies
#print axioms KLS.integral_coordinate_mul_sum_copies
