import KLS.WeakMomentCompactDifferenceEnergy

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A continuous finite potential has a finite reciprocal-density bound on
 every compact set, constructed from its actual exponential. -/
theorem exists_compact_exp_potential_bound
    {u : Space n → ℝ} (hu : Continuous u) {S : Set (Space n)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, Real.exp (u x) ≤ B := by
  obtain ⟨C,hC⟩ := hS.bddAbove_image (Real.continuous_exp.comp hu).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x hx => (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

/-- The actual reciprocal density converts a nonnegative compact weighted
 integral into an unweighted local integral. -/
theorem integral_restrict_le_potential_cutoff
    {u E η : Space n → ℝ} (hu : Continuous u) {S : Set (Space n)} (hS : IsCompact S)
    {B : ℝ} (hB : 0 ≤ B) (hBu : ∀ x ∈ S, Real.exp (u x) ≤ B)
    (hE : Integrable E (potentialMeasure u)) (hE0 : ∀ x, 0 ≤ E x)
    (hηE : Integrable (fun x => η x * E x) (potentialMeasure u))
    (hη0 : ∀ x, 0 ≤ η x) (hηS : ∀ x ∈ S, 1 ≤ η x) :
    (∫ x in S, E x) ≤ B * ∫ x, η x * E x ∂potentialMeasure u := by
  let c : Space n → ℝ := S.indicator (fun x => Real.exp (u x))
  have hm : Measurable c := (Real.continuous_exp.comp hu).measurable.indicator hS.measurableSet
  have hbound : ∀ x, ‖c x‖ ≤ B := by
    intro x
    by_cases hx : x ∈ S
    · simpa only [c,indicator_of_mem hx,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hBu x hx
    · simpa only [c,indicator_of_notMem hx,norm_zero] using hB
  have hi : Integrable (fun x => c x*E x) (potentialMeasure u) :=
    hE.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hbound)
  have heq : (∫ x in S, E x) = ∫ x, c x*E x ∂potentialMeasure u := by
    rw [← integral_indicator hS.measurableSet,integral_potentialMeasure hu.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · simp only [c,indicator_of_mem hx]
        have hexp : Real.exp (u x)*Real.exp (-u x) = 1 := by rw [← Real.exp_add]; simp
        calc
          E x = (Real.exp (u x)*Real.exp (-u x))*E x := by rw [hexp,one_mul]
          _ = _ := by ring
      · simp only [c,indicator_of_notMem hx,zero_mul]
  have hbnd : ∀ x, c x*E x ≤ B*(η x * E x) := by
    intro x
    by_cases hx : x ∈ S
    · change S.indicator (fun y => Real.exp (u y)) x*E x ≤ _
      rw [indicator_of_mem hx]
      have hEη : E x ≤ η x * E x := by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right (hηS x hx) (hE0 x))
      exact (mul_le_mul_of_nonneg_right (hBu x hx) (hE0 x)).trans
        (mul_le_mul_of_nonneg_left hEη hB)
    · change S.indicator (fun y => Real.exp (u y)) x*E x ≤ _
      rw [indicator_of_notMem hx,zero_mul]
      exact mul_nonneg hB (mul_nonneg (hη0 x) (hE0 x))
  rw [heq]
  exact (integral_mono hi (hηE.const_mul B) hbnd).trans_eq (integral_const_mul _ _)

/-- Every scalar entry square is bounded by the actual squared Frobenius
 norm of its matrix. -/
theorem sq_entry_le_matrixFrobeniusSq (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (M i j)^2 ≤ matrixFrobeniusSq M := by
  unfold matrixFrobeniusSq
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (M i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (M k l))) (Finset.mem_univ i))

theorem matrixFrobeniusSq_nonneg (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ matrixFrobeniusSq M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))

end KLS
end
