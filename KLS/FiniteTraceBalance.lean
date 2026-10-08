import KLS.RawWeakTraceFlux

open MeasureTheory Filter
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

/-- Sum finitely many integrable component equations before rearranging
the trace energy. Boundary integrability is derived from the flux and
localized gradient term rather than assumed. -/
theorem integral_balance_of_finite_component_evolution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {L : Fin n → Fin n → Fin n → α → ℝ}
    {R : Fin n → Fin n → α → ℝ} {S A F D E : α → ℝ}
    (hL : ∀ i j a, Integrable (L i j a) μ)
    (hR : ∀ i j, Integrable (R i j) μ)
    (hS : Integrable S μ) (hA : Integrable A μ)
    (hF : Integrable F μ) (hD : Integrable D μ)
    (hleft : ∀ᵐ x ∂μ, (∑ i, ∑ j, ∑ a, L i j a x) = (1 / 2 : ℝ) * E x + A x)
    (hright : ∀ᵐ x ∂μ, (∑ i, ∑ j, R i j x) = -S x + F x + D x)
    (hevolution : ∀ i j, -(∑ a, ∫ x, L i j a x ∂μ) = ∫ x, R i j x ∂μ) :
    Integrable E μ ∧
      (∫ x, A x + F x + D x ∂μ) = (∫ x, S x ∂μ) - (1 / 2 : ℝ) * ∫ x, E x ∂μ := by
  have hLa (i j : Fin n) : Integrable (fun x => ∑ a, L i j a x) μ :=
    integrable_finsetSum _ fun a _ => hL i j a
  have hLj (i : Fin n) : Integrable (fun x => ∑ j, ∑ a, L i j a x) μ :=
    integrable_finsetSum _ fun j _ => hLa i j
  have hLi : Integrable (fun x => ∑ i, ∑ j, ∑ a, L i j a x) μ :=
    integrable_finsetSum _ fun i _ => hLj i
  have hRj (i : Fin n) : Integrable (fun x => ∑ j, R i j x) μ :=
    integrable_finsetSum _ fun j _ => hR i j
  have hE : Integrable E μ := by
    apply ((hLi.sub hA).const_mul 2).congr
    filter_upwards [hleft] with x hx
    change 2 * ((∑ i, ∑ j, ∑ a, L i j a x) - A x) = E x
    linarith
  have hLint : (∫ x, ∑ i, ∑ j, ∑ a, L i j a x ∂μ) =
      ∑ i, ∑ j, ∑ a, ∫ x, L i j a x ∂μ := by
    rw [integral_finsetSum _ fun i _ => hLj i]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ fun j _ => hLa i j]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finsetSum _ fun a _ => hL i j a
  have hRint : (∫ x, ∑ i, ∑ j, R i j x ∂μ) =
      ∑ i, ∑ j, ∫ x, R i j x ∂μ := by
    rw [integral_finsetSum _ fun i _ => hRj i]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ fun j _ => hR i j
  have hsum : -(∫ x, ∑ i, ∑ j, ∑ a, L i j a x ∂μ) =
      ∫ x, ∑ i, ∑ j, R i j x ∂μ := by
    rw [hLint, hRint]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Finset.sum_neg_distrib] using hevolution i j
  have hl : (∫ x, ∑ i, ∑ j, ∑ a, L i j a x ∂μ) =
      (1 / 2 : ℝ) * (∫ x, E x ∂μ) + ∫ x, A x ∂μ := by
    calc
      _ = ∫ x, (1 / 2 : ℝ) * E x + A x ∂μ := integral_congr_ae hleft
      _ = _ := by rw [integral_add (hE.const_mul _) hA, integral_const_mul]
  have hr : (∫ x, ∑ i, ∑ j, R i j x ∂μ) =
      -(∫ x, S x ∂μ) + (∫ x, F x ∂μ) + ∫ x, D x ∂μ := by
    calc
      _ = ∫ x, -S x + F x + D x ∂μ := integral_congr_ae hright
      _ = _ := by
        rw [integral_add (f := fun x => -S x + F x) (g := D) (hS.neg.add hF) hD,
          integral_add (f := fun x => -S x) (g := F) hS.neg hF, integral_neg]
  refine ⟨hE, ?_⟩
  rw [integral_add (f := fun x => A x + F x) (g := D) (hA.add hF) hD,
    integral_add (f := A) (g := F) hA hF]
  rw [hl, hr] at hsum
  linarith

end KLS
end
