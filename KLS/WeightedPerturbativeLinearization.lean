import KLS.AveragedCofactorHolder

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def mongeAmpereQuotientCoefficient (u : Space n → ℝ) (v : Space n) (h : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  averagedCofactor (coordinateHessian u x) (coordinateHessian u (x + h • v))

/-- Actual translated difference quotients of the weak weighted potential
satisfy a family of linear equations. The coefficients are uniformly
elliptic and Holder with constants independent of the translation. Smooth
source and target weights are explicitly required for the uniform bound
on the actual right-hand-side quotients. No Schauder estimate is assumed. -/
theorem weighted_perturbative_difference_quotient_family (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ γ : ℝ, 0 < Δ ∧ 0 < γ ∧ γ ≤ 1 ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α) →
      ContDiff ℝ 1 d₀.W → ContDiff ℝ 1 d₀.V →
      ∃ κ Λ C : ℝ, ∃ L : ℝ≥0, 0 < κ ∧ 0 < Λ ∧ 0 ≤ C ∧
        (∀ (v : Space n) (h : ℝ) (x : Space n), x ∈ closedBall (0 : Space n) (1 / 8) →
          x + h • v ∈ closedBall (0 : Space n) (1 / 8) →
          ContDiffAt ℝ 2 (translatedDifferenceQuotient d₀.u v h) x ∧
          (mongeAmpereQuotientCoefficient d₀.u v h x).IsSymm ∧
          (mongeAmpereQuotientCoefficient d₀.u v h x *
            coordinateHessian (translatedDifferenceQuotient d₀.u v h) x).trace =
              translatedDifferenceQuotient (weightedDataDensity d₀) v h x ∧
          |translatedDifferenceQuotient (weightedDataDensity d₀) v h x| ≤ L * ‖v‖ ∧
          ∀ w : Space n,
            κ * ‖w‖ ^ 2 ≤ inner ℝ w (matrixAction (mongeAmpereQuotientCoefficient d₀.u v h x) w) ∧
            inner ℝ w (matrixAction (mongeAmpereQuotientCoefficient d₀.u v h x) w) ≤ Λ * ‖w‖ ^ 2) ∧
        (∀ (v : Space n) (h : ℝ) (x y : Space n), x ∈ closedBall (0 : Space n) (1 / 8) →
          x + h • v ∈ closedBall (0 : Space n) (1 / 8) →
          y ∈ closedBall (0 : Space n) (1 / 8) → y + h • v ∈ closedBall (0 : Space n) (1 / 8) →
          ‖mongeAmpereQuotientCoefficient d₀.u v h x - mongeAmpereQuotientCoefficient d₀.u v h y‖ ≤
            C * ‖x - y‖ ^ γ) := by
  obtain ⟨Δ, γ, hΔ, hγ, hγone, hreg⟩ := weighted_perturbative_c2_holder_regularity hn hα
  refine ⟨Δ, γ, hΔ, hγ, hγone, ?_⟩
  intro d₀ hd hholder hW hV
  obtain ⟨hu, hMA, M, hM, hHol⟩ := hreg d₀ hd hholder
  let K := closedBall (0 : Space n) (1 / 8)
  have hKS : K ⊆ ball (0 : Space n) (1 / 4) := closedBall_subset_ball (by norm_num)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hH : ContinuousOn (coordinateHessian d₀.u) K :=
    (continuousOn_coordinateHessian_of_contDiffOn_two isOpen_ball hu).mono hKS
  have hpos : ∀ x ∈ K, (coordinateHessian d₀.u x).PosDef := fun x hx => (hMA x (hKS hx)).1
  obtain ⟨κ, Λ, hκ, hΛ, hell⟩ := averagedCofactor_uniform_ellipticity_of_continuous_hessian hK hH hpos
  obtain ⟨R, hR⟩ := hK.bddAbove_image hH.norm
  obtain ⟨C, hC, hCoeff⟩ := averagedCofactor_holder_of_bounded_holder_field hM
    (fun x hx => hR (mem_image_of_mem _ hx))
    (fun x hx y hy => hHol x (ball_subset_closedBall (hKS hx)) y (ball_subset_closedBall (hKS hy)))
  obtain ⟨L, hL⟩ := exists_bound_density_difference_quotients isOpen_ball hu hW hV
    hK (convex_closedBall _ _) hKS
  have hlocal (x : Space n) (hx : x ∈ K) : ContDiffAt ℝ 2 d₀.u x :=
    hu.contDiffAt (isOpen_ball.mem_nhds (hKS hx))
  refine ⟨κ, Λ, C, L, hκ, hΛ, hC, ?_, ?_⟩
  · intro v h x hx hxh
    refine ⟨contDiffAt_translatedDifferenceQuotient v h (hlocal x hx) (hlocal _ hxh),
      averagedCofactor_isSymm (hpos x hx) (hpos _ hxh), ?_, hL v h x hx hxh, hell x hx _ hxh⟩
    exact translated_difference_quotient_mongeAmpere
      (d₀.contDiff.differentiable (by norm_num)) v h (hlocal x hx) (hlocal _ hxh)
      (hpos x hx) (hpos _ hxh) (hMA x (hKS hx)).2 (hMA _ (hKS hxh)).2
  · intro v h x y hx hxh hy hyh
    exact hCoeff (h • v) x y hx hxh hy hyh

end KLS
end
