import KLS.HarmonicPointwiseCalculus

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateDerivative_sq {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => f y ^ 2) i x = 2 * f x * coordinateDerivative f i x := by
  simp_rw [pow_two]
  rw [coordinateDerivative_mul (hf x) (hf x)]
  ring

def harmonicBernsteinAux (η u f : Space n → ℝ) (A : ℝ) (x : Space n) : ℝ :=
  η x ^ 2 * u x ^ 2 + A * f x ^ 2

lemma contDiff_harmonicBernsteinAux {η u f : Space n → ℝ} {m : WithTop ℕ∞}
    (hη : ContDiff ℝ m η) (hu : ContDiff ℝ m u) (hf : ContDiff ℝ m f) (A : ℝ) :
    ContDiff ℝ m (harmonicBernsteinAux η u f A) :=
  ((hη.pow 2).mul (hu.pow 2)).add (contDiff_const.mul (hf.pow 2))

/-- The Bernstein auxiliary has a strictly positive Laplacian wherever the
chosen harmonic derivative is nonzero. All quantities are actual derivatives. -/
theorem laplacian_harmonicBernsteinAux_lower {η u f : Space n → ℝ}
    (hη : ContDiff ℝ 2 η) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 2 f)
    (R : ℝ) (x : Space n) (hηupper : η x ≤ R ^ 2)
    (hηlap : coordinateLaplacian η x = -2 * n)
    (hηenergy : harmonicGradientSquare η x ≤ 4 * R ^ 2)
    (huLap : coordinateLaplacian u x = 0) (hfLap : coordinateLaplacian f x = 0)
    (huf : u x ^ 2 ≤ harmonicGradientSquare f x) :
    4 * R ^ 2 * u x ^ 2 ≤
      coordinateLaplacian (harmonicBernsteinAux η u f ((30 + 2 * n) * R ^ 2)) x := by
  let A : ℝ := (30 + 2 * n) * R ^ 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hcalc : coordinateLaplacian (harmonicBernsteinAux η u f A) x =
      (2 * η x * coordinateLaplacian η x + 2 * harmonicGradientSquare η x) * u x ^ 2 +
      8 * η x * u x * (∑ i, coordinateDerivative η i x * coordinateDerivative u i x) +
      2 * η x ^ 2 * harmonicGradientSquare u x + 2 * A * harmonicGradientSquare f x := by
    change coordinateLaplacian ((fun y => η y ^ 2 * u y ^ 2) + A • (fun y => f y ^ 2)) x = _
    rw [coordinateLaplacian_add (g := A • (fun y => f y ^ 2)) ((hη.pow 2).mul (hu.pow 2)) (contDiff_const.smul (hf.pow 2)),
      coordinateLaplacian_smul (hf.pow 2), coordinateLaplacian_mul (hη.pow 2) (hu.pow 2),
      coordinateLaplacian_sq hη, coordinateLaplacian_sq hu, coordinateLaplacian_sq hf,
      huLap, hfLap]
    simp_rw [coordinateDerivative_sq (hη.differentiable (by norm_num)),
      coordinateDerivative_sq (hu.differentiable (by norm_num))]
    have hs : (∑ i, (2 * η x * coordinateDerivative η i x) *
        (2 * u x * coordinateDerivative u i x)) =
        4 * η x * u x * ∑ i, coordinateDerivative η i x * coordinateDerivative u i x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hs]
    ring
  have hsquares : 0 ≤ η x ^ 2 * harmonicGradientSquare u x +
      8 * η x * u x * (∑ i, coordinateDerivative η i x * coordinateDerivative u i x) +
      16 * u x ^ 2 * harmonicGradientSquare η x := by
    unfold harmonicGradientSquare
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [sq_nonneg (η x * coordinateDerivative u i x + 4 * u x * coordinateDerivative η i x)]
  have he := mul_le_mul_of_nonneg_right hηenergy (sq_nonneg (u x))
  have het := mul_le_mul_of_nonneg_right hηupper
    (mul_nonneg (show (0 : ℝ) ≤ 4 * n by positivity) (sq_nonneg (u x)))
  have haf := mul_le_mul_of_nonneg_left huf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA0)
  have heu : 0 ≤ η x ^ 2 * harmonicGradientSquare u x :=
    mul_nonneg (sq_nonneg _) (harmonicGradientSquare_nonneg _ _)
  change 4 * R ^ 2 * u x ^ 2 ≤ coordinateLaplacian (harmonicBernsteinAux η u f A) x
  rw [hcalc, hηlap]
  dsimp [A] at haf ⊢
  nlinarith

end KLS
end
