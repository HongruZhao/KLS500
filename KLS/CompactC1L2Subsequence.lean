import KLS.MomentDistributionalHarmonicLimit
import KLS.WeightedCompactEmbedding

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A compactly supported C1 family with actual uniform value and coordinate
energy bounds has a genuine strongly L2 convergent subsequence. The proof uses
the proved translation inequality and Frechet--Kolmogorov compactness. -/
theorem exists_strong_L2_subsequence_of_compact_C1_bounds
    {f : ℕ → Space n → ℝ} (hf : ∀ k, ContDiff ℝ 1 (f k))
    {R A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : ∀ k, tsupport (f k) ⊆ closedBall (0 : Space n) R)
    (hv : ∀ k, (∫ x, f k x ^ 2) ≤ A)
    (hd : ∀ k i, (∫ x, coordinateDerivative (f k) i x ^ 2) ≤ B) :
    ∃ (g : Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ),
      StrictMono σ ∧ Tendsto (fun k => eLpNorm (f (σ k) - (g : Space n → ℝ)) 2 volume) atTop (𝓝 0) := by
  have hc (k : ℕ) : HasCompactSupport (f k) :=
    (isCompact_closedBall (0 : Space n) R).of_isClosed_subset (isClosed_tsupport _) (hs k)
  have hfm (k : ℕ) : MemLp (f k) 2 volume :=
    (hf k).continuous.memLp_of_hasCompactSupport (hc k)
  have hdm (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (f k) i) 2 volume :=
    (contDiff_coordinateDerivative (hf k) (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative (hc k) i)
  let F (k : ℕ) : Lp ℝ 2 volume := (hfm k).toLp (f k)
  let D (k : ℕ) (i : Fin n) : Lp ℝ 2 volume := (hdm k i).toLp (coordinateDerivative (f k) i)
  have hFn (k : ℕ) : ‖F k‖ ≤ Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    have he : (∫ x, F k x ^ 2) = ∫ x, f k x ^ 2 :=
      integral_congr_ae ((hfm k).coeFn_toLp.mono (fun _ hx => by dsimp only; exact congrArg (fun t : ℝ => t ^ 2) hx))
    rw [he]
    exact hv k
  have hDn (k : ℕ) (i : Fin n) : ‖D k i‖ ≤ Real.sqrt B := by
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    have he : (∫ x, D k i x ^ 2) = ∫ x, coordinateDerivative (f k) i x ^ 2 :=
      integral_congr_ae ((hdm k i).coeFn_toLp.mono (fun _ hx => by dsimp only; exact congrArg (fun t : ℝ => t ^ 2) hx))
    rw [he]
    exact hd k i
  have hmod (k : ℕ) (h : Space n) :
      ‖transL2 h (F k) - F k‖ ≤ ((n : ℝ) * Real.sqrt B) * ‖h‖ := by
    have he := compact_translation_bound_of_smooth (hf k) (hc k) (F k) (D k)
      (hfm k).coeFn_toLp (fun i => (hdm k i).coeFn_toLp) h
    have hsum : (∑ i : Fin n, ‖D k i‖) ≤ n * Real.sqrt B := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hDn k i)
    exact he.trans (mul_le_mul_of_nonneg_right hsum (norm_nonneg h))
  have htb : TotallyBounded (range F) := by
    apply EllipticPdes.Analysis.totallyBounded_of_lipschitz_translation
      (R := R) (M := Real.sqrt A) (Λ := n * Real.sqrt B)
    · rintro _ ⟨k, rfl⟩
      exact hFn k
    · rintro _ ⟨k, rfl⟩
      filter_upwards [(hfm k).coeFn_toLp] with x hx
      intro hxR
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun ht => hxR (hs k ht))
    · rintro _ ⟨k, rfl⟩
      exact hmod k
  have hcompact : IsCompact (closure (range F)) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨g, _, σ, hσ, hconv⟩ := hcompact.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  refine ⟨g, σ, hσ, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => f (σ k))
    (fun k => hfm (σ k)) g (Lp.memLp g)).mp
  simpa only [Lp.toLp_coeFn, F, Function.comp_def] using hconv

end KLS
end
