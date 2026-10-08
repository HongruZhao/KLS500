import KLS.CompactEnergyInduction
import KLS.SuspensionCumulantTaylorBound

/-! Exact agreement between the adaptive first-slot energy convention and
the final-slot directional cumulant norm used by the suspension argument. -/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace KLS
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantTensor_snoc_eq_cons_of_compact (hμ : IsCompact μ.support)
    (u : Space n) (h : Fin r → Space n) :
    cumulantTensor μ (r+1) (Fin.snoc h u) = cumulantTensor μ (r+1) (Fin.cons u h) := by
  unfold cumulantTensor
  rw [← directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hμ),
    ← directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hμ)]
  have he : List.ofFn (Fin.snoc h u) = List.ofFn h ++ [u] := by
    rw [List.ofFn_succ']
    simp
  rw [he, List.ofFn_cons]
  apply congrFun (directionalWordDerivative_perm (contDiff_tiltLogLaplace hμ) _) 0
  simpa only [List.singleton_append] using
    (List.perm_append_comm : (List.ofFn h ++ [u]).Perm ([u] ++ List.ofFn h))

theorem directionalCumulantSquare_eq_front_of_compact (hμ : IsCompact μ.support) (u : Space n) :
    directionalCumulantSquare μ r u =
      ∑ a : Fin r → Fin n, cumulantTensor μ (r+1)
        (Fin.cons u (fun s => EuclideanSpace.single (a s) (1 : ℝ))) ^ 2 := by
  unfold directionalCumulantSquare
  simp_rw [cumulantTensor_snoc_eq_cons_of_compact hμ, EuclideanSpace.basisFun_apply]

theorem directionalCumulantSquare_le_of_compactBound {B : ℝ}
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hB : CompactCumulantEnergyBound n r B) (u : Space n) :
    directionalCumulantSquare μ r u ≤ B * ‖u‖^2 := by
  rw [directionalCumulantSquare_eq_front_of_compact hμ]
  exact hB μ hμ hadm u

end KLS
end
