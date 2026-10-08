import KLS.ConvexPotentialCoercivity

/-! The actual bounded convex Dirichlet domains used to localize a finite
convex moment-map potential. Their boundary values and compact containment
are proved from finite exponential mass; no regularity of a weak solution
is assumed. -/

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace KLS

variable {n : ℕ}

def potentialSublevel (φ : Space n → ℝ) (R : ℝ) : Set (Space n) := {x | φ x < R}

theorem isOpen_potentialSublevel {φ : Space n → ℝ} (hφ : Continuous φ) (R : ℝ) :
    IsOpen (potentialSublevel φ R) := isOpen_lt hφ continuous_const

theorem convex_potentialSublevel {φ : Space n → ℝ}
    (hc : ConvexOn ℝ univ φ) (R : ℝ) : Convex ℝ (potentialSublevel φ R) := by
  convert! hc.convex_lt R using 1
  ext x
  simp only [potentialSublevel, mem_setOf_eq, mem_univ, true_and]

theorem isCompact_closure_potentialSublevel {φ : Space n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] (R : ℝ) :
    IsCompact (closure (potentialSublevel φ R)) :=
  (isCompact_sublevel_of_finite_potentialMeasure hφ hc R).of_isClosed_subset
    isClosed_closure (closure_lt_subset_le hφ continuous_const)

theorem potential_eq_on_frontier_sublevel {φ : Space n → ℝ}
    (hφ : Continuous φ) (R : ℝ) {x : Space n}
    (hx : x ∈ frontier (potentialSublevel φ R)) : φ x = R :=
  frontier_lt_subset_eq hφ continuous_const hx

theorem potentialSublevel_exhaustion (φ : Space n → ℝ) :
    (⋃ R : ℝ, potentialSublevel φ R) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨φ x + 1, by dsimp [potentialSublevel]; linarith⟩

end KLS
end

#print axioms KLS.isCompact_closure_potentialSublevel
#print axioms KLS.potential_eq_on_frontier_sublevel
