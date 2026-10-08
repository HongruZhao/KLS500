import OptPositiveSquareGap
import KLS.FiniteIsometryAverageAlgebra

/-! Finite orbit spans transfer a finite-dimensional spectral gap to arbitrary
real inner product spaces, including Hilbert spaces of L2 functions. -/
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : Type*} [Group G] [Fintype G]

def finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun g : G => ρ g x)

instance finiteDimensional_finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    FiniteDimensional ℝ (finiteOrbitSpan ρ x) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range fun g : G => ρ g x)

omit [Fintype G] in
theorem action_mem_finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G) :
    ρ g x ∈ finiteOrbitSpan ρ x := Submodule.subset_span ⟨g, rfl⟩

omit [Fintype G] in
theorem self_mem_finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    x ∈ finiteOrbitSpan ρ x := by
  simpa using action_mem_finiteOrbitSpan ρ x 1

theorem finiteAverage_mem_finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    finiteIsometryAverage ρ x ∈ finiteOrbitSpan ρ x := by
  unfold finiteIsometryAverage
  apply Submodule.smul_mem
  exact Submodule.sum_mem _ fun g _ => action_mem_finiteOrbitSpan ρ x g

omit [Fintype G] in
theorem action_preserves_finiteOrbitSpan (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G)
    {y : E} (hy : y ∈ finiteOrbitSpan ρ x) : ρ g y ∈ finiteOrbitSpan ρ x := by
  change y ∈ Submodule.span ℝ (Set.range fun h : G => ρ h x) at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨h, rfl⟩
    apply Submodule.subset_span
    refine ⟨g*h, ?_⟩
    change ρ (g*h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl
  | zero => simpa only [map_zero] using (finiteOrbitSpan ρ x).zero_mem
  | add y z hy hz ihy ihz =>
    simpa only [map_add] using (finiteOrbitSpan ρ x).add_mem ihy ihz
  | smul a y hy ih =>
    simpa only [map_smul] using (finiteOrbitSpan ρ x).smul_mem a ih

theorem inner_sub_finiteAverage_fixed_eq_zero (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (x z : E) (hz : ∀ g, ρ g z = z) :
    inner ℝ (x - finiteIsometryAverage ρ x) z = 0 := by
  have hpair (g : G) : inner ℝ (ρ g x) z = inner ℝ x z := by
    have hh := (ρ g).inner_map_map x z
    rw [hz] at hh
    exact hh
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have havg : inner ℝ (finiteIsometryAverage ρ x) z = inner ℝ x z := by
    unfold finiteIsometryAverage
    rw [inner_smul_left, sum_inner]
    simp only [conj_trivial, hpair, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [inner_sub_left, havg, sub_self]

/-- Only the span of the finite orbit of `x` is diagonalized. The ambient space
is unrestricted in dimension, and completeness is not needed. -/
theorem finite_action_gap_of_positive_square
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (c : ℝ)
    (hpos : ∀ z, 0 ≤ inner ℝ z (A z))
    (hsquare : ∀ z, c * inner ℝ z (A z) ≤ ‖A z‖^2)
    (hstable : ∀ x z, z ∈ finiteOrbitSpan ρ x → A z ∈ finiteOrbitSpan ρ x)
    (hkill : ∀ x, A (finiteIsometryAverage ρ x) = 0)
    (hker : ∀ z, A z = 0 → z = finiteIsometryAverage ρ z)
    (x : E) : c * ‖x - finiteIsometryAverage ρ x‖^2 ≤ inner ℝ x (A x) := by
  have hx : x - finiteIsometryAverage ρ x ∈ finiteOrbitSpan ρ x :=
    (finiteOrbitSpan ρ x).sub_mem (self_mem_finiteOrbitSpan ρ x)
      (finiteAverage_mem_finiteOrbitSpan ρ x)
  have horth (z : E) (_hz : z ∈ finiteOrbitSpan ρ x) (hAz : A z = 0) :
      inner ℝ (x - finiteIsometryAverage ρ x) z = 0 := by
    apply inner_sub_finiteAverage_fixed_eq_zero ρ x z
    intro g
    have hz := hker z hAz
    calc
      ρ g z = ρ g (finiteIsometryAverage ρ z) := congrArg (ρ g) hz
      _ = finiteIsometryAverage ρ z := finiteIsometryAverage_fixed ρ z g
      _ = z := hz.symm
  have hg := positive_symmetric_gap_on_finite_subspace A hA c hpos hsquare
    (finiteOrbitSpan ρ x) (hstable x) (x - finiteIsometryAverage ρ x) hx horth
  have he : inner ℝ (x - finiteIsometryAverage ρ x) (A (x - finiteIsometryAverage ρ x)) =
      inner ℝ x (A x) := by
    rw [map_sub, hkill, sub_zero, inner_sub_left, ← hA (finiteIsometryAverage ρ x) x,
      hkill, inner_zero_left, sub_zero]
  rwa [he] at hg

end KLS.ConstantReduction
end
