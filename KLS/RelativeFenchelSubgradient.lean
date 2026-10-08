import KLS.MomentCenteredSections
import KLS.WeakSubgradientTransport

/-!
# Relative support slopes for the actual finite conjugate

The finite conjugate is defined after centering the original potential at
zero and then undoing the additive shift. Thus its finite values are the
ordinary Fenchel values for every additive normalization. Convexity and
support statements are restricted to its genuine finite domain.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Ordinary support-plane slopes relative to a domain, empty outside it. -/
def convexSubgradientOn (u : Space n → ℝ) (D : Set (Space n)) (x : Space n) :
    Set (Space n) :=
  {p | x ∈ D ∧ ∀ y ∈ D, u x + inner ℝ p (y - x) ≤ u y}

def convexSubgradientImageOn (u : Space n → ℝ) (D S : Set (Space n)) : Set (Space n) :=
  {p | ∃ x ∈ S, p ∈ convexSubgradientOn u D x}

theorem convexSubgradientOn_univ (u : Space n → ℝ) (x : Space n) :
    convexSubgradientOn u univ x = convexSubgradient u x := by
  ext p
  simp only [convexSubgradientOn, convexSubgradient, mem_ofPred_eq, mem_univ,
    true_and, forall_const]

theorem mem_momentLegendreDomain_of_affine_upper_bound
    (u : Space n → ℝ) (p : Space n) {M : ℝ}
    (hbound : ∀ x, inner ℝ p x - u x ≤ M) : p ∈ momentLegendreDomain u := by
  have hle : normalizedLegendreTransform u p ≤ ENNReal.ofReal (max M 0) := by
    apply (normalizedLegendreTransform_le_ofReal_iff u p (le_max_right M 0)).mpr
    intro x
    exact (hbound x).trans (le_max_left M 0)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Shifting a potential by any finite constant preserves its true finite
conjugate domain, including when the ENNReal transform clips negative values. -/
theorem momentLegendreDomain_sub_const (u : Space n → ℝ) (c : ℝ) :
    momentLegendreDomain (fun x => u x - c) = momentLegendreDomain u := by
  ext p
  constructor
  · intro hp
    apply mem_momentLegendreDomain_of_affine_upper_bound u p
      (M := (normalizedLegendreTransform (fun x => u x - c) p).toReal - c)
    intro x
    have hh := normalizedLegendreTransform_young (fun x => u x - c) hp x
    linarith
  · intro hp
    apply mem_momentLegendreDomain_of_affine_upper_bound (fun x => u x - c) p
      (M := (normalizedLegendreTransform u p).toReal + c)
    intro x
    have hh := normalizedLegendreTransform_young u hp x
    linarith

/-- The real-valued representative of the actual Fenchel conjugate on its
finite domain. Values outside that domain carry no convexity assertion. -/
def finiteLegendrePotential (u : Space n → ℝ) (p : Space n) : ℝ :=
  (normalizedLegendreTransform (fun x => u x - u 0) p).toReal - u 0

theorem finiteLegendrePotential_young (u : Space n → ℝ)
    {p : Space n} (hp : p ∈ momentLegendreDomain u) (x : Space n) :
    inner ℝ p x ≤ u x + finiteLegendrePotential u p := by
  have hp' : p ∈ momentLegendreDomain (fun x => u x - u 0) := by
    simpa only [momentLegendreDomain_sub_const] using hp
  have hh := normalizedLegendreTransform_young (fun x => u x - u 0) hp' x
  dsimp [finiteLegendrePotential] at *
  linarith

theorem finiteLegendrePotential_eq_of_mem_convexSubgradient
    {u : Space n → ℝ} {x p : Space n} (hp : p ∈ convexSubgradient u x) :
    finiteLegendrePotential u p = inner ℝ p x - u x := by
  have hp' : p ∈ convexSubgradient (fun y => u y - u 0) x := by
    simpa only [convexSubgradient_sub_const] using hp
  have hh := normalizedLegendreTransform_toReal_eq_of_mem_convexSubgradient
    (φ := fun y => u y - u 0) (by simp) hp'
  dsimp [finiteLegendrePotential]
  rw [hh]
  ring

theorem convexOn_finiteLegendrePotential (u : Space n → ℝ) :
    ConvexOn ℝ (momentLegendreDomain u) (finiteLegendrePotential u) := by
  have hh := (convexOn_normalizedLegendreTransform_toReal (fun x => u x - u 0)).add_const (-u 0)
  rw [momentLegendreDomain_sub_const] at hh
  unfold finiteLegendrePotential
  convert! hh using 1

theorem continuousOn_finiteLegendrePotential_interior (u : Space n → ℝ) :
    ContinuousOn (finiteLegendrePotential u) (interior (momentLegendreDomain u)) :=
  (convexOn_finiteLegendrePotential u).continuousOn_interior

/-- The centered construction retains exact Fenchel biconjugation for the
original potential, without a zero-normalization assumption. -/
theorem finiteLegendrePotential_biconjugate_isLUB
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u) (x : Space n) :
    IsLUB (range (fun p : momentLegendreDomain u =>
      inner ℝ p.1 x - finiteLegendrePotential u p.1)) (u x) := by
  constructor
  · rintro z ⟨p, rfl⟩
    have hh := finiteLegendrePotential_young u p.2 x
    linarith
  · intro z hz
    have hc' : ConvexOn ℝ univ (fun y => u y - u 0) := by
      convert! hc.add_const (-u 0) using 1
    have hu' : Continuous (fun y => u y - u 0) := hu.sub continuous_const
    have hLUB := normalizedLegendre_biconjugate_isLUB
      (φ := fun y => u y - u 0) hu' hc' (by simp : u 0 - u 0 = 0) x
    have hbound : u x - u 0 ≤ z - u 0 := by
      apply hLUB.2
      rintro w ⟨p, rfl⟩
      have hp : p.1 ∈ momentLegendreDomain u := by
        simpa only [momentLegendreDomain_sub_const] using p.2
      have hh := hz (mem_range_self (⟨p.1, hp⟩ : momentLegendreDomain u))
      change inner ℝ p.1 x - finiteLegendrePotential u p.1 ≤ z at hh
      dsimp [finiteLegendrePotential] at hh
      change inner ℝ p.1 x - (normalizedLegendreTransform (fun y => u y - u 0) p.1).toReal ≤ z - u 0
      linarith
    linarith

/-- Exact inverse support graph on the genuine finite conjugate domain.
Neither differentiability nor strict convexity is required. -/
theorem mem_convexSubgradientOn_finiteLegendrePotential_iff
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    (p x : Space n) :
    x ∈ convexSubgradientOn (finiteLegendrePotential u) (momentLegendreDomain u) p ↔
      p ∈ convexSubgradient u x := by
  constructor
  · intro hx
    have hbound : u x ≤ inner ℝ p x - finiteLegendrePotential u p := by
      apply (finiteLegendrePotential_biconjugate_isLUB hu hc x).2
      rintro w ⟨q, rfl⟩
      have hh := hx.2 q.1 q.2
      rw [inner_sub_right] at hh
      rw [← real_inner_comm x q.1, ← real_inner_comm x p] at hh
      linarith
    intro y
    have hh := finiteLegendrePotential_young u hx.1 y
    rw [inner_sub_right]
    linarith
  · intro hp
    refine ⟨mem_momentLegendreDomain_of_support_any_normalization hp, ?_⟩
    intro q hq
    rw [finiteLegendrePotential_eq_of_mem_convexSubgradient hp, inner_sub_right]
    rw [← real_inner_comm x q, ← real_inner_comm x p]
    have hh := finiteLegendrePotential_young u hq x
    linarith

end KLS
end

#print axioms KLS.momentLegendreDomain_sub_const
#print axioms KLS.finiteLegendrePotential_eq_of_mem_convexSubgradient
#print axioms KLS.convexOn_finiteLegendrePotential
#print axioms KLS.finiteLegendrePotential_biconjugate_isLUB
#print axioms KLS.mem_convexSubgradientOn_finiteLegendrePotential_iff
