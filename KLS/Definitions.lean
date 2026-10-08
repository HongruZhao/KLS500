import Mathlib

/-!
# Audited KLS definitions and a new Poincaré companion

`Space` through `KLSConjecture` below preserve the declaration bodies from
`brando90/conjecture-prover`, commit
`715c22ee0b55076591f60b76701cc9428e1b55a4`, `proofs/job_45/Job_45.lean`.
Their presence is a statement of the conjecture, not a proof.

The remainder is new local formalization. `admissibleMeasure` uses compact-set
log-concavity and is deliberately distinct from the original density-based
`IsKLSMeasure`. No density/measure equivalence is assumed or asserted here.
The full-class endpoint must supply that analytic bridge before transferring a
result between the classes.

Energy and variance are extended nonnegative integrals. The constant predicate
requires local Lipschitz regularity and L² integrability. Real variance formulas
may only be used after this integrability has been established.
-/

open scoped Topology ENNReal NNReal BigOperators
open MeasureTheory Set Filter Metric

noncomputable section

namespace KLS

/-- The ambient Euclidean space `ℝⁿ`. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The convention `exp(-t) = 0` at `t = ⊤`, for a potential taking values in
`(-∞, ∞]`, encoded as `WithTop ℝ`. Note that `WithTop ℝ = ℝ ∪ {+∞}`
faithfully captures the codomain `(-∞, ∞]`, since the potential `V` is not
permitted to take the value `-∞`. -/
def expNegPotential : WithTop ℝ → ℝ≥0∞
  | ⊤ => 0
  | (r : ℝ) => ENNReal.ofReal (Real.exp (-r))

/-- Convexity of an extended-real-valued potential `V : ℝⁿ → (-∞, ∞]`,
encoded by convexity of its (weak) epigraph as a subset of `ℝⁿ × ℝ`.
A point `(x, t)` with `t : ℝ` lies in the epigraph iff `V x ≤ (t : WithTop ℝ)`;
this correctly captures convexity of an extended-real-valued function because
every `t ∈ ℝ` is below `⊤`, so a point where `V = ⊤` is never in the epigraph,
while a finite `V x` admits all `t ≥ V x`. -/
def ExtendedConvex {n : ℕ} (V : Space n → WithTop ℝ) : Prop :=
  Convex ℝ {p : Space n × ℝ | V p.1 ≤ (p.2 : WithTop ℝ)}

/-- A measure has a *log-concave density* `f = exp(-V)` with respect to
Lebesgue measure on `ℝⁿ`, where `V : ℝⁿ → (-∞, ∞]` is convex. The code
requires measurability of the density `expNegPotential ∘ V`, exactly the
property needed for the density representation. The declaration body is the
original Job 45 body; this comment makes its actual hypothesis explicit. -/
def HasLogConcaveDensity {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∃ V : Space n → WithTop ℝ,
    ExtendedConvex V ∧
      Measurable (fun x => expNegPotential (V x)) ∧
        μ = (volume : Measure (Space n)).withDensity (fun x => expNegPotential (V x))

/-- Absolute continuity with respect to Lebesgue measure on `ℝⁿ`. (This is
implied by `HasLogConcaveDensity` since `withDensity` measures are
absolutely continuous, but we keep it as a separate predicate for the
faithful statement of the KLS hypotheses.) -/
def AbsolutelyContinuousLebesgue {n : ℕ} (μ : Measure (Space n)) : Prop :=
  μ ≪ (volume : Measure (Space n))

/-- The second-moment matrix `(∫ xᵢ xⱼ dμ)ᵢⱼ`. -/
def secondMomentMatrix {n : ℕ} (μ : Measure (Space n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, x i * x j ∂μ

/-- Isotropy: `μ` has zero mean and identity second-moment matrix.
Together with zero mean, this is the covariance identity `∫ xxᵀ dμ = Iₙ`. -/
def IsIsotropic {n : ℕ} (μ : Measure (Space n)) : Prop :=
  Integrable (fun x : Space n => x) μ ∧
    (∫ x, x ∂μ) = 0 ∧
      (∀ i j : Fin n, Integrable (fun x : Space n => x i * x j) μ) ∧
        secondMomentMatrix μ = (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The closed `ε`-enlargement `Aε = {x : dist(x, A) ≤ ε}`, given by
Mathlib's `Metric.cthickening`. -/
def enlargement {n : ℕ} (A : Set (Space n)) (ε : ℝ) : Set (Space n) :=
  Metric.cthickening ε A

/-- The Minkowski boundary measure
`μ⁺(A) = liminf_{ε ↓ 0⁺} (μ(Aε) - μ(A)) / ε`. The subtraction is taken in
`ℝ≥0∞` (truncated subtraction); since `A ⊆ Aε`, this coincides with the
genuine difference `μ(Aε) - μ(A)`. -/
def boundaryMeasure {n : ℕ} (μ : Measure (Space n)) (A : Set (Space n)) : ℝ≥0∞ :=
  Filter.liminf
    (fun ε : ℝ => (μ (enlargement A ε) - μ A) / ENNReal.ofReal ε)
    (𝓝[>] (0 : ℝ))

/-- The Cheeger (isoperimetric) constant
`ψ_μ = inf_A μ⁺(A) / min(μ(A), 1 - μ(A))`, the infimum being over measurable
sets `A` with `0 < μ(A) < 1`. For a probability measure, `1 - μ A = μ Aᶜ`. -/
def cheegerConstant {n : ℕ} (μ : Measure (Space n)) : ℝ≥0∞ :=
  ⨅ A : {A : Set (Space n) // MeasurableSet A ∧ 0 < μ A ∧ μ A < 1},
    boundaryMeasure μ A.1 / min (μ A.1) (1 - μ A.1)

/-- The class of measures considered by the KLS conjecture: Borel
probability measures on `ℝⁿ`, absolutely continuous w.r.t. Lebesgue
measure, with log-concave density of the form `e^{-V}` (`V` convex), and
isotropic. -/
structure IsKLSMeasure {n : ℕ} (μ : Measure (Space n)) : Prop where
  isProb : IsProbabilityMeasure μ
  absCont : AbsolutelyContinuousLebesgue μ
  logConcave : HasLogConcaveDensity μ
  isotropic : IsIsotropic μ

/-- **The Kannan–Lovász–Simonovits conjecture (Kannan–Lovász–Simonovits, 1995).**
There exists a universal constant `c > 0`, independent of `n` and of `μ`,
such that for every dimension `n ≥ 1` and every isotropic log-concave
probability measure `μ` on `ℝⁿ`, the Cheeger constant satisfies
`ψ_μ ≥ c`. -/
def KLSConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 1 ≤ n →
      ∀ μ : Measure (Space n),
        IsKLSMeasure μ → ENNReal.ofReal c ≤ cheegerConstant μ

/-- Compact-set Minkowski interpolation. Compact inputs have compact, hence
Borel measurable, output in `Space n`. -/
def affineSetCombination {n : ℕ} (t : ℝ) (E F : Set (Space n)) : Set (Space n) :=
  (fun p : Space n × Space n => t • p.1 + (1 - t) • p.2) '' (E ×ˢ F)

/-- Log-concavity of a measure in the compact-set formulation required by the
full KLS target. Both interpolation weights are strictly positive. -/
def measureLogConcave {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∀ E F : Set (Space n), IsCompact E → IsCompact F →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ E) ^ t * (μ F) ^ (1 - t) ≤ μ (affineSetCombination t E F)

/-- The full measure-based admissible class. The Euclidean measurable space is
Borel, and the original isotropy predicate explicitly includes the necessary
first and second moment integrability. Absolute continuity is a theorem to be
proved from these hypotheses, not an additional restriction on this class. -/
structure admissibleMeasure {n : ℕ} (μ : Measure (Space n)) : Prop where
  isProb : IsProbabilityMeasure μ
  logConcave : measureLogConcave μ
  isotropic : IsIsotropic μ

/-- Locally Lipschitz real-valued L² test functions. -/
def LocallyLipschitzTests {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : Prop :=
  LocallyLipschitz f ∧ MemLp f 2 μ

/-- Extended Dirichlet energy. The library gradient uses the Riesz
identification of the Fréchet derivative and defaults to zero at points of
nondifferentiability. Its almost-everywhere interpretation therefore requires
Rademacher's theorem and absolute continuity, proved in separate modules.
The nonnegative integral retains infinite energy as `⊤`. -/
def energy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ

/-- Extended variance from mathlib. Finiteness is equivalent to L² membership
for measurable functions under a finite measure. In Poincaré tests below the
L² hypothesis is explicit, so the usual variance formula is available. -/
def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ≥0∞ :=
  ProbabilityTheory.evariance f μ

/-- The finite nonnegative Poincaré constants, with all locally Lipschitz L²
functions tested and infinite Dirichlet energy allowed. -/
def poincareConstants {n : ℕ} (μ : Measure (Space n)) : Set ℝ≥0 :=
  {C | ∀ f : Space n → ℝ, LocallyLipschitzTests μ f →
    variance μ f ≤ (C : ℝ≥0∞) * energy μ f}

/-- The optimal Poincaré constant as an extended nonnegative infimum of the
finite admissible constants. In particular an empty admissible set gives `⊤`.
Admissibility of this infimum is a further theorem, not part of the definition. -/
def poincareConstant {n : ℕ} (μ : Measure (Space n)) : ℝ≥0∞ :=
  sInf ((fun C : ℝ≥0 => (C : ℝ≥0∞)) '' poincareConstants μ)

/-- The optimal universal Poincaré constant over every positive dimension and
every member of the full measure-based class. Finiteness, admissibility, and
an exact numerical value are separate proof obligations. -/
def universalPoincareConstant : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : 1 ≤ n) (μ : Measure (Space n)) (_ : admissibleMeasure μ),
    poincareConstant μ

end KLS

end
