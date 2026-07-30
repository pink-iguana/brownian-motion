module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration

@[expose] public section

namespace ProbabilityTheory

open ProbabilityTheory MeasureTheory Real Filtration Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
variable {ι : Type*} [LinearOrder ι]
variable (Y : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)

/-- A domain is a subset of stochastic processes. -/
abbrev Domain := Set (ι → Ω → ℝ)
/-- An `SIntegral` maps processes to random variables. -/
abbrev SIntegral := (X : ι → Ω → ℝ) → Ω → ℝ

/-- An SIntegral `I` with domain `S` respects elementary processes w.r.t `Y`
if for any `i ≤ j` and every `𝓕 i`-measurable random variable `X`, the elementary process
constructed from `i`, `j`, and `X` lies in `S` and the value of `I` is the
one we would expect. -/
def IntegralElementary (I : SIntegral) (S : Domain) :=
  (α β : ι) → (α ≤ β) → (X : Ω → ℝ) →
  (StronglyMeasurable[𝓕 α] X) →
  (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ∈ S ∧
  ∀ᵐ ω ∂P, I (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ω =
    X ω * (Y β ω - Y α ω)

/-- An SIntegral `I` with domain `S` respects addition if
`S` is closed under addition and `I` commutes with addition. -/
def IntegralAdd (I : SIntegral) (S : Domain) :=
  (X Y : ι → Ω → ℝ) → (X ∈ S) → (Y ∈ S) →
  X + Y ∈ S ∧ ∀ᵐ ω ∂P, I (X + Y) ω = I X ω + I Y ω

/-- An SIntegral `I` with domain `S` respects scalar multiplication if `S` is
closed under scalar multiplication and `I` commutes with scalar multiplication. -/
def IntegralSMul (I : SIntegral) (S : Domain) :=
  (X : ι → Ω → ℝ) → (X ∈ S) → (α : ℝ) →
  α • X ∈ S ∧ ∀ᵐ ω ∂P, I (α • X) ω = α * I X ω

/-- An SIntegral `I` with domain `S` respects indistinguishability
if for every `Y` which is indistinguishable from some `X ∈ S` it holds that
`Y ∈ S` and `I Y = I X` almost surely. -/
def IntegralIndistinguishable (I : SIntegral) (S : Domain) :=
  (X Y : ι → Ω → ℝ) → (X ∈ S) → (∀ᵐ ω ∂P, ∀ i, X i ω = Y i ω) →
  Y ∈ S ∧ ∀ᵐ ω ∂P, I X ω = I Y ω

/-- An SIntegral `I` with domain `S` respects dominated convergence if, for any
sequence of processes `X n ∈ S` which are dominated by some `Y ∈ S` and
converge to some process `Z`, it holds that `Z ∈ S` and `I X n` converges in
probability to `I Z`. -/
def IntegralDCT (I : SIntegral) (S : Domain) :=
  (X : ℕ → ι → Ω → ℝ) → (Y Z : ι → Ω → ℝ) →
  (∀ n, X n ∈ S) → (Y ∈ S) →
  (∀ n i ω, |X n i ω| ≤ |Y i ω|) →
  (∀ i ω, Tendsto (fun n ↦ X n i ω) atTop (𝓝 (Z i ω))) →
  (Z ∈ S) ∧ TendstoInMeasure P (fun n ↦ I (X n)) atTop (I Z)

/-- An SIntegral `I` with domain `S` is an extension of the Riemann-Stieltjes
integral if it respects indistinguishability, addition, scalar multiplication,
dominated converge, and elementary processes.
-/
def IsRiemannStieltjesExtension (I : SIntegral) (S : Domain) :=
  IntegralElementary P Y 𝓕 I S ∧
  IntegralAdd P I S ∧
  IntegralSMul P I S ∧
  IntegralIndistinguishable P I S ∧
  IntegralDCT P I S

/--
A domain `S` is consistent for `Y` if there can exists at most one
extension of the Riemann-Stieltjes integral w.r.t `Y` on `S` (up to a.s. equality).
This condition ensures that `S` is not accidentally 'too large'.
It can be shown that `S` is consistent if any function in `S` can be
approximated pointwise by a sequence of elementary functions in a dominated way.
-/
def IsConsistentDomain (S : Domain) :=
  (I₁ I₂ : SIntegral) →
  IsRiemannStieltjesExtension P Y 𝓕 I₁ S →
  IsRiemannStieltjesExtension P Y 𝓕 I₂ S →
  (X : ι → Ω → ℝ) → (X ∈ S) →
  ∀ᵐ ω ∂P, I₁ X ω = I₂ X ω

/-- A `stochastic integral` against `Y` consists of a pre-integral `I`
and a pre-domain `S`, such that `S` is a consistent domain and `I` is a
Riemann-Stieltjes extension w.r.t `Y`.
-/
structure StochasticIntegral where
  I : SIntegral
  S : Domain
  is_extension : IsRiemannStieltjesExtension P Y 𝓕 I S
  is_consistent : IsConsistentDomain P Y 𝓕 S

end ProbabilityTheory

end
