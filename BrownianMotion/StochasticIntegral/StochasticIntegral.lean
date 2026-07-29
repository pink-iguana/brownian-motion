module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.BrownianMotion.Basic
public import BrownianMotion.Gaussian.BrownianMotion

open ProbabilityTheory MeasureTheory Real Filtration Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
variable {ι : Type*} [LinearOrder ι]
variable (Y : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)

/-- A `domain` is a subset of stochastic processes. -/
abbrev PreDomain := Set (ι → Ω → ℝ)
/-- A `pre-integral` maps processes to random variables. -/
abbrev PreIntegral := (X : ι → Ω → ℝ) → Ω → ℝ

--- We now write down some properties which any reasonable stochastic integral
--- should satisfy.

/-- A pre-integral `I` with domain `S` respects elementary processes
if ...
-/
def IntegralElementary (I : PreIntegral) (S : PreDomain) :=
    (α β : ι) → (α ≤ β) → (X : Ω → ℝ) →
    (StronglyMeasurable[𝓕 α] X) →
    (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ∈ S ∧
    ∀ᵐ ω ∂P, I (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ω =
      X ω * (Y β ω - Y α ω)

/-- A pre-integral `I` with domain `S` respects addition if
`S` is closed under addition and `I` commutes with addition. -/
def IntegralAdd (I : PreIntegral) (S : PreDomain) :=
    (X : ι → Ω → ℝ) → (Y : ι → Ω → ℝ) →
    (X ∈ S) → (Y ∈ S) →
    X + Y ∈ S ∧ ∀ᵐ ω ∂P, I (X + Y) ω = I X ω + I Y ω

/-- A pre-integral `I` with domain `S` respects scalar multiplication if `S` is
closed under scalar multiplication and `I` commutes with scalar multiplication. -/
def IntegralSMul (I : PreIntegral) (S : PreDomain) :=
    (α : ℝ) → (X : ι → Ω → ℝ) → (X ∈ S) →
    α • X ∈ S ∧ ∀ᵐ ω ∂P, I (α • X) ω = α * I X ω

/-- A pre-integral `I` with domain `S` respects indistinguishability
if for every `Y` which is indistinguishable from some `X ∈ S` it holds that
`Y ∈ S` and `I Y = I X` almost surely. -/
def IntegralIndistinguishable (I : PreIntegral) (S : PreDomain) :=
    (X Y : ι → Ω → ℝ) →
    (h₁ : X ∈ S) →
    (h₂ : ∀ᵐ ω ∂P, ∀ i, X i ω = X i ω) →
    Y ∈ S ∧ ∀ᵐ ω ∂P, I X ω = I Y ω

/-- A pre-integral `I` with domain `S` respects dominated convergence if, for any
sequence of processes `X n ∈ S` which are pointwise dominated by some `Y ∈ S` and
converge pointwise to some process `Z`, it holds that `Z ∈ S` and
`I X n` converges in probability to `I Z`. -/
def IntegralDCT (I : PreIntegral) (S : PreDomain) :=
    (X : ℕ → ι → Ω → ℝ) → (Y Z : ι → Ω → ℝ) →
    (∀ n, X n ∈ S) → (Y ∈ S) →
    (∀ n i ω, |X n i ω| ≤ |Y i ω|) →
    (∀ i ω, Tendsto (fun n ↦ X n i ω) atTop (𝓝 (Z i ω))) →
    (Z ∈ S) ∧ TendstoInMeasure P (fun n ↦ I (X n)) atTop (I Z)

/--
A pre-integral `I` with domain `S` is a stochastic integral if it
respects indistinguishability, addition, scalar multiplication, dominated
converge, and elementary processes.
-/
def IsStochasticIntegral (I : PreIntegral) (S : PreDomain) :=
    IntegralElementary P Y 𝓕 I S ∧
    IntegralAdd P I S ∧
    IntegralSMul P I S ∧
    IntegralIndistinguishable P I S ∧
    IntegralDCT P I S

/--
A pre-domain `S` is consistent for `Y` if any two stochastic integrals for `Y`
with domain `S` must necessarily agree. Using `IntegralDCT` it can be shown that
this condition holds if every `X ∈ S` can be approximated pointwise by a sequence
of elementary processes which are dominated by some element of `S`.
-/
def IsConsistentDomain (S : PreDomain) :=
    (I₁ I₂ : PreIntegral) →
    IsStochasticIntegral P Y 𝓕 I₁ S →
    IsStochasticIntegral P Y 𝓕 I₂ S →
    (X : ι → Ω → ℝ) → (X ∈ S) →
    ∀ᵐ ω ∂P, I₁ X ω = I₂ X ω

def CMSpace (B : NNReal → Ω → ℝ) (hB : IsBrownianReal B P) :=
    {X : NNReal → Ω → ℝ | IsStronglyPredictable (m := mΩ) (natural B sorry) X}

theorem exists_sintegral (B : NNReal → Ω → ℝ) (𝓕 : Filtration NNReal mΩ)
    (hB : IsBrownianReal B P) (hB₂ : IsFilteredPreBrownian B 𝓕 P) :
    ∃ I : PreIntegral, ∃ S : PreDomain,
    IsStochasticIntegral P B 𝓕 I S ∧ IsConsistentDomain P B 𝓕 S :=
  sorry
