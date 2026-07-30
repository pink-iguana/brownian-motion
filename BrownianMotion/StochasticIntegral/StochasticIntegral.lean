/-
Copyright (c) 2025 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration

/-!
# Characterization of the stochastic integral.

This file contains an axiomatic characterization of the stochastic integral
against a process `Y : ι → Ω → ℝ`. Ideally, any reasonable definition of a
stochastic integral should satisfy the following properties, packaged together
into the definition `IsRiemannStieltjesExtension`.

* `IntegralElementary`: the integral agrees with the Riemann-Stieltjes integral
  on a very elementary set of processes.
* `IntegralAdd`, `IntegralMul`: the integral should be linear.
* `IntegralDCT`: if `X` is integrable, the the pointwise limit of any sequence
of integrable processes which is dominated by `X` should again be integrable, and
in this case the integral should commute with the limit.
* `IntegralIndistinguishable`: a process which is indistinguishable from an integrable
process should be integrable.

In order to prevent nonuniqueness, we additionally impose a condition on the domain:
* `IsConsistent`: the stochastic integral `I` should be canonical, i.e., any other Riemann-Stieltjes
extension satisfying the above axioms should agree with `I` on the intersection of their domains.
In practice, `IsConsistentDomain` can be shown whenever every element in `S` can be
pointwise approximated by simple processes in a dominated way (in this case, uniqueness
is easily shown using `IntegralDCT`).

A `stochastic integral` is then given by the structure `StochasticIntegral`,
guaranteeing that it satisfies all the above properties.

Note that none of the definitions impose that the domain `S` should be maximal.
As a consequence, it is possible to define different stochastic integrals w.r.t `Y`.
However, any two such integrals will necessarily agree (almost surely)
on the intersection of their domains.
-/

@[expose] public section

namespace ProbabilityTheory

open ProbabilityTheory MeasureTheory Real Filtration Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
variable {ι : Type*} [LinearOrder ι] [OrderBot ι]
variable (Y : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ)

/-- A domain is a subset of stochastic processes. -/
abbrev Domain := Set (ι → Ω → ℝ)
/-- An `SIntegral` maps processes to random variables. -/
abbrev SIntegral := (X : ι → Ω → ℝ) → Ω → ℝ

/-- An SIntegral `I` with domain `S` respects elementary processes w.r.t `Y`
if for any `i ≤ j` and every `𝓕 i`-measurable random variable `X`, the elementary process
constructed from `i`, `j`, and `X` lies in `S` and the value of `I` is the
one we would expect. -/
def IntegralElementary₁ (I : SIntegral) (S : Domain) :=
  (α β : ι) → (α ≤ β) → (X : Ω → ℝ) →
  (StronglyMeasurable[𝓕 α] X) →
  (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ∈ S ∧
  ∀ᵐ ω ∂P, I (fun i ω ↦ if (i ∈ Set.Ioc α β) then X ω else 0) ω =
    X ω * (Y β ω - Y α ω)

/-- An SIntegral `I` with domain `S` respects elementary processes w.r.t `Y`
if for any `i ≤ j` and every `𝓕 i`-measurable random variable `X`, the elementary process
constructed from `i`, `j`, and `X` lies in `S` and the value of `I` is the
one we would expect. -/
def IntegralElementary₂ (I : SIntegral) (S : Domain) :=
  (α : ι) → (X : Ω → ℝ) → (StronglyMeasurable[𝓕 ⊥] X) →
  (fun i ω ↦ if (i ∈ Set.Iic α) then X ω else 0) ∈ S ∧
  ∀ᵐ ω ∂P, I (fun i ω ↦ if (i ∈ Set.Iic α) then X ω else 0) ω =
    X ω * Y α ω - X ω * Y ⊥ ω

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
  ∀ X ∈ S, AEStronglyMeasurable (I X) P ∧
  IntegralElementary₁ P Y 𝓕 I S ∧
  IntegralElementary₂ P Y 𝓕 I S ∧
  IntegralAdd P I S ∧
  IntegralSMul P I S ∧
  IntegralIndistinguishable P I S ∧
  IntegralDCT P I S

/--
An SIntegral `I` with domain `S` is *consistent* if any Riemann-Stieltjes extension
with domain `S'` must almost surely agree with `I` on `S ∩ S'`.
This condition ensures that `S` is not accidentally 'too large'.
-/
def IsConsistent (I : SIntegral) (S : Domain) :=
  (I' : SIntegral) → (S' : Domain) →
  IsRiemannStieltjesExtension P Y 𝓕 I' S' →
  (X : ι → Ω → ℝ) → (X ∈ S ∩ S') →
  ∀ᵐ ω ∂P, I X ω = I' X ω

/-- A `stochastic integral` against `Y` consists of a pre-integral `I`
and a pre-domain `S`, such that `S` is a consistent domain and `I` is a
Riemann-Stieltjes extension w.r.t `Y`.
-/
structure StochasticIntegral where
  I : SIntegral
  S : Domain
  is_extension : IsRiemannStieltjesExtension P Y 𝓕 I S
  is_consistent : IsConsistent P Y 𝓕 I S

end ProbabilityTheory

end
