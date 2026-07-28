/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.EVariationOn
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The variation process

## Main definitions

* `variationProcess`: the pathwise variation of `X` from a starting time `a`, as a process.

## Main results

* `variationProcess_nonneg`: for `a ≤ t` the variation process is nonnegative.
* `monotone_variationProcess`: the variation process of a path of locally bounded variation is
  monotone in time.
* `MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous`,
  `..._of_continuousWithinAt_Ioi` and `..._of_continuousWithinAt_Iio`: for `a ≤ t`, the value at
  time `t` of the variation process of a strongly adapted process is `𝓕 t`-measurable, assuming
  continuous, right-continuous and left-continuous paths respectively. The continuous case assumes
  separability of the time index, the two others second countability; see
  `BrownianMotion.Auxiliary.EVariationOn` for a discussion of these assumptions, and for the
  results about the variation of a function that these proofs rely on.

-/

@[expose] public section

open MeasureTheory Set TopologicalSpace

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω}

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation process of `X` from the starting time `a`. -/
noncomputable def variationProcess (X : ι → Ω → E) (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) univ a t

/-- For `a ≤ t`, the variation process at time `t` is the total variation of the path on `Icc a t`,
converted to a real number. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (X : ι → Ω → E) {a t : ι} (hat : a ≤ t)
    (ω : Ω) : variationProcess X a t ω = (eVariationOn (X · ω) (Icc a t)).toReal := by
  simp [variationProcess, variationOnFromTo, hat]

/-- For `a ≤ t` the variation process is nonnegative. It can be negative for `t < a`, where it
takes the signed value `-(eVariationOn (X · ω) (Icc t a)).toReal`. -/
theorem variationProcess_nonneg (X : ι → Ω → E) {a t : ι} (hat : a ≤ t) (ω : Ω) :
    0 ≤ variationProcess X a t ω :=
  variationOnFromTo.nonneg_of_le _ _ hat

/-- The variation process of a path of locally bounded variation is monotone in time. Monotonicity
holds on all of `ι`, not just above the starting time `a`, since the variation is signed. -/
theorem monotone_variationProcess {X : ι → Ω → E} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) univ) (a : ι) :
    Monotone fun t ↦ variationProcess X a t ω :=
  fun _ _ hst ↦ variationOnFromTo.monotoneOn hX (mem_univ a) (mem_univ _) (mem_univ _) hst

section Measurability

variable [TopologicalSpace ι]

section Separable

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuous [OrderTopology ι]
    [SeparableSpace ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) {a t : ι} (hcont : ∀ ω, ContinuousOn (X · ω) (Ici a))
    (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω ↦ (hcont ω).mono Icc_subset_Ici_self

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with continuous paths is adapted. -/
theorem MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuous [OrderTopology ι]
    [OrderBot ι] [SeparableSpace ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, Continuous (X · ω)) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuous (by simpa) bot_le

end Separable

section SecondCountableTopology

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
right-continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Ioi
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Ioi i) i)
    {a t : ι} (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Ioi
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with right-continuous paths is adapted. -/
theorem MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuousWithinAt_Ioi
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Ioi i) i) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuousWithinAt_Ioi hcont bot_le

/-- For `a ≤ t`, the value at time `t` of the variation process of a strongly adapted process with
left-continuous paths is `𝓕 t`-measurable. -/
theorem MeasureTheory.StronglyAdapted.measurable_variationProcess_of_continuousWithinAt_Iio
    [OrderTopology ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Iio i) i)
    {a t : ι} (hat : a ≤ t) : Measurable[𝓕 t] (variationProcess X a t) := by
  rw [funext fun ω ↦ variationProcess_eq_toReal_eVariationOn_Icc X hat ω]
  exact Measurable.ennreal_toReal <| measurable_eVariationOn_of_continuousWithinAt_Iio
    (fun i hi ↦ (hX i).mono (𝓕.mono hi.2)) fun ω i _ ↦ (hcont ω i).mono inter_subset_right

/-- If the index set has a bottom element, then the variation process of a strongly adapted process
with right-continuous paths is adapted. -/
theorem MeasureTheory.StronglyAdapted.adapted_variationProcess_of_continuousWithinAt_Iio
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hcont : ∀ ω, ∀ i, ContinuousWithinAt (X · ω) (Iio i) i) :
    Adapted 𝓕 (variationProcess X ⊥) :=
  fun _ => hX.measurable_variationProcess_of_continuousWithinAt_Iio hcont bot_le

end SecondCountableTopology

end Measurability
