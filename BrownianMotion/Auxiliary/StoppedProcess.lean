module

public import BrownianMotion.Auxiliary.Indistinguishable
public import Mathlib.Probability.Process.Stopping

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X Y : ι → Ω → E}

section stoppedProcess

variable [LinearOrder ι]

@[simp]
lemma stoppedProcess_of_eq_top (s : ι) (hτ : τ ω = ⊤) :
    stoppedProcess X τ s ω = X s ω := by
  simp [stoppedProcess, hτ]

@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]

lemma stoppedProcess_congr (h : X ≡ᵐ[P] Y) :
    stoppedProcess X τ ≡ᵐ[P] stoppedProcess Y τ := by
  filter_upwards [h] with ω h t
  simp [stoppedProcess, h]

end stoppedProcess

namespace stoppedValue

@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl

@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl

@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl

end stoppedValue

end MeasureTheory
