/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.AEEq
public import BrownianMotion.Auxiliary.Indistinguishable
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.Auxiliary.StoppedProcess
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import Mathlib.Probability.Notation

import BrownianMotion.Auxiliary.Analysis
import BrownianMotion.Auxiliary.LimitProcess
import BrownianMotion.Auxiliary.MeanInequalities
import BrownianMotion.Auxiliary.MeasureTheory
import BrownianMotion.Gaussian.StochasticProcesses
import BrownianMotion.StochasticIntegral.ClassD
import BrownianMotion.StochasticIntegral.DoobLp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Average

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace AEEqProcess
open scoped ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y Z : ι → Ω → E} {𝓕 : Filtration ι mΩ} {τ : Ω → WithTop ι}

section IsSquareIntegrable

/-! ### Predicates `IsSquareIntegrable` and `IsAESquareIntegrable` -/

variable [NormedSpace ℝ E]

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

lemma IsSquareIntegrable.isRightContinuous (hX : IsSquareIntegrable X 𝓕 P) (ω : Ω) :
    IsRightContinuous (X · ω) := (hX.cadlag ω).right_continuous

lemma IsSquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsSquareIntegrable (fun _ _ ↦ c) 𝓕 P where
  martingale := martingale_const 𝓕 P c
  cadlag ω := isCadlag_const c
  bounded := by
    obtain _ | _ := isEmpty_or_nonempty ι
    · simp
    obtain rfl | hP := eq_or_ne P 0
    · simp
    rw [iSup_const, eLpNorm_const c (by simp) hP]
    finiteness

lemma IsSquareIntegrable.uniformIntegrable [IsFiniteMeasure P] [CompleteSpace E]
    (hX : IsSquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P :=
  uniformIntegrable_of_eLpNorm_le 2 (by simp) (⨆ t, eLpNorm (X t) 2 P)
    hX.bounded.ne (le_iSup _)

/-- An a.e.-square integrable martingale is a process that is indistinguishable from a
square integrable martingale, see `IsSquareIntegrable`. -/
def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y

lemma IsSquareIntegrable.stronglyMeasurable_stoppedValue' [Nonempty ι]
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ P) := by
  borelize ι
  exact 𝓕.stronglyMeasurable_stoppedValue'
    (hX.martingale.stronglyAdapted.isStronglyProgressive_of_rightContinuous
      (fun ω ↦ (hX.cadlag ω).right_continuous)) (fun ω ↦ (hX.cadlag ω).right_continuous) hτ

lemma IsAESquareIntegrable.aestronglyMeasurable_stoppedValue' [MeasurableSpace ι] [Nonempty ι]
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] [BorelSpace ι]
    (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    AEStronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ P) P :=
  ⟨𝓕.stoppedValue' hX.choose τ P, hX.choose_spec.1.stronglyMeasurable_stoppedValue' hτ,
    𝓕.stoppedValue'_congr hX.choose_spec.2⟩

lemma IsAESquareIntegrable.uniformIntegrable [IsFiniteMeasure P] [CompleteSpace E]
    (hX : IsAESquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P :=
  hX.choose_spec.1.uniformIntegrable.ae_eq (fun t ↦ (hX.choose_spec.2.ae_eq_eval t).symm)

lemma IsAESquareIntegrable.aestronglyAdapted (hX : IsAESquareIntegrable X 𝓕 P) :
    AEStronglyAdapted X 𝓕 P :=
  hX.choose_spec.1.martingale.stronglyAdapted.aestronglyAdapted.congr hX.choose_spec.2.symm

lemma IsSquareIntegrable.isAESquareIntegrable (hX : IsSquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable X 𝓕 P := ⟨X, hX, by rfl⟩

lemma IsAESquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsAESquareIntegrable (fun _ _ ↦ c) 𝓕 P :=
  IsSquareIntegrable.const.isAESquareIntegrable

lemma IsAESquareIntegrable.congr {X Y : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P)
    (hXY : X ≡ᵐ[P] Y) : IsAESquareIntegrable Y 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  exact ⟨Z, hZ1, hXY.symm.trans hZ2⟩

lemma isAESquareIntegrable_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    IsAESquareIntegrable X 𝓕 P ↔ IsAESquareIntegrable Y 𝓕 P where
  mp h := h.congr hXY
  mpr h := h.congr hXY.symm

lemma IsSquareIntegrable.memLp_two (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    MemLp (X i) 2 P := by
  refine ⟨(hX.martingale.stronglyMeasurable i).aestronglyMeasurable.mono (𝓕.le i), ?_⟩
  grw [le_iSup (fun t ↦ eLpNorm (X t) 2 P)]
  exact hX.bounded

lemma IsSquareIntegrable.integrable_sq (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P := by
  constructor
  · have hX_meas := (hX.martingale.stronglyAdapted i).mono (𝓕.le i)
    fun_prop
  · have hX_bound : eLpNorm (X i) 2 P < ∞ := by
      calc eLpNorm (X i) 2 P
      _ ≤ ⨆ j, eLpNorm (X j) 2 P := le_iSup (fun j ↦ eLpNorm (X j) 2 P) i
      _ < ∞ := hX.bounded
    simpa [HasFiniteIntegral, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top] using hX_bound

@[to_fun]
lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X + Y) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.cadlag ω).add (hY.cadlag ω), ?_⟩
  have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
  have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
  calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
      ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
        refine iSup_mono fun i ↦ ?_
        exact eLpNorm_add_le
          ((hX.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable
          ((hY.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
    _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
        refine iSup_le fun i => ?_
        gcongr
        · exact le_iSup (fun i => eLpNorm (X i) 2 P) i
        · exact le_iSup (fun i => eLpNorm (Y i) 2 P) i
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩

@[to_fun]
lemma IsAESquareIntegrable.add [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X + Y) 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  obtain ⟨T, hT1, hT2⟩ := hY
  exact ⟨Z + T, hZ1.add hT1, hZ2.add hT2⟩

@[to_fun]
lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (r • X) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := hX.cadlag ω |>.const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

@[to_fun]
lemma IsAESquareIntegrable.smul [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) (r : ℝ) :
    IsAESquareIntegrable (r • X) 𝓕 P := by
  obtain ⟨Y, hY1, hY2⟩ := hX
  exact ⟨r • Y, hY1.smul r, hY2.const_smul⟩

@[to_fun]
lemma IsSquareIntegrable.neg [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsAESquareIntegrable.neg [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsSquareIntegrable.sub [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

@[to_fun]
lemma IsAESquareIntegrable.sub [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

open scoped Classical in
/-- If `hX : IsAESquareIntegrable X 𝓕 P` and `∀ᵐ ω ∂P, Continuous (X · ω)`, then
`hX.toContinuous X` is continuous everywhere, satisfies `IsSquareIntegrable` and
is indistinguishable from `X`. -/
noncomputable def IsAESquareIntegrable.toContinuous
    (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) (t : ι) (ω : Ω) : E :=
  if Continuous (hX.choose · ω) then hX.choose t ω else 0

lemma IsAESquareIntegrable.continuous_toContinuous (hX : IsAESquareIntegrable X 𝓕 P) (ω : Ω) :
    Continuous (hX.toContinuous X · ω) := by
  simp_rw [toContinuous]
  split_ifs with h
  · exact h
  · exact continuous_const

lemma IsAESquareIntegrable.indist_toContinuous (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hX2 : IsAESquareIntegrable X 𝓕 P) :
    X ≡ᵐ[P] hX2.toContinuous X := by
  filter_upwards [hX1, hX2.choose_spec.2] with ω h1 h2
  simp_rw [h2] at h1
  simp [toContinuous, h1, h2]

variable [SigmaFiniteFiltration P 𝓕]

lemma IsSquareIntegrable.submartingale_sq_norm [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  refine hX.1.submartingale_convex_comp (φ := fun x ↦ ‖x‖ ^ 2) ?_ (by fun_prop) fun i ↦ ?_
  · exact ConvexOn.pow convexOn_univ_norm (fun _ _ ↦ by positivity) 2
  · refine MemLp.integrable_norm_pow ⟨?_, ?_⟩ (by linarith)
    · exact hX.1.1.stronglyMeasurable.aestronglyMeasurable
    · exact lt_of_le_of_lt (le_iSup (fun i ↦ eLpNorm (X i) 2 P) i) hX.3

lemma IsSquareIntegrable.eLpNorm_mono [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    {i j : ι} (hij : i ≤ j) :
    eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have : ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X j ω‖ ^ 2 ∂P := by
    simpa using hX.submartingale_sq_norm.setIntegral_le hij MeasurableSet.univ
  calc
  _ = (∫⁻ ω, ‖X i ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  _ = (ENNReal.ofReal (∫ ω, ‖X i ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq i)).symm
  _ ≤ (ENNReal.ofReal (∫ ω, ‖X j ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
  _ = (∫⁻ ω, ‖X j ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq j))
  _ = eLpNorm (X j) 2 P := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]

lemma _root_.MeasureTheory.UniformIntegrable.ae_tendsto_limitProcess
    (hX1 : UniformIntegrable X 1 P) (hX2 : Martingale X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

lemma IsSquareIntegrable.ae_tendsto_limitProcess [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) [CompleteSpace E] :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) :=
  hX.uniformIntegrable.ae_tendsto_limitProcess hX.martingale

lemma IsAESquareIntegrable.ae_tendsto_limitProcess [Nonempty ι] [IsFiniteMeasure P]
    [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  filter_upwards [hX.choose_spec.2, hX.choose_spec.1.ae_tendsto_limitProcess,
    𝓕.limitProcess_congr hX.choose_spec.2] with ω h1 h2 h3
  rw [h3]
  exact h2.congr (fun t ↦ (h1 t).symm)

variable (𝓕) in
lemma tendsto_ae_condExp' (X : Ω → E) :
    ∀ᵐ ω ∂P, Tendsto (P[X | 𝓕 ·] ω) atTop (𝓝 (P[X | ⨆ t, 𝓕 t] ω)) := by
  sorry

lemma _root_.MeasureTheory.Martingale.condExp_limitProcess_ae_eq
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsCadlag (X · ω)) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

lemma IsSquareIntegrable.condExp_limitProcess_ae_eq (hX : IsSquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

lemma IsAESquareIntegrable.condExp_limitProcess_ae_eq' [CompleteSpace E] [Nonempty ι]
    (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    P[𝓕.limitProcess X P | hτ.measurableSpace] =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma iSup_eLpNorm_le_eLpNorm_limitProcess (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, IsCadlag (X · ω)) [IsFiniteMeasure P] [CompleteSpace E]
    (hX3 : UniformIntegrable X 1 P) :
    ⨆ t, eLpNorm (X t) 2 P ≤ eLpNorm (𝓕.limitProcess X P) 2 P := by
  refine iSup_le fun t ↦ ?_
  rw [eLpNorm_congr_ae (hX1.condExp_limitProcess_ae_eq hX3 hX2 t).symm]
  exact eLpNorm_condExp_le_eLpNorm (by simp) _

lemma isSquareIntegrable_of_limitProcess [CompleteSpace E] [IsFiniteMeasure P]
    (hX1 : Martingale X 𝓕 P) (hX2 : ∀ ω, IsCadlag (X · ω))
    (hX3 : UniformIntegrable X 1 P) (hX4 : MemLp (𝓕.limitProcess X P) 2 P) :
    IsSquareIntegrable X 𝓕 P where
  martingale := hX1
  cadlag := hX2
  bounded := by
    grw [iSup_eLpNorm_le_eLpNorm_limitProcess hX1 hX2 hX3]
    exact hX4.2

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma IsSquareIntegrable.iSup_lintegral_pow_two_eq (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ t, ∫⁻ ω, ‖X t ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖𝓕.limitProcess X P ω‖ₑ ^ 2 ∂P := by
  apply ENNReal.rpow_left_injective (x := 1 / 2) (by simp)
  simp only
  rw [ENNReal.rpow_iSup _ (by simp)]
  convert hX.iSup_eLpNorm_eq_eLpNorm_limitProcess
  · rw [eLpNorm_eq_eLpNorm', eLpNorm']
    all_goals simp
  · rw [eLpNorm_eq_eLpNorm', eLpNorm']
    all_goals simp

lemma IsAESquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess [Nonempty ι]
    (hX : IsAESquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  rw [eLpNorm_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2),
    ← hX.choose_spec.1.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  congr with i
  rw [eLpNorm_congr_ae (hX.choose_spec.2.ae_eq_eval i)]

lemma IsSquareIntegrable.memLp_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  constructor
  · exact Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable
  rw [← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  exact hX.bounded

lemma IsAESquareIntegrable.memLp_limitProcess (hX : IsAESquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  rw [memLp_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2)]
  exact hX.choose_spec.1.memLp_limitProcess

variable [OrderTopology ι] [SecondCountableTopology ι]

theorem IsSquareIntegrable.integral_iSup_norm_rpow_rpow_inv_le_limitProcess
    [CompleteSpace E] [IsFiniteMeasure P] (hX : IsSquareIntegrable X 𝓕 P) :
    (∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ 2 * eLpNorm (𝓕.limitProcess X P) 2 P := by
  simp_rw [← ENNReal.rpow_ofNat (n := 2)]
  grw [integral_iSup_norm_rpow_le hX.martingale hX.isRightContinuous,
    ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_iSup, ← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  · gcongr
    · rw [one_div, ENNReal.rpow_inv_le_iff (by simp)]
      norm_num
    · rw [eLpNorm_eq_eLpNorm' (by simp) (by simp), eLpNorm']
      rfl
  all_goals simp

theorem IsAESquareIntegrable.integral_iSup_norm_rpow_rpow_inv_le_limitProcess
    [CompleteSpace E] [IsFiniteMeasure P] (hX : IsAESquareIntegrable X 𝓕 P) :
    (∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ 2 * eLpNorm (𝓕.limitProcess X P) 2 P := by
  grw [eLpNorm_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2),
    ← hX.choose_spec.1.integral_iSup_norm_rpow_rpow_inv_le_limitProcess]
  gcongr 1
  apply lintegral_mono_ae
  filter_upwards [hX.choose_spec.2] with ω h
  simp [h]

variable [OrderBot ι]

lemma limitProcess_stoppedProcess (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  borelize ι E
  apply 𝓕.limitProcess_ae_eq
  · exact 𝓕.stronglyMeasurable_stoppedValue'
      (hX1.stronglyAdapted.isStronglyProgressive_of_rightContinuous hX3) hX3 hτ |>.mono sorry
      -- #42021
  filter_upwards [hX2.ae_tendsto_limitProcess hX1] with ω h
  cases h1 : τ ω with
  | top => simpa [h1]
  | coe t =>
    simp only [h1, WithTop.coe_inj, stoppedProcess_of_eq_coe, Filtration.stoppedValue'_of_eq_coe]
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨t, fun s hs ↦ by simp [hs]⟩)

variable [IsFiniteMeasure P] [CompleteSpace E]

lemma IsSquareIntegrable.limitProcess_stoppedProcess
    (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P :=
  ProbabilityTheory.limitProcess_stoppedProcess hX.martingale hX.uniformIntegrable
    (fun ω ↦ (hX.cadlag ω).right_continuous) hτ

lemma IsAESquareIntegrable.limitProcess_stoppedProcess
    (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  grw [𝓕.limitProcess_congr (stoppedProcess_congr hX.choose_spec.2),
    hX.choose_spec.1.limitProcess_stoppedProcess hτ, 𝓕.stoppedValue'_congr hX.choose_spec.2]

protected lemma IsSquareIntegrable.stoppedProcess
    [Approximable 𝓕 P] (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsSquareIntegrable (stoppedProcess X τ) 𝓕 P := by
  borelize ι E
  apply isSquareIntegrable_of_limitProcess
  · exact hX.martingale.stoppedProcess (fun _ ↦ (hX.cadlag _).right_continuous) hτ
  · exact fun ω ↦ (hX.cadlag ω).stoppedProcess τ
  · have : ClassD X 𝓕 P := hX.martingale.classD_iff_uniformIntegrable hX.isRightContinuous |>.2
        hX.uniformIntegrable
    simp_rw [stoppedProcess_eq_stoppedValue]
    exact this.uniformIntegrable.comp (fun t : ι ↦ ⟨fun ω ↦ min t (τ ω),
      (isStoppingTime_const 𝓕 t).min hτ, by simp⟩)
  · refine ⟨𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
    calc
    ∫⁻ ω, ‖𝓕.limitProcess (MeasureTheory.stoppedProcess X τ) P ω‖ₑ ^ (ENNReal.toReal 2) ∂P
      = ∫⁻ ω, ‖𝓕.stoppedValue' X τ P ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hX.limitProcess_stoppedProcess hτ] with ω h
      simp [h]
    _ ≤ ∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.isAESquareIntegrable.ae_tendsto_limitProcess] with ω h1
      gcongr
      cases h : τ ω with
      | top =>
        simp only [h, Filtration.stoppedValue'_of_eq_top]
        grw [← ((continuous_enorm.tendsto (𝓕.limitProcess X P ω)).comp h1).limsup_eq,
          limsup_le_iSup]
        simp
      | coe t =>
        simpa [h] using le_iSup (fun s ↦ ‖X s ω‖ₑ) t
    _ ≤ 4 * ∫⁻ ω, ‖𝓕.limitProcess X P ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      grw [integral_iSup_norm_rpow_le hX.martingale hX.isRightContinuous (by simp)]
      simp [hX.iSup_lintegral_pow_two_eq]
      norm_num
    _ < ∞ := by
      apply ENNReal.mul_lt_top (by simp)
      rw [← eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
      exact hX.memLp_limitProcess.2

protected lemma IsAESquareIntegrable.stoppedProcess
    [Approximable 𝓕 P] (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsAESquareIntegrable (stoppedProcess X τ) 𝓕 P := by
  exact ⟨stoppedProcess hX.choose τ, hX.choose_spec.1.stoppedProcess hτ, by
    filter_upwards [hX.choose_spec.2] with ω h t
    simp [stoppedProcess, h]⟩

lemma IsAESquareIntegrable.memLp_two_stoppedValue'
    [Approximable 𝓕 P] (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    MemLp (𝓕.stoppedValue' X τ P) 2 P := by
  borelize E
  rw [← memLp_congr_ae (hX.limitProcess_stoppedProcess hτ)]
  exact (hX.stoppedProcess hτ).memLp_limitProcess

end IsSquareIntegrable

section SquareIntegrable

/-! ### The Hilbert space of square integrable martingales -/

/-- A process is a purely discontinuous square integrable martingale if it is square integrable
and orthogonal to every continuous square integrable martingale in the Hilbert space of
square integrable martingales. -/
def IsPurelyDiscontinuous [InnerProductSpace ℝ E]
  (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  IsAESquareIntegrable X 𝓕 P ∧
  ∀ Y, IsAESquareIntegrable Y 𝓕 P → (∀ᵐ ω ∂P, Continuous (Y · ω)) →
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] = 0

lemma IsPurelyDiscontinuous.congr [InnerProductSpace ℝ E]
    (hX : IsPurelyDiscontinuous X 𝓕 P) (h : X ≡ᵐ[P] Y) :
    IsPurelyDiscontinuous Y 𝓕 P := by
  refine ⟨hX.1.congr h, fun Z hZ1 hZ2 ↦ ?_⟩
  rw [← hX.2 Z hZ1 hZ2]
  apply integral_congr_ae
  filter_upwards [𝓕.limitProcess_congr h] with ω h
  rw [h]

variable [CompleteSpace E] [IsFiniteMeasure P]

section NormedSpace

variable [NormedSpace ℝ E]

variable (E P 𝓕) in
/-- The type of square integrable martingales, as a submodule of equivalence classes of
indistinguishable processes. -/
def squareIntegrableSubmodule : Submodule ℝ (Ω →ₚ[P, 𝓕] E) where
  carrier := {X | IsAESquareIntegrable X 𝓕 P}
  add_mem' {X Y} hX hY := (hX.add hY).congr (coeFn_add X Y).symm
  zero_mem' := IsAESquareIntegrable.const.congr coeFn_zero.symm
  smul_mem' c {X} hX := (hX.smul c).congr (coeFn_smul c X).symm

variable (E P 𝓕) in
/-- The type of square integrable martingales up to indistinguishability. -/
def SquareIntegrable : Type _ := squareIntegrableSubmodule E P 𝓕

instance : AddCommGroup (SquareIntegrable E P 𝓕) :=
  AddSubgroupClass.toAddCommGroup (squareIntegrableSubmodule E P 𝓕)

instance : Module ℝ (SquareIntegrable E P 𝓕) :=
  Submodule.module (squareIntegrableSubmodule E P 𝓕)

/-- The equivalence class of a process that is indistinguishable from a square integrable
martingale. -/
noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable E P 𝓕 :=
  ⟨.mk X hX.aestronglyAdapted, hX.congr (coeFn_mk X _).symm⟩

open scoped Classical in
/-- Given an equivalence class of square integrable martingales, this is a version that satisfies
`IsSquareIntegrable`. Don't use this directly, use the coercion system instead. -/
@[coe]
noncomputable def SquareIntegrable.out (X : SquareIntegrable E P 𝓕) : ι → Ω → E :=
  if h : ∃ Y, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X.1 ≡ᵐ[P] Y
    then h.choose
    else X.2.choose

noncomputable instance : CoeFun (SquareIntegrable E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := SquareIntegrable.out

lemma SquareIntegrable.isSquareIntegrable_coe (X : SquareIntegrable E P 𝓕) :
    IsSquareIntegrable X 𝓕 P := by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact X.2.choose_spec.1

lemma SquareIntegrable.isAESquareIntegrable_coe (X : SquareIntegrable E P 𝓕) :
    IsAESquareIntegrable X 𝓕 P := X.isSquareIntegrable_coe.isAESquareIntegrable

private lemma SquareIntegrable.val_indist_coe (X : SquareIntegrable E P 𝓕) :
    X.1 ≡ᵐ[P] ↑X := by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.2
  · exact X.2.choose_spec.2

@[ext]
lemma SquareIntegrable.ext {X Y : SquareIntegrable E P 𝓕} (h : ↑X ≡ᵐ[P] ↑Y) :
    X = Y := by
  unfold SquareIntegrable
  ext
  grw [val_indist_coe, val_indist_coe, h]

lemma SquareIntegrable.coe_add (X Y : SquareIntegrable E P 𝓕) :
    ↑(X + Y) ≡ᵐ[P] ↑X + ↑Y := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_add, coeFn_add, val_indist_coe, val_indist_coe]

lemma SquareIntegrable.coe_sub (X Y : SquareIntegrable E P 𝓕) :
    ↑(X - Y) ≡ᵐ[P] ↑X - ↑Y := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_sub, coeFn_sub, val_indist_coe, val_indist_coe]

lemma SquareIntegrable.coe_smul (X : SquareIntegrable E P 𝓕) (c : ℝ) :
    ↑(c • X) ≡ᵐ[P] c • ↑X := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_smul, coeFn_smul, val_indist_coe]

lemma SquareIntegrable.coe_neg (X : SquareIntegrable E P 𝓕) :
    ↑(-X) ≡ᵐ[P] -↑X := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_neg, coeFn_neg, val_indist_coe]

private lemma SquareIntegrable.val_mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P)
    (h : AEStronglyAdapted X 𝓕 P) :
    (mk X hX).1 = .mk X h := rfl

lemma SquareIntegrable.mk_indist (hX : IsAESquareIntegrable X 𝓕 P) :
    mk X hX ≡ᵐ[P] X := by
  grw [← val_indist_coe, val_mk X hX hX.aestronglyAdapted, coeFn_mk]

lemma SquareIntegrable.mk_eq_mk {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk X hX = mk Y hY ↔ X ≡ᵐ[P] Y where
  mp h := by
    unfold SquareIntegrable at h
    rw [Subtype.ext_iff, mk, mk] at h
    rwa [AEEqProcess.mk_eq_mk] at h
  mpr h := by
    ext
    grw [mk_indist, mk_indist, h]

lemma SquareIntegrable.mk_add {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk (X + Y) (hX.add hY) = mk X hX + mk Y hY := by
  ext
  grw [mk_indist, coe_add, mk_indist, mk_indist]

lemma SquareIntegrable.mk_sub {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk (X - Y) (hX.sub hY) = mk X hX - mk Y hY := by
  ext
  grw [mk_indist, coe_sub, mk_indist, mk_indist]

variable (E P 𝓕) in
lemma SquareIntegrable.coe_const (c : E) :
    (mk (fun _ _ ↦ c) .const : SquareIntegrable E P 𝓕) ≡ᵐ[P] (fun _ _ ↦ c) :=
  mk_indist _

variable (E P 𝓕) in
lemma SquareIntegrable.coe_zero :
    (0 : SquareIntegrable E P 𝓕) ≡ᵐ[P] 0 := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_zero, coeFn_zero]

variable [Nonempty ι]

@[to_fun limitProcess_fun_add]
lemma IsAESquareIntegrable.limitProcess_add
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.add 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.add h2

@[to_fun limitProcess_fun_sub]
lemma IsAESquareIntegrable.limitProcess_sub
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X - Y) P =ᵐ[P] 𝓕.limitProcess X P - 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.sub 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.sub h2

open TopologicalSpace in
/-- Two modifications that are right-continuous are indistinguishable. -/
lemma indistinguishable_of_modification' {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E} [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E] [Preorder T]
    (hX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := sorry

variable (E P 𝓕) in
/-- The injection of square integrable martingales into the `L^2` space given by `X ↦ X ∞`.
This is a `LinearIsometryEquiv` onto the subspace of functions that are strongly measurable
with respect to `⨆ t, 𝓕 t`, see `SquareIntegrable.toL2Isom`. -/
noncomputable def SquareIntegrable.toL2 : SquareIntegrable E P 𝓕 →ₗ[ℝ] Lp E 2 P where
  toFun X := (isSquareIntegrable_coe X).memLp_limitProcess.toLp
  map_add' X Y := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_add X Y)),
      MemLp.toLp_congr _ _ (IsAESquareIntegrable.limitProcess_add _ _), MemLp.toLp_add]
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.add
        (isSquareIntegrable_coe Y).memLp_limitProcess
    · exact X.isAESquareIntegrable_coe
    · exact Y.isAESquareIntegrable_coe
    · exact (X.isSquareIntegrable_coe.add Y.isSquareIntegrable_coe).memLp_limitProcess
  map_smul' c X := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_smul X c)),
      MemLp.toLp_congr _ _ (𝓕.limitProcess_smul _ _), MemLp.toLp_const_smul]
    · simp
    · exact (isSquareIntegrable_coe X).memLp_limitProcess
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.const_smul c
    · exact ((isSquareIntegrable_coe X).smul c).memLp_limitProcess

lemma SquareIntegrable.toL2_def (X : SquareIntegrable E P 𝓕) :
    toL2 E P 𝓕 X = (isSquareIntegrable_coe X).memLp_limitProcess.toLp := rfl

lemma SquareIntegrable.toL2_ae_eq (X : SquareIntegrable E P 𝓕) :
    toL2 E P 𝓕 X =ᵐ[P] 𝓕.limitProcess X P := by
  rw [toL2_def]
  exact MemLp.coeFn_toLp _

variable [SeparableSpace ι]

lemma SquareIntegrable.injective_toL2 : Injective (toL2 E P 𝓕) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  rw [toL2_def, ← MemLp.toLp_zero, MemLp.toLp_eq_toLp_iff] at hX
  swap; · simp
  ext
  refine .trans ?_ (coe_zero _ _ _).symm
  refine indistinguishable_of_modification' ?_ ?_ fun t ↦ ?_
  · exact ae_of_all _ fun _ ↦ (isSquareIntegrable_coe _).cadlag _
      |>.right_continuous
  · exact ae_of_all _ fun _ ↦ isRightContinuous_const 0
  grw [show (0 : ι → Ω → E) t = 0 from rfl, ← lpNorm_eq_zero _ two_ne_zero, ← toReal_eLpNorm,
    ENNReal.toReal_eq_zero_iff]
  · left
    suffices eLpNorm (X t) 2 P ≤ 0 by simp_all
    grw [le_iSup fun s ↦ eLpNorm (X s) 2 P,
      (isSquareIntegrable_coe _).iSup_eLpNorm_eq_eLpNorm_limitProcess, nonpos_iff_eq_zero,
      ← ofReal_lpNorm, ENNReal.ofReal_eq_zero, lpNorm_congr hX, lpNorm_zero]
    exact (isSquareIntegrable_coe _).memLp_limitProcess
  · exact ((isSquareIntegrable_coe X).martingale.stronglyMeasurable
      t).aestronglyMeasurable.mono (𝓕.le t)
  · exact (isSquareIntegrable_coe X).memLp_two t

noncomputable instance :
    NormedAddCommGroup (SquareIntegrable E P 𝓕) :=
  NormedAddCommGroup.induced _ _ (SquareIntegrable.toL2 E P 𝓕) SquareIntegrable.injective_toL2

lemma SquareIntegrable.norm_def {X : SquareIntegrable E P 𝓕} :
    ‖X‖ = lpNorm (𝓕.limitProcess X P) 2 P := by
  change ‖toL2 E P 𝓕 X‖ = _
  rw [toL2_def, Lp.norm_toLp, lpNorm, if_pos]
  exact 𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable

lemma SquareIntegrable.enorm_def {X : SquareIntegrable E P 𝓕} :
    ‖X‖ₑ = eLpNorm (𝓕.limitProcess X P) 2 P := by
  rw [← ofReal_norm, norm_def, ofReal_lpNorm]
  exact (isSquareIntegrable_coe X).memLp_limitProcess

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [SeparableSpace ι]

noncomputable instance :
    InnerProductSpace ℝ (SquareIntegrable E P 𝓕) :=
  InnerProductSpace.induced (SquareIntegrable.toL2 E P 𝓕)

lemma SquareIntegrable.inner_def {X Y : SquareIntegrable E P 𝓕} :
    ⟪X, Y⟫ = P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] := by
  rw [inner_induced_eq, toL2_def, toL2_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(isSquareIntegrable_coe X).memLp_limitProcess.coeFn_toLp,
    (isSquareIntegrable_coe Y).memLp_limitProcess.coeFn_toLp] with ω h1 h2
  simp_all

lemma IsAESquareIntegrable.inner_limitProcess_eq (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] =
      ⟪SquareIntegrable.mk X hX, .mk Y hY⟫ := by
  rw [SquareIntegrable.inner_def]
  apply integral_congr_ae
  filter_upwards [𝓕.limitProcess_congr (SquareIntegrable.mk_indist hX),
    𝓕.limitProcess_congr (SquareIntegrable.mk_indist hY)] with ω h1 h2
  simp_all

/-- Given a martingale `X`, this is a càdlàg martingale that is a modification of `X`. -/
def _root_.MeasureTheory.modif (X : ι → Ω → E) :
    ι → Ω → E := sorry

lemma _root_.MeasureTheory.isCadlag_modif (X : ι → Ω → E) (ω : Ω) :
    IsCadlag (modif X · ω) := sorry

lemma _root_.MeasureTheory.modification_modif (hX : Martingale X 𝓕 P) (t : ι) :
    modif X t =ᵐ[P] X t := sorry

lemma _root_.MeasureTheory.martingale_modif : Martingale (modif X) 𝓕 P := sorry

variable (𝓕) in
lemma isSquareIntegrable_modif_condExp {X : Ω → E} (hX : MemLp X 2 P) :
    IsSquareIntegrable (modif (fun t ↦ P[X | 𝓕 t])) 𝓕 P where
  martingale := martingale_modif
  cadlag := isCadlag_modif _
  bounded := by
    refine (iSup_le fun i ↦ ?_).trans_lt hX.2
    grw [eLpNorm_congr_ae (modification_modif (martingale_condExp X 𝓕 P) i), eLpNorm_condExp_le]

/-- The `LinearIsometryEquiv` between square integrable martingales and
the type of `L^2` random variables that are strongly measurable with respect to `⨆ t, 𝓕 t`,
given by `X ↦ X ∞`. -/
noncomputable def SquareIntegrable.toL2Isom [OrderTopology ι] :
    SquareIntegrable E P 𝓕 ≃ₗᵢ[ℝ] lpMeas E ℝ (⨆ t, 𝓕 t) 2 P where
  toFun X := ⟨toL2 E P 𝓕 X, by
    rw [mem_lpMeas_iff_aestronglyMeasurable, aestronglyMeasurable_congr (toL2_ae_eq X)]
    exact 𝓕.stronglyMeasurable_limitProcess.aestronglyMeasurable
  ⟩
  invFun X := mk (modif (fun t ↦ P[X.1 | 𝓕 t]))
    (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).isAESquareIntegrable
  map_add' := by simp
  map_smul' := by simp
  left_inv X := by
    ext
    refine indistinguishable_of_modification' ?_ ?_ (fun t ↦ ?_)
    · exact ae_of_all _ (isSquareIntegrable_coe _).isRightContinuous
    · exact ae_of_all _ (isSquareIntegrable_coe _).isRightContinuous
    simp only
    grw [(mk_indist ?_).ae_eq_eval, modification_modif, toL2_def, MemLp.coeFn_toLp,
      X.isSquareIntegrable_coe.condExp_limitProcess_ae_eq]
    · exact martingale_condExp _ _ _
    · exact isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp _) |>.isAESquareIntegrable
  right_inv X := by
    ext
    simp only
    grw [toL2_def, MemLp.coeFn_toLp, 𝓕.limitProcess_congr (mk_indist _)]
    obtain ⟨u, hu⟩ := (atTop : Filter ι).exists_seq_tendsto
    have h1 : ∀ᵐ ω ∂P, ∀ n, modif (fun t ↦ P[X.1 | 𝓕 t]) (u n) ω = P[X.1 | 𝓕 (u n)] ω := by
      rw [ae_all_iff]
      exact fun _ ↦ modification_modif (martingale_condExp X.1 𝓕 P) _
    filter_upwards [h1,
      (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).ae_tendsto_limitProcess,
      tendsto_ae_condExp' 𝓕 X.1,
      condExp_of_aestronglyMeasurable' (iSup_le 𝓕.le) X.2
        ((Lp.memLp X.1).integrable (by simp))] with ω h1 h2 h3 h4
    rw [← h4]
    apply tendsto_nhds_unique ?_ (h3.comp hu)
    apply Tendsto.congr h1 (h2.comp hu)
  norm_map' X := rfl

instance [OrderTopology ι] : CompleteSpace (SquareIntegrable E P 𝓕) :=
  haveI : Fact (⨆ t, 𝓕 t ≤ mΩ) := ⟨iSup_le 𝓕.le⟩
  SquareIntegrable.toL2Isom.toIsometryEquiv.completeSpace

end InnerProductSpace

/-! ### Continuous square integrable martingales -/

section NormedSpace

variable [NormedSpace ℝ E]

variable (E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def continuousSquareIntegrable : Submodule ℝ (SquareIntegrable E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2, hX3⟩ ⟨Y', hY1, hY2, hY3⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), hX2.add hY2, ?_⟩
    grw [← hX3, ← hY3, SquareIntegrable.coe_add]
  zero_mem' := ⟨0, by fun_prop, .const, SquareIntegrable.coe_zero E P 𝓕⟩
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2, hX3⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, hX2.smul c, ?_⟩
    grw [SquareIntegrable.coe_smul X c, hX3]

lemma continuous_coe {X : SquareIntegrable E P 𝓕} (hX : X ∈ continuousSquareIntegrable E P 𝓕)
    (ω : Ω) :
    Continuous (X · ω) := by
  have : ∃ Y : ι → Ω → E,
      (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X.1 ≡ᵐ[P] Y := by
    obtain ⟨Y, hY1, hY2, hY3⟩ := hX
    exact ⟨Y, hY1, hY2, by grw [X.val_indist_coe, hY3]⟩
  rw [SquareIntegrable.out, dif_pos this]
  exact this.choose_spec.1 ω

lemma IsAESquareIntegrable.isSquareIntegrable_toContinuous [h𝓕 : 𝓕.IsComplete P]
    (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hX2 : IsAESquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (hX2.toContinuous X) 𝓕 P := by
  have obv : ∀ᵐ ω ∂P, Continuous (hX2.choose · ω) := by
    filter_upwards [hX2.choose_spec.2, hX1] with ω h h'
    simpa [← h]
  refine ⟨hX2.choose_spec.1.martingale.congr (fun t ↦ ?_) (fun t ↦ ?_),
    fun ω ↦ (hX2.continuous_toContinuous ω).isCadlag, ?_⟩
  · obtain ⟨f, hf⟩ := hX2.choose_spec.1.martingale.stronglyAdapted t
    let s := {ω | Continuous (hX2.choose · ω)}
    have hs : MeasurableSet[𝓕 t] s := (h𝓕.measurableSet_of_null obv t).of_compl
    refine ⟨fun n ↦ @SimpleFunc.piecewise Ω E (𝓕 t) s hs (f n) (@SimpleFunc.const Ω E (𝓕 t) 0),
      fun ω ↦ ?_⟩
    by_cases hω : Continuous (hX2.choose · ω)
    · simpa [s, hω, toContinuous] using hf ω
    · simp [s, hω, toContinuous]
  · filter_upwards [obv] with ω h
    simp [toContinuous, h]
  · convert hX2.choose_spec.1.memLp_limitProcess.2
    rw [← hX2.choose_spec.1.iSup_eLpNorm_eq_eLpNorm_limitProcess]
    congr with i
    rw [← eLpNorm_congr_ae ((hX2.indist_toContinuous hX1).ae_eq_eval i),
      eLpNorm_congr_ae (hX2.choose_spec.2.ae_eq_eval i)]

/-- A square integrable martingale that is almost surely continuous is indistinguishable
from a square integrable martingale that is continuous everywhere. -/
lemma mem_continuousSquareIntegrable [𝓕.IsComplete P] {X : SquareIntegrable E P 𝓕}
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) : X ∈ continuousSquareIntegrable E P 𝓕 :=
  ⟨X.isAESquareIntegrable_coe.toContinuous X,
    X.isAESquareIntegrable_coe.continuous_toContinuous,
    X.isAESquareIntegrable_coe.isSquareIntegrable_toContinuous hX,
    X.isAESquareIntegrable_coe.indist_toContinuous hX⟩

/-- A square integrable martingale that is almost surely continuous is indistinguishable
from a square integrable martingale that is continuous everywhere. -/
lemma IsAESquareIntegrable.mk_mem_continuousSquareIntegrable [𝓕.IsComplete P]
    (hX1 : IsAESquareIntegrable X 𝓕 P) (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    .mk X hX1 ∈ continuousSquareIntegrable E P 𝓕 := by
  apply mem_continuousSquareIntegrable
  filter_upwards [hX2, SquareIntegrable.mk_indist hX1] with ω h1 h2
  simpa [h2]

/-- If `M` is a sequence of square integrable martingales that converges to `N` in
`SquareIntegrable E P 𝓕`, then there exists `φ : ℕ → ℕ` increasing such that almost surely,
`M n` converges to `N` uniformly. This is needed to show that the space of continuous
square integrable martingales is closed. -/
lemma exists_subsequence_ae_tendsto_uniformly {M : ℕ → ι → Ω → E} {N : ι → Ω → E}
    [OrderTopology ι] [SecondCountableTopology ι]
    (hM : ∀ n, IsAESquareIntegrable (M n) 𝓕 P) (hN : IsAESquareIntegrable N 𝓕 P)
    (h : Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ ω ∂P, TendstoUniformly (fun n t ↦ M (φ n) t ω) (N · ω) atTop) := by
  obtain hι | _ := isEmpty_or_nonempty ι
  · refine ⟨id, strictMono_id, ae_of_all _ fun _ ↦ ?_⟩
    rw [← tendstoUniformlyOn_univ, Set.univ_eq_empty_iff.2 hι]
    exact tendstoUniformlyOn_empty
  -- We can find a subsequence such that `‖(M (φ n))∞ - N∞‖ₑ ≤ (1 / 2) ^ n`
  have h1 n : ∃ k, ∀ l ≥ k,
      eLpNorm (𝓕.limitProcess (M l) P - 𝓕.limitProcess N P) 2 P ≤ (1 / 2) ^ n := by
    rw [ENNReal.tendsto_atTop_zero] at h
    exact h _ (ENNReal.pow_pos (ENNReal.div_pos (by simp) (by simp)) n)
  obtain ⟨φ, mφ, hφ⟩ := extraction_forall_of_eventually' h1
  have aem_iSup n : AEMeasurable (fun ω ↦ ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ) P := by
    refine ⟨fun ω ↦ ⨆ t, ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ, ?_, ?_⟩
    · suffices Measurable (⨆ t, fun ω ↦ ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ) by
        convert this with ω
        simp
      refine measurable_iSup_of_rightContinuous (fun ω ↦ ?_) (fun ω ↦ ?_)
      · exact (((hM (φ n)).choose_spec.1.sub hN.choose_spec.1).isRightContinuous ω).continuous_comp
          continuous_enorm
      · exact (continuous_enorm.comp_stronglyMeasurable ((hM (φ n)).choose_spec.1.sub
          hN.choose_spec.1).martingale.stronglyMeasurable').measurable
    · filter_upwards [(hM (φ n)).choose_spec.2, hN.choose_spec.2] with ω h1 h2
      simp_rw [h1, h2]
  use φ, mφ
  /- This implies that the series `∑' n, ‖(M (φ n))∞ - N∞‖ₑ` converges, which by Doob's inequality
  implies that `∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ converges. -/
  have : ∫⁻ ω, ∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P < ∞ :=
    calc
    _ = ∑' n, ∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P := lintegral_tsum aem_iSup
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) *
        ∑' n, (∫⁻ ω, (⨆ t, ‖M (φ n) t ω - N t ω‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.tsum_mul_left]
      gcongr
      grw [← ENNReal.rpow_rpow_inv (y := 2) (x := ∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P) (by simp),
        ENNReal.rpow_lintegral_le' (aem_iSup n) (by simp), ENNReal.mul_rpow_of_nonneg, one_div]
      · norm_num
      · simp
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) * (2 * ∑' n, eLpNorm (𝓕.limitProcess (M (φ n)) P -
        𝓕.limitProcess N P) 2 P) := by
      rw [← ENNReal.tsum_mul_left (a := 2)]
      gcongr
      grw [((hM (φ n)).fun_sub hN).integral_iSup_norm_rpow_rpow_inv_le_limitProcess,
        eLpNorm_congr_ae ((hM (φ n)).limitProcess_fun_sub hN)]
      rfl
    _ ≤ (P Set.univ) ^ (1 / 2 : ℝ) * (2 * ∑' n, (1 / 2 : ℝ≥0∞) ^ n) := by grw [hφ]
    _ < ∞ := by
      refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top (by simp) ?_)
      · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
      rw [ENNReal.tsum_geometric]
      simp
  filter_upwards [ae_lt_top' (.tsum aem_iSup) this.ne] with ω h
  -- In particular `⨆ t, ‖M (φ n) t ω - N t ω‖ₑ` tends to `0`, so we have uniform convergence.
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.tendsto_atTop_zero.1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h.ne)
    (.ofReal (ε / 2)) (by simpa)
  refine eventually_atTop.2 ⟨n, fun k hk t ↦ ?_⟩
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by simp)]
  · grw [dist_comm, dist_eq_norm, ofReal_norm, le_iSup (fun s ↦ ‖M (φ k) s ω - N s ω‖ₑ), hn k hk,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg]
    · simpa
    · positivity

/- Is in mathlib but not available here for some reason. -/
@[to_additive]
theorem tendsto_iff_enorm_div_tendsto_zero {α E : Type*} [SeminormedCommGroup E] {f : α → E}
    {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

/-- The submodule of continuous square integrable martingales is closed in the Hilbert space
of square integrable martingales. -/
instance [𝓕.IsComplete P] [Nonempty ι] [OrderTopology ι] [SecondCountableTopology ι] :
    IsClosed (continuousSquareIntegrable E P 𝓕 : Set (SquareIntegrable E P 𝓕)) := by
  refine IsSeqClosed.isClosed fun M N hM1 hM2 ↦ ?_
  have :
      Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0) := by
    simp_rw [tendsto_iff_enorm_sub_tendsto_zero, SquareIntegrable.enorm_def] at hM2
    refine hM2.congr fun n ↦ ?_
    rw [eLpNorm_congr_ae <| 𝓕.limitProcess_congr (SquareIntegrable.coe_sub (M n) N),
      eLpNorm_congr_ae (IsAESquareIntegrable.limitProcess_sub ?_ ?_)]
    all_goals exact SquareIntegrable.isAESquareIntegrable_coe _
  obtain ⟨φ, mφ, hφ⟩ := exists_subsequence_ae_tendsto_uniformly
      (fun n ↦ (M n).isAESquareIntegrable_coe) N.isAESquareIntegrable_coe this
  apply mem_continuousSquareIntegrable
  filter_upwards [hφ] with ω h
  exact h.continuous <| .of_forall fun n ↦ continuous_coe (hM1 (φ n)) ω

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [OrderTopology ι] [SecondCountableTopology ι]

open scoped Classical in
/-- The continuous martingale part of a square-integrable martingale `X`. This is defined as the
projection of `X` onto the closed subspace of continuous square-integrable martingales. -/
noncomputable def continuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [SigmaFiniteFiltration P 𝓕] [𝓕.IsComplete P] : ι → Ω → E :=
  if hX : IsAESquareIntegrable X 𝓕 P
    then (continuousSquareIntegrable E P 𝓕).starProjection (SquareIntegrable.mk X hX)
    else 0

section IsComplete

variable [𝓕.IsComplete P]

lemma continuousPart_congr (hXY : X ≡ᵐ[P] Y) :
    continuousPart X 𝓕 P = continuousPart Y 𝓕 P := by
  by_cases hX : IsAESquareIntegrable X 𝓕 P
  · simp only [continuousPart, hX, ↓reduceDIte, hX.congr hXY]
    ext t ω
    congr 2
    rwa [SquareIntegrable.mk_eq_mk]
  simp [continuousPart, hX, (isAESquareIntegrable_congr hXY).not.1 hX]

lemma continuous_continuousPart (X : ι → Ω → E) (ω : Ω) :
    Continuous (continuousPart X 𝓕 P · ω) := by
  rw [continuousPart]
  split_ifs
  · exact continuous_coe ((continuousSquareIntegrable E P 𝓕).starProjection_apply_mem _) ω
  simp [continuous_const]

lemma isSquareIntegrable_continuousPart :
    IsSquareIntegrable (continuousPart X 𝓕 P) 𝓕 P := by
  rw [continuousPart]
  split_ifs
  · exact SquareIntegrable.isSquareIntegrable_coe _
  · exact .const

lemma IsAESquareIntegrable.mk_continuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    .mk (continuousPart X 𝓕 P) isSquareIntegrable_continuousPart.isAESquareIntegrable =
      (continuousSquareIntegrable E P 𝓕).starProjection (.mk X hX) := by
  ext
  grw [SquareIntegrable.mk_indist, continuousPart, dif_pos hX]

/-- The purely discontinuous martingale part of a square integrable martingale. Purely discontinuous
martingales are the orthogonal submodule of continuous square integrable martingales
in the Hilbert space of square integrable martingales. -/
noncomputable def discontinuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [𝓕.IsComplete P] : ι → Ω → E :=
  X - continuousPart X 𝓕 P

lemma discontinuousPart_def (X : ι → Ω → E) :
    discontinuousPart X 𝓕 P = X - continuousPart X 𝓕 P := rfl

lemma continuousPart_add_discontinuousPart :
    continuousPart X 𝓕 P + discontinuousPart X 𝓕 P = X := by
  simp [discontinuousPart]

lemma IsAESquareIntegrable.discontinuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (discontinuousPart X 𝓕 P) 𝓕 P :=
  hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable

end IsComplete

variable (E P 𝓕) in
/-- The submodule of purely discontinuous square integrable martingales. Purely discontinuous
martingales are the orthogonal submodule of continuous square integrable martingales
in the Hilbert space of square integrable martingales. -/
noncomputable def discontinuousSquareIntegrable : Submodule ℝ (SquareIntegrable E P 𝓕) :=
  (continuousSquareIntegrable E P 𝓕).orthogonal

omit [OrderTopology ι] in
/-- A purely discontinuous square integrable martingale is in the submodule of purely discontinuous
square integrable martingales. This statements links the predicate `IsPurelyDiscontinuous`
with the submodule `discontinuousSquareIntegrable`. -/
lemma mem_discontinuousSquareIntegrable {Y : SquareIntegrable E P 𝓕}
    (hY : IsPurelyDiscontinuous Y 𝓕 P) : Y ∈ discontinuousSquareIntegrable E P 𝓕 := by
  rw [discontinuousSquareIntegrable, Submodule.mem_orthogonal']
  intro X hX
  rw [SquareIntegrable.inner_def, hY.2]
  · exact X.isAESquareIntegrable_coe
  · exact ae_of_all _ <| continuous_coe hX

omit [OrderTopology ι] in
/-- A purely discontinuous square integrable martingale is in the submodule of purely discontinuous
square integrable martingales. This statements links the predicate `IsPurelyDiscontinuous`
with the submodule `discontinuousSquareIntegrable`. -/
lemma IsPurelyDiscontinuous.mk_mem_discontinuousSquareIntegrable
    (hY : IsPurelyDiscontinuous Y 𝓕 P) :
    .mk Y hY.1 ∈ discontinuousSquareIntegrable E P 𝓕 := by
  apply mem_discontinuousSquareIntegrable
  exact hY.congr (SquareIntegrable.mk_indist hY.1).symm

variable [𝓕.IsComplete P]

/-- The discontinuous part of square integrable martingale is purely discontinuous. -/
lemma isPurelyDiscontinuous_discontinuousPart (hX : IsAESquareIntegrable X 𝓕 P) :
    IsPurelyDiscontinuous (discontinuousPart X 𝓕 P) 𝓕 P := by
  constructor
  · exact hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable
  intro Y hY1 hY2
  rw! [hX.discontinuousPart.inner_limitProcess_eq hY1, discontinuousPart, SquareIntegrable.mk_sub,
    hX.mk_continuousPart, Submodule.starProjection_inner_eq_zero]
  · rfl
  · apply mem_continuousSquareIntegrable
    filter_upwards [hY2, SquareIntegrable.mk_indist hY1] with ω h1 h2
    simp_rw [h2]
    exact h1

/-- Uniqueness of the decomposition of a square integrable martingale into a continuous part and
a discontinuous part: If a square integrable martingale `Z` is indistinguishable from `X + Y`
where `X` is continuous and `Y` is discontinuous, then `X` is indistinguishable from the
continuous part of `Z`. -/
lemma indist_continuousPart (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : IsPurelyDiscontinuous Y 𝓕 P)
    (hZ1 : IsAESquareIntegrable Z 𝓕 P) (hZ2 : Z ≡ᵐ[P] X + Y) :
    X ≡ᵐ[P] continuousPart Z 𝓕 P := by
  rw [← SquareIntegrable.mk_eq_mk (hX := hZ1) (hY := hX1.add hY.1),
    SquareIntegrable.mk_add (hX := hX1) (hY := hY.1)] at hZ2
  have := Submodule.eq_starProjection_of_mem_orthogonal' (hX1.mk_mem_continuousSquareIntegrable hX2)
    hY.mk_mem_discontinuousSquareIntegrable hZ2
  rw [continuousPart, dif_pos hZ1, this]
  exact SquareIntegrable.mk_indist hX1 |>.symm

/-- Uniqueness of the decomposition of a square integrable martingale into a continuous part and
a discontinuous part: If a square integrable martingale `Z` is indistinguishable from `X + Y`
where `X` is continuous and `Y` is discontinuous, then `Y` is indistinguishable from the
discontinuous part of `Z`. -/
lemma indist_discontinuousPart {X Y Z : ι → Ω → E} (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY2 : IsPurelyDiscontinuous Y 𝓕 P)
    (hZ1 : IsAESquareIntegrable Z 𝓕 P) (hZ2 : Z ≡ᵐ[P] X + Y) :
    Y ≡ᵐ[P] discontinuousPart Z 𝓕 P := by
  grw [discontinuousPart, ← indist_continuousPart hX1 hX2 hY2 hZ1 hZ2, hZ2]
  simp

omit [𝓕.IsComplete P] in
/-- The stopped process of a purely discontinuous square integrable martingale is again
a purely discontinuous square integrable martingale. -/
nonrec
lemma IsPurelyDiscontinuous.stoppedProcess [OrderBot ι] [MetrizableSpace ι] [Approximable 𝓕 P]
    (hX : IsPurelyDiscontinuous X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsPurelyDiscontinuous (stoppedProcess X τ) 𝓕 P := by
  borelize ι
  refine ⟨hX.1.stoppedProcess hτ, fun Y hY1 hY2 ↦ ?_⟩
  rw [← hX.2 (stoppedProcess Y τ), ← integral_condExp hτ.measurableSpace_le,
    ← integral_condExp hτ.measurableSpace_le (f := fun _ ↦ ⟪_, _⟫)]
  · apply integral_congr_ae
    grw [condExp_inner_of_aestronglyMeasurable_left,
      condExp_inner_of_aestronglyMeasurable_right]
    · filter_upwards [hX.1.limitProcess_stoppedProcess hτ, hX.1.condExp_limitProcess_ae_eq' hτ,
        hY1.limitProcess_stoppedProcess hτ, hY1.condExp_limitProcess_ae_eq' hτ] with ω h1 h2 h3 h4
      rw [h1, h2, h3, h4]
    · exact (hY1.aestronglyMeasurable_stoppedValue' hτ).congr
        (hY1.limitProcess_stoppedProcess hτ).symm
    · exact integrable_inner hX.1.memLp_limitProcess (hY1.stoppedProcess hτ).memLp_limitProcess
    · exact hX.1.memLp_limitProcess.integrable (by simp)
    · exact (hX.1.aestronglyMeasurable_stoppedValue' hτ).congr
        (hX.1.limitProcess_stoppedProcess hτ).symm
    · exact integrable_inner (hX.1.stoppedProcess hτ).memLp_limitProcess hY1.memLp_limitProcess
    · exact hY1.memLp_limitProcess.integrable (by simp)
  · exact hY1.stoppedProcess hτ
  · filter_upwards [hY2] with ω h using h.stoppedProcess τ

/-- The continuous part of the stopped process is the stopped process of the continuous part. -/
lemma continuousPart_stoppedProcess [OrderBot ι] [MeasurableSpace ι] [BorelSpace ι]
    [MetrizableSpace ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    continuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P] stoppedProcess (continuousPart X 𝓕 P) τ := by
  have : stoppedProcess X τ =
      stoppedProcess (continuousPart X 𝓕 P) τ + stoppedProcess (discontinuousPart X 𝓕 P) τ := by
    rw [← stoppedProcess_add, continuousPart_add_discontinuousPart]
  borelize E
  symm
  apply indist_continuousPart
    (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (ae_of_all _ (fun ω ↦ (continuous_continuousPart X ω).stoppedProcess τ))
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [this])

attribute [to_fun] stoppedProcess_sub

lemma stoppedProcess_discontinuousPart [OrderBot ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    discontinuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P]
      stoppedProcess (discontinuousPart X 𝓕 P) τ := by
  have : stoppedProcess X τ =
      stoppedProcess (continuousPart X 𝓕 P) τ + stoppedProcess (discontinuousPart X 𝓕 P) τ := by
    rw [← stoppedProcess_add, continuousPart_add_discontinuousPart]
  borelize E
  symm
  apply indist_discontinuousPart
    (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (ae_of_all _ (fun ω ↦ (continuous_continuousPart X ω).stoppedProcess τ))
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [this])

end InnerProductSpace

end SquareIntegrable

section LocallySquareIntegrable

variable [NormedSpace ℝ E]

/-- A stochastic process is locally square-integrable if it satisfies the square-integrable
martingale property locally. -/
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P

lemma IsSquareIntegrable.isLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX

/-- A locally square-integrable martingale has locally submartingale squared norm. -/
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm [SigmaFiniteFiltration P 𝓕]
    [OrderBot ι] [OrderTopology ι] [CompleteSpace E]
    (hX : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  have h_stopped_sq_norm {τ : Ω → WithTop ι} :
      stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
        fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
    ext t ω
    by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ ω, IsCadlag (Y · ω)) 𝓕 (fun t ω ↦ ‖X t ω‖ ^ 2) P
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hXn := hX.stoppedProcess_localSeq n
  constructor
  · simpa [h_stopped_sq_norm] using hXn.submartingale_sq_norm
  · intro ω
    simpa [h_stopped_sq_norm] using IsCadlag.norm_sq (hXn.cadlag ω)

end LocallySquareIntegrable

end ProbabilityTheory
