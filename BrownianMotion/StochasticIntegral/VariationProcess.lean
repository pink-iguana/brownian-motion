/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BrownianMotion.Auxiliary.SeparableSpace
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.EMetricSpace.BoundedVariation

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
  time `t` of the variation process of a strongly adapted process is `𝓕 t`-measurable.

-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω}

variable [LinearOrder ι] [PseudoEMetricSpace E]

/-- The variation process of `X` from the starting time `a`. -/
noncomputable def variationProcess (X : ι → Ω → E) (a : ι) : ι → Ω → ℝ :=
  fun t ω ↦ variationOnFromTo (X · ω) univ a t

/-- For `a ≤ t`, the variation process at time `t` is the total variation of the path on `Icc a t`,
converted to a real number. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (X : ι → Ω → E) {a t : ι} (hat : a ≤ t)
    (ω : Ω) : variationProcess X a t ω = (eVariationOn (X · ω) (Icc a t)).toReal := by
  simp [variationProcess, variationOnFromTo, univ_inter, hat]

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

/-- The variation over `s`, reindexed as a supremum over monotone tuples `Fin (n + 1) → ι` with
values in `s`. Unlike the defining supremum over monotone sequences `ℕ → ι`, this index type is
countable whenever `s` is, which is what makes `measurable_eVariationOn_of_countable` go through. -/
theorem eVariationOn_eq_iSup_fin {s : Set ι} (X : ι → Ω → E) (ω : Ω) :
    eVariationOn (X · ω) s = ⨆ (n : ℕ) (p : {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}),
      ∑ i : Fin n, edist (X (p.1 i.succ) ω) (X (p.1 i.castSucc) ω) := by
  refine le_antisymm (iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_)
    (iSup_le fun n ↦ iSup_le fun ⟨p, hp, hps⟩ ↦ ?_)
  · let κ := fun n ↦ {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s}
    let p : κ n := ⟨fun i : Fin (n + 1) ↦ u i, hu.comp Fin.val_strictMono.monotone, fun i ↦ hus i⟩
    have : ∑ i ∈ Finset.range n, edist (X (u (i + 1)) ω) (X (u i) ω) =
      ∑ i : Fin n, edist (X (p.1 i.succ) ω) (X (p.1 i.castSucc) ω) := by simp [Finset.sum_range, p]
    simpa [this] using le_iSup₂ (α := ℝ≥0∞) n p
  · let v : ℕ → ι := fun k ↦ p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
    have : ∑ i : Fin n, edist (X (p i.succ) ω) (X (p i.castSucc) ω) =
      ∑ i ∈ Finset.range n, edist (X (v (i + 1)) ω) (X (v i) ω) := by
      simp only [Finset.sum_range, Order.add_one_le_iff, Fin.is_lt, inf_of_le_left, Fin.is_le', v]
      congr
    rw [this]
    exact eVariationOn.sum_le (fun _ _ _ ↦ hp (by aesop)) fun i ↦ hps _

/-- The variation of a process over a countable set of times is measurable in `ω`. -/
theorem measurable_eVariationOn_of_countable {m : MeasurableSpace Ω} {s : Set ι}
    (hs : s.Countable) {X : ι → Ω → E} (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i)) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  simp only [eVariationOn_eq_iSup_fin]
  refine Measurable.iSup fun n ↦ ?_
  have : Countable {u : Fin (n + 1) → ι // Monotone u ∧ ∀ i, u i ∈ s} :=
    (countable_pi fun _ ↦ hs).mono fun _ hu ↦ hu.2
  refine Measurable.iSup fun p ↦ Finset.measurable_sum _ fun i _ ↦ ?_
  exact (continuous_edist.comp_stronglyMeasurable
    ((hX _ (p.2.2 i.succ)).prodMk (hX _ (p.2.2 i.castSucc)))).measurable

variable [TopologicalSpace ι]

section Separable

/-- The variation of a function that is continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`. -/
theorem eVariationOn_eq_comp_val_of_dense [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) {f : ι → E} (hf : ContinuousOn f s) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  simp only [eVariationOn.eVariationOn_eq_strictMonoOn, iSup_le_iff, Sigma.forall, Subtype.forall,
    mem_Iic, and_imp]
  refine fun n u hsu hus ↦ ?_
  -- the product filter approaching every partition point through the dense set `t`
  let F := pi (fun i ↦ 𝓝[t] (u (min i n)))
  let g : (ℕ → ι) → ℝ≥0∞ := (fun a ↦ ∑ i ∈ Finset.range n, edist (f (a (i + 1))) (f (a i)))
  have heval ⦃i⦄ (hi : i ≤ n) : Tendsto (fun a : ℕ → ι ↦ a i) F (𝓝[t] (u i)) := by
    nth_rw 2 [← min_eq_left hi]
    exact tendsto_eval_pi _ i
  have htend : Tendsto g F (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    suffices ∀ i ≤ n, Tendsto (fun a : ℕ → ι ↦ f (a i)) F (𝓝 (f (u i))) from
      tendsto_finsetSum _ fun i hi ↦ (this (i + 1) (Finset.mem_range.1 hi)).edist
        (this i (Finset.mem_range_le hi))
    refine fun i hi ↦ Tendsto.comp ?_ (heval hi)
    exact (hf (u i) (hus _ hi)).mono (Subtype.coe_image_subset s t)
  have (i : ℕ) : (𝓝[t] (u (min i n))).NeBot := by
    simpa [← mem_closure_iff_nhdsWithin_neBot, ← closure_image_closure continuous_subtype_val,
      ht.closure_eq] using subset_closure <| hus _ (min_le_right i n)
  refine le_of_tendsto htend ?_
  -- eventually the approximants lie in `t` and stay strictly increasing along the partition
  have hlt : ∀ᶠ c in F, StrictMonoOn c (Iic n) := by
    unfold StrictMonoOn
    refine (eventually_all_finite (finite_Iic n)).2 fun _ hi ↦
      (eventually_all_finite (finite_Iic n)).2 fun _ hj ↦ eventually_all.2 fun hij ↦ ?_
    refine Tendsto.eventually_lt ?_ ?_ (hsu hi hj hij)
    <;> exact tendsto_nhds_of_tendsto_nhdsWithin (heval (by assumption))
  have hmem : ∀ᶠ c in F, ∀ i ∈ Iic n, c i ∈ (t : Set ι) := (eventually_all_finite (finite_Iic n)).2
    fun i hi ↦ (tendsto_eval_pi _ i).eventually eventually_mem_nhdsWithin
  filter_upwards [hlt, hmem] with c hclt hcmem
  exact le_iSup_of_le ⟨n, c, hclt, hcmem⟩ le_rfl

/-- The variation of a process whose paths are continuous within `s` at every point of `s`, over
the times in a set `s`, is measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt [OrderTopology ι]
    [SeparableSpace ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i)) (hcont : ∀ ω, ContinuousOn (X · ω) s) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, htc, ht⟩ := exists_countable_dense s
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense ht (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

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

/-- A point of a subset `s` is isolated on the right in the subspace `↥s` exactly when it is
isolated on the right within `s`. -/
theorem nhdsGT_subtype_eq_bot_iff {s : Set ι} {x : s} :
    𝓝[>] x = ⊥ ↔ 𝓝[s ∩ Ioi x.1] x.1 = ⊥ := by
  have : ((↑) : s → ι) ⁻¹' Ioi x.1 = Ioi x := rfl
  rw [← this, nhdsWithin_subtype_eq_bot_iff, nhdsWithin, inf_assoc, inf_principal, inter_comm,
    ← nhdsWithin]

/-- The variation of a function that is right-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the right. -/
theorem eVariationOn_eq_comp_val_of_dense_Ioi [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[>] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Ioi x) x) :
    eVariationOn f s = eVariationOn f t := by
  refine le_antisymm ?_ (eVariationOn.mono f (Subtype.coe_image_subset s t))
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_
  -- clamp the partition so it is defined on all of `ℕ`, then lift it into the subspace `↥s`
  set v : ℕ → ι := fun i ↦ u (min i n) with hvdef
  have hvs : ∀ i, v i ∈ s := fun i ↦ hus _ (min_le_right i n)
  set p : ℕ → s := fun i ↦ ⟨v i, hvs i⟩ with hpdef
  have hvu : ∀ i ≤ n, v i = u i := fun i hi ↦ by rw [hvdef]; simp [min_eq_left hi]
  have hplt : ∀ i, i < n → p i < p (i + 1) := fun i hi ↦ by
    have : v i < v (i + 1) := by
      rw [hvu i hi.le, hvu (i + 1) hi]
      exact hu (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega)
    exact this
  -- right-continuity of `f`, transported into the subspace as continuity within `Ici (p j)`
  have hcwa : ∀ j, Tendsto (fun x : s ↦ f x) (𝓝[Ici (p j)] (p j)) (𝓝 (f (v j))) := fun j ↦ by
    have hset : s ∩ Ici (v j) = insert (v j) (s ∩ Ioi (v j)) := by
      ext y
      simp only [mem_inter_iff, mem_Ici, mem_insert_iff, mem_Ioi]
      constructor
      · rintro ⟨hys, hle⟩
        rcases hle.lt_or_eq with h | h
        · exact Or.inr ⟨hys, h⟩
        · exact Or.inl h.symm
      · rintro (rfl | ⟨hys, hlt⟩)
        · exact ⟨hvs j, le_rfl⟩
        · exact ⟨hys, hlt.le⟩
    have h1 : ContinuousWithinAt f (s ∩ Ici (v j)) (v j) := by
      rw [hset, continuousWithinAt_insert_self]; exact hf (v j) (hvs j)
    have hval : Tendsto (Subtype.val : s → ι) (𝓝[Ici (p j)] (p j)) (𝓝[s ∩ Ici (v j)] (v j)) :=
      continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin
        fun y hy ↦ ⟨y.2, Subtype.coe_le_coe.2 hy⟩
    exact Tendsto.comp h1 hval
  -- the product filter approaching every partition point from the right, through the dense set `t`
  set F : Filter (ℕ → s) := Filter.pi (fun i ↦ 𝓝[t ∩ Ici (p i)] (p i)) with hFdef
  haveI : F.NeBot := by
    rw [hFdef]
    refine pi_neBot.2 fun i ↦ ?_
    rw [← mem_closure_iff_nhdsWithin_neBot]
    by_cases hiso : 𝓝[>] (p i) = ⊥
    · exact subset_closure ⟨hts hiso, le_rfl⟩
    · rw [mem_closure_iff]
      intro U hU hpU
      haveI : (𝓝[Ioi (p i)] (p i)).NeBot := ⟨hiso⟩
      have hne : (U ∩ Ioi (p i)).Nonempty :=
        Filter.nonempty_of_mem (inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hpU))
          self_mem_nhdsWithin)
      obtain ⟨w, hwt, hwm⟩ := ht.exists_mem_open (hU.inter isOpen_Ioi) hne
      exact ⟨w, hwm.1, hwt, hwm.2.le⟩
  have hev : ∀ j, Tendsto (fun c : ℕ → s ↦ c j) F (𝓝[t ∩ Ici (p j)] (p j)) := fun j ↦
    tendsto_eval_pi _ j
  have hev' : ∀ j, Tendsto (fun c : ℕ → s ↦ c j) F (𝓝 (p j)) := fun j ↦
    (hev j).mono_right nhdsWithin_le_nhds
  let g : (ℕ → s) → ℝ≥0∞ := fun a ↦ ∑ x ∈ Finset.range n, edist (f (a (x + 1))) (f (a x))
  have htend : Tendsto g F (𝓝 (∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)))) := by
    rw [show (∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)))
        = ∑ x ∈ Finset.range n, edist (f (v (x + 1))) (f (v x)) from
      Finset.sum_congr rfl fun x hx ↦ by
        rw [hvu x (Finset.mem_range.1 hx).le, hvu (x + 1) (Finset.mem_range.1 hx)]]
    refine tendsto_finsetSum _ fun x _ ↦ Tendsto.edist ?_ ?_
    · exact (hcwa (x + 1)).comp ((hev (x + 1)).mono_right (nhdsWithin_mono _ inter_subset_right))
    · exact (hcwa x).comp ((hev x).mono_right (nhdsWithin_mono _ inter_subset_right))
  refine le_of_tendsto htend ?_
  -- eventually the approximants lie in `t` and stay strictly increasing along the partition
  have hmem : ∀ᶠ c in F, ∀ i : Fin (n + 1), (c i.1 : s) ∈ t :=
    eventually_all.2 fun i ↦
      (hev i.1).eventually (mem_of_superset self_mem_nhdsWithin inter_subset_left)
  have hlt : ∀ᶠ c in F, ∀ i : Fin n, (c i.1 : s) < c (i.1 + 1) :=
    eventually_all.2 fun i ↦ ((hev' i.1).prodMk_nhds (hev' (i.1 + 1))).eventually
      ((isOpen_lt continuous_fst continuous_snd).eventually_mem (hplt i.1 i.2))
  filter_upwards [hmem, hlt] with c hcmem hclt
  simp only [g]
  refine eVariationOn.sum_le_of_monotoneOn_Iic (u := fun i ↦ (c i : ι)) ?_ ?_
  · refine (strictMonoOn_of_lt_succ ordConnected_Iic fun a _ _ hsa ↦ ?_).monotoneOn
    exact Subtype.coe_lt_coe.2 (hclt ⟨a, by simpa using hsa⟩)
  · exact fun i hi ↦ ⟨c i, hcmem ⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩

/-- The variation of a process with right-continuous paths over the times in a set `s` is
measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt_Ioi [OrderTopology ι]
    [SecondCountableTopology ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Ioi i) i) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  obtain ⟨t, ht, htc, hts⟩ : ∃ t : Set s, Dense t ∧ t.Countable ∧ {x : s | 𝓝[>] x = ⊥} ⊆ t := by
    obtain ⟨d, hdc, hdd⟩ := exists_countable_dense s
    have hsub : {x : s | 𝓝[>] x = ⊥} ⊆ Subtype.val ⁻¹' {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥} :=
      fun x hx ↦ ⟨x.2, nhdsGT_subtype_eq_bot_iff.1 hx⟩
    have hisoc : {x : s | 𝓝[>] x = ⊥}.Countable :=
      ((countable_setOf_isolated_right_within (s := s)).preimage Subtype.val_injective).mono hsub
    exact ⟨d ∪ {x : s | 𝓝[>] x = ⊥}, hdd.mono subset_union_left, hdc.union hisoc,
      subset_union_right⟩
  simp only [fun ω ↦ eVariationOn_eq_comp_val_of_dense_Ioi ht hts (hcont ω)]
  exact measurable_eVariationOn_of_countable (htc.image _) fun i hi ↦ hX i
    (Subtype.coe_image_subset s t hi)

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

/-- The variation of a function that is left-continuous within `s` at every point of `s` can be
computed using only points of a dense subset `t` of `s`, provided `t` contains every point of `s`
that is isolated on the left. -/
theorem eVariationOn_eq_comp_val_of_dense_Iio [OrderTopology ι] {s : Set ι} {t : Set s}
    (ht : Dense t) (hts : {x : s | 𝓝[<] x = ⊥} ⊆ t) {f : ι → E}
    (hf : ∀ x ∈ s, ContinuousWithinAt f (s ∩ Iio x) x) :
    eVariationOn f s = eVariationOn f t := by
  rw [← eVariationOn.comp_ofDual, ← eVariationOn.comp_ofDual f t,
    eVariationOn_eq_comp_val_of_dense_Ioi (s := OrderDual.ofDual ⁻¹' s)
    (f := f ∘ OrderDual.ofDual) ht hts hf]
  congr

/-- The variation of a process with left-continuous paths over the times in a set `s` is
measurable. -/
theorem measurable_eVariationOn_of_continuousWithinAt_Iio [OrderTopology ι]
    [SecondCountableTopology ι] {m : MeasurableSpace Ω} {s : Set ι} {X : ι → Ω → E}
    (hX : ∀ i ∈ s, StronglyMeasurable[m] (X i))
    (hcont : ∀ ω, ∀ i ∈ s, ContinuousWithinAt (X · ω) (s ∩ Iio i) i) :
    Measurable[m] fun ω ↦ eVariationOn (X · ω) s := by
  have hdual : ∀ ω, eVariationOn (fun i ↦ X (OrderDual.ofDual i) ω) (OrderDual.ofDual ⁻¹' s)
    = eVariationOn (X · ω) s := fun ω ↦ eVariationOn.comp_ofDual (X · ω) s
  simpa [hdual] using measurable_eVariationOn_of_continuousWithinAt_Ioi
    (s := OrderDual.ofDual ⁻¹' s) (X := fun i ↦ X (OrderDual.ofDual i)) hX hcont

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
