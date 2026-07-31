/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.StochasticIntegral.StochasticInterval

@[expose] public section

open ProbabilityTheory ENNReal Filter
open scoped Topology

namespace MeasureTheory

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
  {τ σ : Ω → WithTop ι} {A : Set Ω}

section Preorder

variable [Preorder ι] {𝓕 : Filtration ι mΩ}

lemma isStoppingTime_piecewise [DecidablePred (· ∈ A)]
    (hτ : IsStoppingTime 𝓕 τ) (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsStoppingTime 𝓕 (A.piecewise τ (fun _ ↦ ⊤)) := by
  intro t
  convert ((hτ.measurableSet A).1 hA).2 t
  ext ω
  simp only [Set.piecewise, Set.mem_ofPred_eq, Set.mem_inter_iff]
  split_ifs <;> simp_all

variable [OrderBot ι]

@[instance_reducible]
def leftMeasurableSpace (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : MeasurableSpace Ω :=
  𝓕 ⊥ ⊔ (MeasurableSpace.generateFrom {s | ∃ A t, MeasurableSet[𝓕 t] A ∧ s = A ∩ {ω | t < τ ω}})

def IsPredictableTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : Prop :=
  MeasurableSet[𝓕.predictable] (stochIco τ (fun _ ↦ ⊤))

lemma IsPredictableTime.isStoppingTime (hτ : IsPredictableTime 𝓕 τ) :
    IsStoppingTime 𝓕 τ := by
  intro t
  have : {ω | τ ω ≤ t} = (Prod.mk t) ⁻¹' (stochIco τ (fun _ ↦ ⊤)) := by ext; simp
  rw [this]
  convert hτ.preimage (measurable_generateFrom (fun A hA ↦ ?_))
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hA
  classical
  obtain ⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩ := hA <;> rw [Set.mk_preimage_prod_right_eq_if]
  · split_ifs
    · grind
    · convert MeasurableSet.empty
  · split_ifs with h
    · exact (𝓕.mono h.le) A hA
    · convert MeasurableSet.empty

structure IsAccessibleTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : Prop where
  isStoppingTime : IsStoppingTime 𝓕 τ
  stochIco_subset : ∃ σ : ℕ → Ω → WithTop ι,
    (∀ n, IsPredictableTime 𝓕 (σ n)) ∧ stochGraph τ ⊆ ⋃ n, stochGraph (σ n)

structure IsInacessibleTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) (P : Measure Ω) : Prop where
  isStoppingTime : IsStoppingTime 𝓕 τ
  measure_eq_lt_top_eq_zero : ∀ σ, IsPredictableTime 𝓕 σ → P {ω | τ ω = σ ω ∧ σ ω < ⊤} = 0

end Preorder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ}

lemma test [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hσ : IsStoppingTime 𝓕 σ) (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[leftMeasurableSpace 𝓕 τ] (A ∩ {ω | σ ω < τ ω}) := by
  obtain ⟨s, cs, ds⟩ := TopologicalSpace.exists_countable_dense ι
  let t := s ∪ {x | 𝓝[>] x = ⊥}
  have ct : t.Countable := cs.union countable_setOfPred_isolated_right
  have dt : Dense t := ds.mono (by grind)
  have : A ∩ {ω | σ ω < τ ω} = ⋃ x ∈ t, A ∩ {ω | σ ω ≤ x} ∩ {ω | x < τ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_left,
      exists_prop]
    refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨i, ⟨hi1, hi2⟩, hi3, hi4⟩ ↦ ⟨hi1, hi2.trans_lt hi4⟩⟩
    cases h' : σ ω with
    | top => simp_all
    | coe i =>
      obtain h | h := (𝓝[>] i).eq_or_neBot
      · exact ⟨i, ⟨h1, le_rfl⟩, by grind, by rwa [← h']⟩
      · cases h'' : τ ω with
        | top =>
          have : (Set.Ioi i).Nonempty := nonempty_of_mem (f := 𝓝[>] i)
            self_mem_nhdsWithin
          obtain ⟨j, hj1, hj2⟩ := dt.exists_mem_open isOpen_Ioi this
          refine ⟨j, ⟨h1, ?_⟩, hj1, by simp⟩
          simpa using hj2.le
        | coe j =>
          have : (Set.Ioo i j).Nonempty := by
            convert nonempty_of_mem (f := 𝓝[>] i)
              (inter_mem_nhdsWithin _ (t := Set.Iio j) ?_)
            · rw [Set.Ioi_inter_Iio]
            · apply Iio_mem_nhds
              rwa [← WithTop.coe_lt_coe, ← h', ← h'']
          obtain ⟨k, hk1, hk2⟩ := dt.exists_mem_open isOpen_Ioo this
          refine ⟨k, ⟨h1, by simpa using hk2.1.le⟩, hk1, by simpa using hk2.2⟩
  rw [this]
  refine .biUnion ct fun x _ ↦ MeasurableSpace.measurableSet_generateFrom ?_
  simp only [Set.sup_eq_union, Set.mem_union, Set.mem_ofPred_eq]
  right
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨A ∩ {ω | σ ω ≤ x}, x, ((hσ.measurableSet A).1 hA).2 x, rfl⟩

theorem Set.iInter_prod {α β ι : Type*} {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (⋂ (i : ι), t i) ×ˢ s = ⋂ (i : ι), t i ×ˢ s := by
  ext
  simp only [Set.mem_prod, Set.mem_iInter]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2⟩, fun h ↦ ⟨fun i ↦ (h i).1, (h Classical.ofNonempty).2⟩⟩

lemma IsPredictableTime.const [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (𝓕 : Filtration ι mΩ) (t : WithTop ι) :
    IsPredictableTime 𝓕 (fun _ ↦ t) := by
  rw [IsPredictableTime]
  cases t with
  | top =>
    convert MeasurableSet.empty
    ext; simp [stochIco]
  | coe t =>
    have : (stochIco (fun _ ↦ (t : WithTop ι)) (fun _ ↦ ⊤) : Set (ι × Ω)) =
      (Set.Ici t) ×ˢ Set.univ := by ext; simp [stochIco]
    rw [this]
    by_cases h : Order.IsSuccLimit t
    · obtain ⟨u, mu, hu1, hu2, -⟩ := h.isLUB_Iio.exists_seq_strictMono_tendsto_of_notMem (by simp)
        h.nonempty_Iio
      have : Set.Ici t = ⋂ n, Set.Ioi (u n) := by
        ext s
        simp only [Set.mem_Ici, Set.mem_iInter, Set.mem_Ioi]
        exact ⟨fun h n ↦ (hu1 n).trans_le h, fun h ↦ le_of_tendsto' hu2 (fun n ↦ (h n).le)⟩
      rw [this, Set.iInter_prod]
      exact .iInter (fun _ ↦ measurableSet_predictable_Ioi_prod .univ)
    rw [Order.isSuccLimit_iff, Order.IsSuccPrelimit] at h
    push +distrib Not at h
    obtain h | h := h
    · convert MeasurableSet.univ
      grind [IsMin]
    · obtain ⟨s, hs⟩ := h
      convert measurableSet_predictable_Ioi_prod (i := s) .univ
      grind [CovBy]

variable {mΩ} {P : Measure Ω}

lemma IsStoppingTime.measurableSet_lt_top (hτ : IsStoppingTime 𝓕 τ) [TopologicalSpace ι]
    [OrderTopology ι] [TopologicalSpace.SeparableSpace ι] :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < ⊤} := by
  obtain ⟨u, hu⟩ := (atTop : Filter ι).exists_seq_tendsto
  have : {ω | τ ω < ⊤} = ⋃ n, {ω | τ ω ≤ u n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
    · contrapose! h
      rw [top_le_iff, WithTop.eq_top_iff_forall_gt]
      intro t
      obtain ⟨n, hn⟩ := (hu.eventually (eventually_ge_atTop t)).exists
      grw [WithTop.coe_le_coe.2 hn, h]
    · exact hi.trans_lt (by simp)
  rw [this]
  exact .iUnion fun n ↦ hτ.measurableSet_le' (u n)

/-- For a stopping time `τ`, there exists a set `A` that is `𝓕 τ`-measurable and such that
`τ_A` is accessible while `τ_Aᶜ` is inaccessible, where `τ_A` is the stopping time which
coincides with `τ` over `A` and is infinite elsewhere. -/
theorem IsStoppingTime.decompositon
  [∀ ω (s : Set Ω), Decidable (ω ∈ s)] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [IsFiniteMeasure P] (hτ : IsStoppingTime 𝓕 τ) :
    ∃ A, MeasurableSet[hτ.measurableSpace] A ∧ A ⊆ {ω | τ ω < ⊤} ∧
      IsAccessibleTime 𝓕 (A.piecewise τ (fun _ ↦ ⊤)) ∧
      IsInacessibleTime 𝓕 (Aᶜ.piecewise τ (fun _ ↦ ⊤)) P := by
  classical
  let S := {x : ℝ≥0∞ | ∃ σ : ℕ → Ω → WithTop ι, (∀ n, IsPredictableTime 𝓕 (σ n)) ∧
    x = P (⋃ n, {ω | τ ω = σ n ω ∧ σ n ω < ⊤})}
  have hS : S.Nonempty := ⟨_, ⟨fun _ _ ↦ ⊥, fun _ ↦ .const 𝓕 ⊥, rfl⟩⟩
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_seq_tendsto_sSup hS (OrderTop.bddAbove S)
  simp only [Set.mem_ofPred_eq, S] at hu3
  choose σ hσ1 hσ2 using hu3
  let A n k := {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤}
  have mA n k : MeasurableSet[hτ.measurableSpace] (A n k) := by
    have : {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤} = {ω | τ ω = σ n k ω ∧ τ ω < ⊤} := by grind
    simp_rw [A, this, Set.ofPred_and]
    exact (hτ.measurableSet_eq_stopping_time (hσ1 n k).isStoppingTime).inter
      hτ.measurableSet_lt_top
  let B := ⋃ n, ⋃ k, A n k
  have mB : MeasurableSet[hτ.measurableSpace] B := .iUnion fun n ↦ .iUnion fun k ↦ (mA n k)
  refine ⟨B, mB, by simp +contextual [A, B], ⟨isStoppingTime_piecewise hτ mB, ?_⟩,
    ⟨isStoppingTime_piecewise hτ mB.compl, fun π hπ ↦ ?_⟩⟩
  · obtain ⟨φ, hφ⟩ := exists_surjective_nat (ℕ × ℕ)
    refine ⟨fun n ↦ σ (φ n).1 (φ n).2, fun n ↦ hσ1 _ _, fun tω h ↦ ?_⟩
    simp only [stochGraph, Set.piecewise, Set.mem_iUnion, Set.mem_ofPred_eq, B, A] at h ⊢
    split_ifs at h with h'
    · obtain ⟨n, k, h1, h2⟩ := h'
      obtain ⟨i, hi⟩ := hφ (n, k)
      use i
      simp_all
    · contradiction
  · have : {ω | Bᶜ.piecewise τ (fun x ↦ ⊤) ω = π ω ∧ π ω < ⊤} =
        (Bᶜ ∩ {ω | τ ω = π ω ∧ π ω < ⊤}) := by
      ext ω
      simp only [Set.piecewise, Set.compl_iUnion, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_ofPred_eq, not_and, not_lt, top_le_iff, Set.mem_inter_iff, B, A]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · split_ifs at h with h'
        · exact ⟨fun k n h'' ↦ h' _ _ h'', h.1, h.2⟩
        · grind
      · split_ifs with h'
        · exact ⟨h.2.1, h.2.2⟩
        · grind
    rw [this]
    by_contra!
    have key n : u n + P (Bᶜ ∩ {ω | τ ω = π ω ∧ π ω < ⊤}) ≤ sSup S := by
      refine le_trans (b := u n + P ((⋃ k, A n k)ᶜ ∩ {ω | τ ω = π ω ∧ π ω < ⊤})) ?_ ?_
      · gcongr 4 with
        exact Set.subset_iUnion (fun m ↦ ⋃ k, {ω | τ ω = σ m k ω ∧ σ m k ω < ⊤}) n
      refine le_sSup_of_le (b := P ((⋃ k, A n k) ∪ {ω | τ ω = π ω ∧ π ω < ⊤})) ?_ ?_
      · obtain ⟨φ, hφ⟩ := exists_surjective_nat (ℕ ⊕ Unit)
        refine ⟨fun k ↦ Sum.elim (σ n) (fun _ ↦ π) (φ k), fun k ↦ ?_, ?_⟩
        · simp only
          cases φ k with
          | inl l => exact hσ1 n l
          | inr _ => exact hπ
        congr with ω
        simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, A]
        constructor
        · rintro (⟨i, hi1, hi2⟩ | ⟨h1, h2⟩)
          · obtain ⟨j, hj⟩ := hφ (.inl i)
            use j
            simp_all
          · obtain ⟨j, hj⟩ := hφ (.inr ())
            use j
            simp_all
        · rintro ⟨i, hi1, hi2⟩
          cases hi : φ i with
          | inl j =>
            left
            use j
            simp_all
          | inr _ =>
            right
            simp_all
      · grw [hσ2, ← measure_union, measure_mono]
        · grind
        · grind
        refine .inter (.compl (.iUnion (fun k ↦ hτ.measurableSpace_le _ (mA n k)))) ?_
        · rw [Set.ofPred_and]
          refine (hτ.measurableSpace_le _
              (hτ.measurableSet_eq_stopping_time hπ.isStoppingTime)).inter ?_
          exact measurableSet_Iio.preimage hπ.isStoppingTime.measurable'
    have final := le_of_tendsto' (hu2.add_const _) key
    suffices sSup S < sSup S by grind
    calc
    sSup S
      < sSup S + P (Bᶜ ∩ {ω | τ ω = π ω ∧ π ω < ⊤}) := by
        grw [← pos_of_ne_zero this, add_zero]
        apply ne_top_of_le_ne_top (b := P Set.univ)
        · simp
        · rw [sSup_le_iff]
          rintro - ⟨_, _, rfl⟩
          exact measure_mono (by simp)
    _ ≤ sSup S := final

def IsThinSet (s : Set (ι × Ω)) (𝓕 : Filtration ι mΩ) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, (∀ n, IsStoppingTime 𝓕 (τ n)) ∧ s = ⋃ n, stochGraph (τ n)

lemma IsThinSet.mono {s t : Set (ι × Ω)} (ht : IsThinSet t 𝓕) (hst : s ⊆ t)
    [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [BorelSpace ι]
    (hs' : IsStronglyProgressive 𝓕 (fun t ω ↦ s.indicator (1 : ι × Ω → ℝ) (t, ω))) :
    IsThinSet s 𝓕 := by
  obtain ⟨τ, hτ, rfl⟩ := ht
  let L n : Set Ω := {ω | ∃ (h : τ n ω ≠ ⊤), ((τ n ω).untop h, ω) ∈ s}
  classical
  refine ⟨fun n ↦ (L n).piecewise (τ n) (fun _ ↦ ⊤), fun n ↦ isStoppingTime_piecewise (hτ n) ?_, ?_⟩
  · rw [← measurable_indicator_const_iff (b := (1 : ℝ))]
    have : (L n).indicator (fun _ ↦ (1 : ℝ)) =
        {ω | τ n ω ≠ ⊤}.indicator
          (stoppedValue (fun u ω ↦ s.indicator (1 : ι × Ω → ℝ) (u, ω)) (τ n)) := by
      ext ω
      cases h : τ n ω with
      | top => simp [L, h]
      | coe u => simp [h, Set.indicator, L, stoppedValue]
    rw [this]
    refine .indicator ?_ ((measurableSet_singleton ⊤).preimage (hτ n).measurable).compl
    exact measurable_stoppedValue hs' (hτ n)
  · ext uω
    simp only [stochGraph, Set.piecewise, ne_eq, Set.mem_ofPred_eq, Set.mem_iUnion, L]
    refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
    · have := hst h
      simp only [stochGraph, Set.mem_iUnion, Set.mem_ofPred_eq] at this
      obtain ⟨n, hn⟩ := this
      refine ⟨n, ?_⟩
      rw [if_pos, hn]
      rw [← hn]
      simpa
    split_ifs at hn with h
    · obtain ⟨h1, h2⟩ := h
      rw! [← hn, WithTop.untop_coe] at h2
      exact h2
    · contradiction

end MeasureTheory
