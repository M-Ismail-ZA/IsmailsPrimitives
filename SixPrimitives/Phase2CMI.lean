import SixPrimitives.Phase0
import SixPrimitives.Phase1
import SixPrimitives.Phase2
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Ismail's Primitives — Phase 2: Conditional Mutual Information -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SixPrimitives.Phase2

-- LOCAL ENTROPY DEFINITIONS

section EntropyDefs

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def condEntropy
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (m : MeasurableSpace Ω) : ℝ :=
  ∫ ω, ∑ x : α,
    -(ℙ[(X ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] ω *
      Real.log (ℙ[(X ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] ω)) ∂ℙ

noncomputable def entropy
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) : ℝ :=
  condEntropy X ⊥

end EntropyDefs

-- PROPERTIES OF condEntropy

section CondEntropyProps

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma condEntropy_nonneg
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X_rv : Ω → α) (m : MeasurableSpace Ω) :
    0 ≤ condEntropy X_rv m := by
  simp only [condEntropy]
  apply integral_nonneg_of_ae
  by_cases hm : m ≤ MeasureSpace.toMeasurableSpace
  · have h_nn : ∀ x : α, 0 ≤ᵐ[ℙ]
        ℙ[(X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] :=
      fun x => condExp_nonneg (Eventually.of_forall
        (Set.indicator_nonneg (fun _ _ => zero_le_one)))
    have h_le : ∀ x : α,
        ℙ[(X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[ℙ] 1 := fun x => by
      by_cases hint : Integrable ((X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ))) ℙ
      · have hmono : ℙ[(X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[ℙ]
                     ℙ[fun _ => (1 : ℝ) | m] :=
          condExp_mono hint (integrable_const 1)
            (Eventually.of_forall (fun ω => by
              classical
              simp only [Set.indicator_apply]
              split_ifs <;> norm_num))
        filter_upwards [hmono] with ω hω
        simp only [condExp_const hm] at hω
        exact hω
      · rw [condExp_of_not_integrable hint]
        exact Eventually.of_forall fun _ => zero_le_one
    filter_upwards [Filter.eventually_all.mpr (fun x => (h_nn x).and (h_le x))]
        with ω hω
    apply Finset.sum_nonneg
    intro x _
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (hω x).1 (Real.log_nonpos (hω x).1 (hω x).2))
  · apply Eventually.of_forall
    intro ω
    simp only [condExp_of_not_le hm, Pi.zero_apply, Real.log_zero,
               mul_zero, neg_zero, Finset.sum_const_zero, le_refl]

lemma condEntropy_anti
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X_rv : Ω → α) (hX : Measurable X_rv)
    {m₁ m₂ : MeasurableSpace Ω} (h_le : m₁ ≤ m₂) :
    condEntropy X_rv m₂ ≤ condEntropy X_rv m₁ := by
  by_cases hm₂ : m₂ ≤ MeasureSpace.toMeasurableSpace
  swap
  · simp only [condEntropy, condExp_of_not_le hm₂, Pi.zero_apply, Real.log_zero,
               mul_zero, neg_zero, Finset.sum_const_zero, integral_zero]
    exact condEntropy_nonneg X_rv m₁
  have hm₁ : m₁ ≤ MeasureSpace.toMeasurableSpace := h_le.trans hm₂
  simp only [condEntropy]
  simp_rw [show ∀ (t : ℝ), -(t * Real.log t) = Real.negMulLog t from
    fun t => by simp [Real.negMulLog, neg_mul]]
  have h_nlint : ∀ (m : MeasurableSpace Ω), m ≤ MeasureSpace.toMeasurableSpace →
      ∀ x : α, Integrable
        (fun ω => Real.negMulLog (ℙ[(X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m] ω)) ℙ := by
    intro m hm x
    set f := (X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) with hf_def
    have h_ind_int : Integrable f ℙ :=
      (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton x))
    have h_nn : 0 ≤ᵐ[ℙ] ℙ[f | m] :=
      condExp_nonneg (Eventually.of_forall (Set.indicator_nonneg (fun _ _ => zero_le_one)))
    have h_le_one : ℙ[f | m] ≤ᵐ[ℙ] fun _ => (1 : ℝ) := by
      have hmono : ℙ[f | m] ≤ᵐ[ℙ] ℙ[fun _ => (1 : ℝ) | m] :=
        condExp_mono h_ind_int (integrable_const (1 : ℝ))
          (Eventually.of_forall (fun ω => by
            classical
            simp [f, Set.indicator_apply]
            split_ifs <;> norm_num))
      have hconst : ℙ[fun _ : Ω => (1 : ℝ) | m] =ᵐ[ℙ] fun _ => (1 : ℝ) :=
        ae_of_all ℙ (fun ω => congr_fun (condExp_const hm (1 : ℝ)) ω)
      filter_upwards [hmono, hconst] with ω hω hconst
      exact le_of_le_of_eq hω hconst
    have hInt : Integrable (ℙ[f | m]) ℙ := integrable_condExp
    have h_aestrong := hInt.aestronglyMeasurable
    have h_aestrong' := Real.continuous_negMulLog.comp_aestronglyMeasurable h_aestrong
    have h_le_one_ae : ∀ᵐ ω ∂ℙ, ‖Real.negMulLog (ℙ[f | m] ω)‖ ≤ ‖(1 : ℝ)‖ := by
      filter_upwards [h_nn, h_le_one] with ω h0 h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
      rw [abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
      apply le_trans (Real.negMulLog_le_one_sub_self h0)
      exact sub_le_self (1 : ℝ) h0
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) ℙ := integrable_const (1 : ℝ)
    exact hconst.mono h_aestrong' h_le_one_ae
  rw [integral_finsetSum Finset.univ (fun x _ => h_nlint m₂ hm₂ x),
      integral_finsetSum Finset.univ (fun x _ => h_nlint m₁ hm₁ x)]
  apply Finset.sum_le_sum
  intro x _
  set f := (X_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) with hf_def
  have h_ind_int : Integrable f ℙ :=
    (integrable_const 1).indicator (hX (measurableSet_singleton x))
  have h_nn : ∀ᵐ ω ∂ℙ, ℙ[f | m₂] ω ∈ Set.Ici 0 :=
    (condExp_nonneg (Eventually.of_forall (Set.indicator_nonneg (fun _ _ => zero_le_one)))).mono
      (fun ω h => Set.mem_Ici.mpr h)
  have hJensen :
      ℙ[Real.negMulLog ∘ ℙ[f | m₂] | m₁]
      ≤ᵐ[ℙ]
      Real.negMulLog ∘ ℙ[ℙ[f | m₂] | m₁] :=
    ConcaveOn.condExp_map_le hm₁ Real.concaveOn_negMulLog
      Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
      h_nn isClosed_Ici integrable_condExp (h_nlint m₂ hm₂ x)
  have hTower : ℙ[ℙ[f | m₂] | m₁] =ᵐ[ℙ] ℙ[f | m₁] :=
    condExp_condExp_of_le h_le hm₂
  have h_rhs_int : Integrable (fun ω => Real.negMulLog (ℙ[ℙ[f | m₂] | m₁] ω)) ℙ := by
    apply (h_nlint m₁ hm₁ x).congr
    filter_upwards [hTower] with ω h
    rw [h]
  calc
    ∫ ω, Real.negMulLog (ℙ[f | m₂] ω) ∂ℙ
        = ∫ ω, ℙ[Real.negMulLog ∘ ℙ[f | m₂] | m₁] ω ∂ℙ := by
      exact (integral_condExp hm₁).symm
    _ ≤ ∫ ω, Real.negMulLog (ℙ[ℙ[f | m₂] | m₁] ω) ∂ℙ := by
      refine integral_mono_ae integrable_condExp h_rhs_int hJensen
    _ = ∫ ω, Real.negMulLog (ℙ[f | m₁] ω) ∂ℙ := by
      exact integral_congr_ae (hTower.mono fun ω h => congrArg Real.negMulLog h)

lemma condEntropy_le_entropy
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X_rv : Ω → α) (hX : Measurable X_rv) (m : MeasurableSpace Ω) :
    condEntropy X_rv m ≤ entropy X_rv := by
  have h_bot : (⊥ : MeasurableSpace Ω) ≤ m := bot_le
  have h_anti := condEntropy_anti X_rv hX h_bot
  exact h_anti

lemma condEntropy_of_deterministic
    {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : α → β) (hf : Measurable f)
    (X_rv : Ω → α) (hX : Measurable X_rv)
    (ℱ : MeasurableSpace Ω)
    (h_le : MeasurableSpace.comap X_rv inferInstance ≤ ℱ) :
    condEntropy (f ∘ X_rv) ℱ = 0 := by
  by_cases hℱ : ℱ ≤ MeasureSpace.toMeasurableSpace
  swap
  · simp only [condEntropy, condExp_of_not_le hℱ, Pi.zero_apply, Real.log_zero, mul_zero, neg_zero, Finset.sum_const_zero, integral_zero]
  have h_int_y : ∀ y : β, Integrable (((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ => (1 : ℝ))) ℙ :=
    fun y => (integrable_const 1).indicator ((hf.comp hX) (measurableSet_singleton y))
  have h_sm_y : ∀ y : β, StronglyMeasurable[ℱ] (((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ : Ω => (1 : ℝ))) := by
    intro y
    letI : MeasurableSpace Ω := ℱ
    have hs : MeasurableSet ((f ∘ X_rv) ⁻¹' {y}) := by
      apply h_le
      exact ⟨f ⁻¹' {y}, hf (measurableSet_singleton y), rfl⟩
    exact Measurable.stronglyMeasurable (Measurable.indicator measurable_const hs)
  have hae : ∀ y : β, ℙ[((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) | ℱ] =ᵐ[ℙ] ((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) := by
    intro y
    have h_eq := condExp_of_stronglyMeasurable hℱ (h_sm_y y) (h_int_y y)
    exact Eventually.of_forall (congr_fun h_eq)
  simp only [condEntropy]
  simp_rw [show ∀ (t : ℝ), -(t * Real.log t) = Real.negMulLog t from fun t => by simp [Real.negMulLog, neg_mul]]
  have h_integrand_zero : ∀ᵐ ω ∂ℙ, ∑ x : β, Real.negMulLog (ℙ[((f ∘ X_rv) ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ℱ] ω) = 0 := by
    have hae_all : ∀ᵐ ω ∂ℙ, ∀ y : β, ℙ[((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) | ℱ] ω = ((f ∘ X_rv) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω := by
      rw [Filter.eventually_all]
      exact hae
    filter_upwards [hae_all] with ω hω
    apply Finset.sum_eq_zero
    intro y _
    rw [hω y]
    by_cases h : ω ∈ (f ∘ X_rv) ⁻¹' {y}
    · simp [Set.indicator, h, Real.negMulLog]
    · simp [Set.indicator, h, Real.negMulLog]
  calc
    ∫ (ω : Ω), ∑ (x : β), Real.negMulLog (ℙ[((f ∘ X_rv) ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ℱ] ω) ∂ℙ
    _ = ∫ (ω : Ω), (0 : ℝ) ∂ℙ := integral_congr_ae h_integrand_zero
    _ = 0 := integral_zero Ω ℝ

lemma condEntropy_le_compl_mul
    (X : Ω → Bool) (ℱ : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet E)
    (_h_meas_X : Measurable X)
    (h_zero_on_E : ∀ᵐ ω, ω ∈ E →
        condEntropy (fun ω' => X ω') ℱ = 0)
    (h_bound : condEntropy (fun ω' => X ω') ℱ ≤ Real.log 2) :
    condEntropy (fun ω' => X ω') ℱ ≤ (ℙ Eᶜ).toReal * Real.log 2 := by
  by_cases hℱ : ℱ ≤ MeasureSpace.toMeasurableSpace
  · have hE_ambient := hℱ E hE
    by_cases h_zero : condEntropy (fun ω' => X ω') ℱ = 0
    · rw [h_zero]
      apply mul_nonneg
      · exact ENNReal.toReal_nonneg
      · exact Real.log_nonneg (by norm_num)
    · have h_ae_not_E : ∀ᵐ ω, ω ∉ E := by
        filter_upwards [h_zero_on_E] with ω hω hωE
        exact h_zero (hω hωE)
      have h_PE_zero : ℙ E = 0 := by
        have h1 : ℙ {ω | ¬ (ω ∉ E)} = 0 := ae_iff.mp h_ae_not_E
        have h2 : {ω | ¬ (ω ∉ E)} = E := by ext; simp
        rwa [h2] at h1
      have hPEc : ℙ Eᶜ = 1 := by
        have h_union : ℙ (E ∪ Eᶜ) = ℙ E + ℙ Eᶜ :=
          measure_union disjoint_compl_right hE_ambient.compl
        have h_univ : ℙ (Set.univ : Set Ω) = 1 := measure_univ
        rw [Set.union_compl_self E] at h_union
        rw [h_union, h_PE_zero, zero_add] at h_univ
        exact h_univ
      rw [hPEc]
      rw [ENNReal.toReal_one, one_mul]
      exact h_bound
  · have h_zero : condEntropy (fun ω' => X ω') ℱ = 0 := by
      simp only [condEntropy, condExp_of_not_le hℱ, Pi.zero_apply, Real.log_zero,
                 mul_zero, neg_zero, Finset.sum_const_zero, integral_zero]
    rw [h_zero]
    apply mul_nonneg
    · exact ENNReal.toReal_nonneg
    · exact Real.log_nonneg (by norm_num)

end CondEntropyProps

-- CONDITIONAL ENTROPY CONGRUENCE

section CondEntropyCongr

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma ae_eq_preimage_of_ae_eq
    {β : Type*} [MeasurableSpace β]
    {f g : Ω → β} (h : f =ᵐ[(ℙ : Measure Ω)] g) (s : Set β) :
    (f ⁻¹' s : Set Ω) =ᵐ[(ℙ : Measure Ω)] (g ⁻¹' s : Set Ω) := by
  filter_upwards [h] with ω hω
  have hgoal : (f ω ∈ s) ↔ (g ω ∈ s) := by rw [hω]
  simpa [Set.mem_preimage] using hgoal

private lemma condExp_comap_ae_eq_of_ae_eq
    {β : Type*} [MeasurableSpace β]
    {f g : Ω → β} (hf : Measurable f) (hg : Measurable g)
    (h_ae : f =ᵐ[(ℙ : Measure Ω)] g)
    {φ : Ω → ℝ} (hφ : Integrable φ (ℙ : Measure Ω)) :
    (ℙ : Measure Ω)[φ | MeasurableSpace.comap f inferInstance] =ᵐ[(ℙ : Measure Ω)]
      (ℙ : Measure Ω)[φ | MeasurableSpace.comap g inferInstance] := by
  have hm_f : MeasurableSpace.comap f inferInstance ≤ MeasureSpace.toMeasurableSpace := by
    rintro s ⟨t, ht, rfl⟩; exact hf ht
  have hm_g : MeasurableSpace.comap g inferInstance ≤ MeasureSpace.toMeasurableSpace := by
    rintro s ⟨t, ht, rfl⟩; exact hg ht
  have h_pre : ∀ t : Set β, MeasurableSet t →
      (f ⁻¹' t : Set Ω) =ᵐ[(ℙ : Measure Ω)] (g ⁻¹' t : Set Ω) :=
    fun t _ => ae_eq_preimage_of_ae_eq h_ae t
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_g hφ
      (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
  · intro A hA _
    obtain ⟨t, ht, rfl⟩ := hA
    rw [setIntegral_congr_set (h_pre t ht).symm,
        setIntegral_condExp hm_f hφ ⟨t, ht, rfl⟩,
        setIntegral_congr_set (h_pre t ht)]
  · have h_strong_f : StronglyMeasurable[MeasurableSpace.comap f inferInstance]
      (ℙ[φ | MeasurableSpace.comap f inferInstance]) := stronglyMeasurable_condExp
    obtain ⟨ψ, hψ_sm, hψ_eq⟩ := h_strong_f.exists_eq_measurable_comp
    have h_factor_ae : ψ ∘ g =ᵐ[(ℙ : Measure Ω)] ℙ[φ | MeasurableSpace.comap f inferInstance] := by
      calc
        ψ ∘ g =ᵐ[(ℙ : Measure Ω)] ψ ∘ f := h_ae.mono fun ω h => congr_arg ψ h.symm
        _ = ℙ[φ | MeasurableSpace.comap f inferInstance] := hψ_eq.symm
    have h_ae_strongly' : AEStronglyMeasurable[MeasurableSpace.comap g inferInstance] (ψ ∘ g) ℙ :=
      (hψ_sm.comp_measurable (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable
    exact h_ae_strongly'.congr h_factor_ae

lemma condEntropy_congr_ae
    {β α : Type*} [MeasurableSpace β]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X)
    {f g : Ω → β} (hf : Measurable f) (hg : Measurable g)
    (h_ae : f =ᵐ[(ℙ : Measure Ω)] g) :
    condEntropy X (MeasurableSpace.comap f inferInstance) =
      condEntropy X (MeasurableSpace.comap g inferInstance) := by
  simp only [condEntropy]
  apply integral_congr_ae
  have hkey : ∀ x : α,
      (ℙ : Measure Ω)[((X ⁻¹' {x}).indicator fun _ => (1 : ℝ)) |
          MeasurableSpace.comap f inferInstance] =ᵐ[(ℙ : Measure Ω)]
      (ℙ : Measure Ω)[((X ⁻¹' {x}).indicator fun _ => (1 : ℝ)) |
          MeasurableSpace.comap g inferInstance] :=
    fun x => condExp_comap_ae_eq_of_ae_eq hf hg h_ae
      ((integrable_const 1).indicator (hX (measurableSet_singleton x)))
  have hkey_all : ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ x : α,
      (ℙ : Measure Ω)[((X ⁻¹' {x}).indicator fun _ => (1 : ℝ)) |
          MeasurableSpace.comap f inferInstance] ω =
      (ℙ : Measure Ω)[((X ⁻¹' {x}).indicator fun _ => (1 : ℝ)) |
          MeasurableSpace.comap g inferInstance] ω := by
    rw [Filter.eventually_all]; exact hkey
  filter_upwards [hkey_all] with ω hω
  apply Finset.sum_congr rfl; intro x _; rw [hω x]

end CondEntropyCongr

-- CONDITIONAL MUTUAL INFORMATION

section ConditionalMutualInformation

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def condMutualInfo
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (X_rv : Ω → X) (Y_rv : Ω → Y) (ℱ : MeasurableSpace Ω) : ℝ :=
  condEntropy X_rv ℱ -
    condEntropy X_rv (MeasurableSpace.comap Y_rv inferInstance ⊔ ℱ)

-- BASIC LEMMAS

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma condMutualInfo_eq_entropy_diff
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (X_rv : Ω → X) (Y_rv : Ω → Y) (ℱ : MeasurableSpace Ω) :
    condMutualInfo X_rv Y_rv ℱ =
      condEntropy X_rv ℱ -
      condEntropy X_rv (MeasurableSpace.comap Y_rv inferInstance ⊔ ℱ) := rfl

lemma condMutualInfo_nonneg
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (X_rv : Ω → X) (Y_rv : Ω → Y)
    (hX : Measurable X_rv) (_hY : Measurable Y_rv)
    (ℱ : MeasurableSpace Ω) :
    0 ≤ condMutualInfo X_rv Y_rv ℱ := by
  rw [condMutualInfo_eq_entropy_diff X_rv Y_rv ℱ]
  linarith [condEntropy_anti X_rv hX
    (le_sup_right (a := MeasurableSpace.comap Y_rv inferInstance) (b := ℱ))]

lemma condMutualInfo_le_entropy
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (X_rv : Ω → X) (Y_rv : Ω → Y)
    (hX : Measurable X_rv) (_hY : Measurable Y_rv)
    (ℱ : MeasurableSpace Ω) :
    condMutualInfo X_rv Y_rv ℱ ≤ entropy X_rv := by
  rw [condMutualInfo_eq_entropy_diff X_rv Y_rv ℱ]
  calc condEntropy X_rv ℱ -
        condEntropy X_rv (MeasurableSpace.comap Y_rv inferInstance ⊔ ℱ)
      ≤ condEntropy X_rv ℱ :=
          sub_le_self _ (condEntropy_nonneg _ _)
    _ ≤ entropy X_rv :=
          condEntropy_le_entropy _ hX _

-- SUFFICIENCY THEOREM (algebraic)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma condMutualInfo_sufficient_summary
    {Θ : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Obs : Type*} [Fintype Obs] [MeasurableSpace Obs] [MeasurableSingletonClass Obs]
    (Θ_rv  : Ω → Θ)
    (S_rv  : Ω → S)
    (Obs_rv : Ω → Obs)
    (_h_meas_Θ   : Measurable Θ_rv)
    (_h_meas_S   : Measurable S_rv)
    (_h_meas_Obs : Measurable Obs_rv)
    (ℋ : MeasurableSpace Ω)
    (_h_S_le : MeasurableSpace.comap S_rv inferInstance ≤ ℋ)
    (h_S4 : condEntropy Θ_rv ℋ =
            condEntropy Θ_rv (MeasurableSpace.comap S_rv inferInstance))
    (h_S4_obs : condEntropy Θ_rv
                  (MeasurableSpace.comap Obs_rv inferInstance ⊔
                   MeasurableSpace.comap S_rv inferInstance) =
                condEntropy Θ_rv
                  (MeasurableSpace.comap Obs_rv inferInstance ⊔ ℋ)) :
    condMutualInfo Θ_rv Obs_rv (MeasurableSpace.comap S_rv inferInstance) =
      condMutualInfo Θ_rv Obs_rv ℋ := by
  simp only [condMutualInfo_eq_entropy_diff]
  linarith [h_S4, h_S4_obs]

-- BANDIT MEASURABILITY

section BanditMeasurability

variable {A Sig : Type*}
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableEq A]
  [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
  [MeasurableSingletonClass Sig] [MeasurableEq Sig]

lemma summary_at_succ_ae_bandit
    (env : SixPrimitives.Env Unit A Bool)
    (alg : SixPrimitives.Algorithm A Bool Sig)
    [h : AlgIsDeterministic alg]
    (hr : Measurable env.r)
    (hD : TransIsDeterministic env)
    (hEnv : EnvIsMarkov env)
    (hAlg : AlgIsMarkov alg)
    (t T : ℕ) (ht : t + 1 ≤ T) :
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      summary_at alg (t + 1) T ht ω =
        (fun p : Sig × Bool =>
          h.updateFn (p.1, h.actFn p.1, p.2, env.r ((), h.actFn p.1)))
        (summary_at alg t T (Nat.le_of_succ_le ht) ω,
         traj_observation t (Nat.lt_of_succ_le ht) ω) := by
  have h_succ := summary_at_succ_ae_eq env alg hr t T ht hEnv
  have h_act := traj_action_ae_eq_actFn env alg hr t T (Nat.lt_of_succ_le ht) hEnv
  have h_rew := trajMeasure_step_reward_eq_unit env alg hr hD hEnv hAlg T t (Nat.lt_of_succ_le ht)
  filter_upwards [h_succ, h_act, h_rew] with ω hw_succ hw_act hw_rew
  have hw_act' :
      (ω ⟨t, Nat.lt_of_succ_le ht⟩).1 =
        AlgIsDeterministic.actFn alg (summary_at alg t T (Nat.le_of_succ_le ht) ω) := by
    simpa [traj_action] using hw_act
  have hw_rew' :
      traj_reward t (Nat.lt_of_succ_le ht) ω =
        env.r ((), (ω ⟨t, Nat.lt_of_succ_le ht⟩).1) := by
    simpa [traj_reward] using hw_rew
  rw [hw_succ, hw_rew', hw_act']

omit [MeasurableSingletonClass A] [MeasurableEq A] [MeasurableSingletonClass Sig] [MeasurableEq Sig] in
lemma bandit_summary_g_fn_measurable
    (env  : SixPrimitives.Env Unit A Bool)
    (alg  : SixPrimitives.Algorithm A Bool Sig)
    [h   : AlgIsDeterministic alg]
    (hr   : Measurable env.r) :
    Measurable (fun p : Sig × Bool =>
      h.updateFn (p.1, h.actFn p.1, p.2, env.r ((), h.actFn p.1))) := by
  apply h.updateFn_meas.comp
  exact measurable_fst.prodMk
    ((h.actFn_meas.comp measurable_fst).prodMk
      (measurable_snd.prodMk
        (hr.comp ((measurable_const).prodMk (h.actFn_meas.comp measurable_fst)))))

lemma bandit_summary_update_measurable_space
    (env  : SixPrimitives.Env Unit A Bool)
    (alg  : SixPrimitives.Algorithm A Bool Sig)
    [h   : AlgIsDeterministic alg]
    (hr   : Measurable env.r)
    (hD   : TransIsDeterministic env)
    (hEnv : EnvIsMarkov env)
    (hAlg : AlgIsMarkov alg)
    (t T  : ℕ) (ht : t + 1 ≤ T) :
    Measurable (summary_at alg (t + 1) T ht) ∧
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      summary_at alg (t + 1) T ht ω =
        (fun p : Sig × Bool =>
          h.updateFn (p.1, h.actFn p.1, p.2, env.r ((), h.actFn p.1)))
        (summary_at alg t T (Nat.le_of_succ_le ht) ω,
         traj_observation t (Nat.lt_of_succ_le ht) ω) :=
  ⟨summary_at_measurable alg (t + 1) T ht,
   summary_at_succ_ae_bandit env alg hr hD hEnv hAlg t T ht⟩

lemma bandit_summary_condEntropy_eq
    {θ : Type*} [Fintype θ] [MeasurableSpace θ] [MeasurableSingletonClass θ]
    (env  : SixPrimitives.Env Unit A Bool)
    (alg  : SixPrimitives.Algorithm A Bool Sig)
    [h   : AlgIsDeterministic alg]
    (hr   : Measurable env.r)
    (hD   : TransIsDeterministic env)
    (hEnv : EnvIsMarkov env)
    (hAlg : AlgIsMarkov alg)
    (T    : ℕ) (t : ℕ) (ht : t + 1 ≤ T)
    (Θ_rv : Trajectory A Bool T → θ) (hΘ : Measurable Θ_rv)
    [hprob : IsProbabilityMeasure (trajMeasure env alg hr T)] :
    letI : MeasureSpace (Trajectory A Bool T) := ⟨trajMeasure env alg hr T⟩
    condEntropy Θ_rv
        (MeasurableSpace.comap (summary_at alg (t + 1) T ht) inferInstance) =
    condEntropy Θ_rv
        (MeasurableSpace.comap
          (fun ω : Trajectory A Bool T =>
            h.updateFn
              (summary_at alg t T (Nat.le_of_succ_le ht) ω,
               h.actFn (summary_at alg t T (Nat.le_of_succ_le ht) ω),
               traj_observation t (Nat.lt_of_succ_le ht) ω,
               env.r ((), h.actFn (summary_at alg t T (Nat.le_of_succ_le ht) ω))))
          inferInstance) := by
  letI : MeasureSpace (Trajectory A Bool T) := ⟨trajMeasure env alg hr T⟩
  refine condEntropy_congr_ae Θ_rv hΘ ?hf ?hg ?hae
  · exact (bandit_summary_update_measurable_space env alg hr hD hEnv hAlg t T ht).1
  · have h_pair_meas :
        Measurable (fun ω : Trajectory A Bool T =>
          (summary_at alg t T (Nat.le_of_succ_le ht) ω,
           traj_observation t (Nat.lt_of_succ_le ht) ω)) := by
      exact (summary_at_measurable alg t T (Nat.le_of_succ_le ht)).prodMk
        (measurable_traj_observation t (Nat.lt_of_succ_le ht))
    exact (bandit_summary_g_fn_measurable env alg hr).comp h_pair_meas
  · exact (bandit_summary_update_measurable_space env alg hr hD hEnv hAlg t T ht).2

end BanditMeasurability

-- CONDITIONAL MI TO OBSERVATIONS — ALGEBRAIC

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma condMutualInfo_eq_condMI_obs
    {Θ : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    {Sig : Type*} [Fintype Sig] [MeasurableSpace Sig] [MeasurableSingletonClass Sig]
    (Θ_rv        : Ω → Θ)
    (obs_cycle_K : Ω → Bool)
    (S_prev S_curr : Ω → Sig)
    (_h_meas_Θ      : Measurable Θ_rv)
    (_h_meas_obs    : Measurable obs_cycle_K)
    (_h_meas_S_prev : Measurable S_prev)
    (_h_meas_S_curr : Measurable S_curr)
    (ℱ_prev        : MeasurableSpace Ω)
    (h_S_prev_le   : MeasurableSpace.comap S_prev inferInstance ≤ ℱ_prev)
    (h_S4_prev     : condEntropy Θ_rv ℱ_prev =
                     condEntropy Θ_rv (MeasurableSpace.comap S_prev inferInstance))
    (_h_S4_obs     : condEntropy Θ_rv
                       (MeasurableSpace.comap obs_cycle_K inferInstance ⊔
                        MeasurableSpace.comap S_prev inferInstance) =
                     condEntropy Θ_rv
                       (MeasurableSpace.comap obs_cycle_K inferInstance ⊔ ℱ_prev))
    (h_S4_curr     : condEntropy Θ_rv
                       (MeasurableSpace.comap S_curr inferInstance ⊔
                        MeasurableSpace.comap S_prev inferInstance) =
                     condEntropy Θ_rv
                       (MeasurableSpace.comap S_curr inferInstance ⊔ ℱ_prev))
    (h_S_curr_det  : MeasurableSpace.comap S_curr inferInstance ≤
                     MeasurableSpace.comap S_prev inferInstance ⊔
                     MeasurableSpace.comap obs_cycle_K inferInstance)
    (h_obs_det     : MeasurableSpace.comap obs_cycle_K inferInstance ≤
                     MeasurableSpace.comap S_curr inferInstance ⊔ ℱ_prev) :
    condMutualInfo Θ_rv S_curr (MeasurableSpace.comap S_prev inferInstance) =
      condMutualInfo Θ_rv obs_cycle_K ℱ_prev := by
  simp only [condMutualInfo_eq_entropy_diff]
  rw [← h_S4_prev, h_S4_curr]
  suffices h_eq : MeasurableSpace.comap S_curr inferInstance ⊔ ℱ_prev =
                  MeasurableSpace.comap obs_cycle_K inferInstance ⊔ ℱ_prev by
    rw [h_eq]
  apply le_antisymm
  · apply sup_le
    · calc MeasurableSpace.comap S_curr inferInstance
        _ ≤ MeasurableSpace.comap S_prev inferInstance ⊔ MeasurableSpace.comap obs_cycle_K inferInstance := h_S_curr_det
        _ ≤ ℱ_prev ⊔ MeasurableSpace.comap obs_cycle_K inferInstance :=
            sup_le (h_S_prev_le.trans le_sup_left) le_sup_right
        _ = MeasurableSpace.comap obs_cycle_K inferInstance ⊔ ℱ_prev := sup_comm _ _
    · exact le_sup_right
  · apply sup_le
    · exact h_obs_det
    · exact le_sup_right

end ConditionalMutualInformation

-- FANO'S INEQUALITY (Concrete Bridges)

section FanoConcrete

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma integrable_negMulLog_indicator {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (Y_rv : Ω → α) (hY : Measurable Y_rv) (y : α)
    (m : MeasurableSpace Ω) (hm : m ≤ MeasureSpace.toMeasurableSpace) :
    Integrable (fun ω => Real.negMulLog (ℙ[(Y_rv ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) | m] ω)) ℙ := by
  let f := (Y_rv ⁻¹' {y}).indicator (fun _ => (1 : ℝ))
  have hf_int : Integrable f ℙ := (integrable_const 1).indicator (hY (measurableSet_singleton y))
  have h_nn : 0 ≤ᵐ[ℙ] ℙ[f | m] := condExp_nonneg (Eventually.of_forall (Set.indicator_nonneg (fun _ _ => zero_le_one)))
  have h_le_one : ℙ[f | m] ≤ᵐ[ℙ] fun _ => (1 : ℝ) := by
    have hmono : ℙ[f | m] ≤ᵐ[ℙ] ℙ[fun _ => (1 : ℝ) | m] :=
      condExp_mono hf_int (integrable_const 1) (Eventually.of_forall (fun ω => by
        classical
        change ((Y_rv ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω) ≤ 1
        simp only [Set.indicator_apply]
        split_ifs <;> norm_num))
    have hconst : ℙ[fun _ : Ω => (1 : ℝ) | m] =ᵐ[ℙ] fun _ => (1 : ℝ) :=
      ae_of_all ℙ (fun ω => congr_fun (condExp_const hm (1 : ℝ)) ω)
    filter_upwards [hmono, hconst] with ω h1 h2
    exact le_of_le_of_eq h1 h2
  have hInt : Integrable (ℙ[f | m]) ℙ := integrable_condExp
  have h_aestrong := hInt.aestronglyMeasurable
  have h_aestrong' := Real.continuous_negMulLog.comp_aestronglyMeasurable h_aestrong
  have h_le_one_ae : ∀ᵐ ω ∂ℙ, ‖Real.negMulLog (ℙ[f | m] ω)‖ ≤ ‖(1 : ℝ)‖ := by
    filter_upwards [h_nn, h_le_one] with ω h0 h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
    apply le_trans (Real.negMulLog_le_one_sub_self h0)
    exact sub_le_self 1 h0
  exact (integrable_const 1).mono h_aestrong' h_le_one_ae

lemma negMulLog_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hy_pos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have h1 : x * Real.log x ≤ x * Real.log (x + y) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hx_pos (by linarith)) hx
  have h2 : y * Real.log y ≤ y * Real.log (x + y) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hy_pos (by linarith)) hy
  have h3 : x * Real.log x + y * Real.log y ≤ (x + y) * Real.log (x + y) := by
    calc x * Real.log x + y * Real.log y
      _ ≤ x * Real.log (x + y) + y * Real.log (x + y) := add_le_add h1 h2
      _ = (x + y) * Real.log (x + y) := by ring
  dsimp [Real.negMulLog]
  linarith

lemma negMulLog_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Real.negMulLog]
  · intro a s has ih hf
    rw [Finset.sum_insert has, Finset.sum_insert has]
    have ha : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs : 0 ≤ ∑ i ∈ s, f i := by
      apply Finset.sum_nonneg
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)
    have hi : ∀ i ∈ s, 0 ≤ f i := by
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)
    refine le_trans (negMulLog_add_le (f a) (∑ i ∈ s, f i) ha hs) ?_
    exact add_le_add (le_refl (Real.negMulLog (f a))) (ih hi)

lemma sum_negMulLog_le_finset {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤
    Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log (s.card : ℝ) := by
  by_cases hs : s = ∅
  · simp [hs, Real.negMulLog]
  · have h_card_pos : 0 < (s.card : ℝ) := by
      rw [Nat.cast_pos, Finset.card_pos]
      exact Finset.nonempty_of_ne_empty hs
    by_cases hS : ∑ i ∈ s, p i = 0
    · have h_all_zero : ∀ i ∈ s, p i = 0 := by
        intro i hi
        exact (Finset.sum_eq_zero_iff_of_nonneg hp).mp hS i hi
      have h_lhs : ∑ i ∈ s, Real.negMulLog (p i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [h_all_zero i hi, Real.negMulLog]
      have h_rhs :
          Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log (s.card : ℝ) = 0 := by
        simp [hS, Real.negMulLog]
      linarith
    · have hS_pos : 0 < ∑ i ∈ s, p i := lt_of_le_of_ne (Finset.sum_nonneg hp) (Ne.symm hS)
      let w : ι → ℝ := fun _ => 1 / (s.card : ℝ)
      have hw : ∀ i ∈ s, 0 ≤ w i := fun _ _ => one_div_nonneg.mpr (le_of_lt h_card_pos)
      have hw_sum : ∑ i ∈ s, w i = 1 := by
        dsimp [w]
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_one_div_cancel h_card_pos.ne'
      have hp_mem : ∀ i ∈ s, p i ∈ Set.Ici (0 : ℝ) := fun i hi => hp i hi
      have h_jensen := Real.concaveOn_negMulLog.le_map_sum hw hw_sum hp_mem
      have h_sum_w_f :
          ∑ i ∈ s, w i • Real.negMulLog (p i) =
            (1 / (s.card : ℝ)) * ∑ i ∈ s, Real.negMulLog (p i) := by
        classical
        dsimp [w]
        simp [Finset.mul_sum]
      have h_sum_w_p :
          ∑ i ∈ s, w i • p i =
            (1 / (s.card : ℝ)) * ∑ i ∈ s, p i := by
        classical
        dsimp [w]
        simp [Finset.mul_sum]
      rw [h_sum_w_f, h_sum_w_p] at h_jensen
      have h_mul := mul_le_mul_of_nonneg_left h_jensen (le_of_lt h_card_pos)
      have h_cancel1 : (s.card : ℝ) * ((1 / (s.card : ℝ)) * ∑ i ∈ s, Real.negMulLog (p i)) = ∑ i ∈ s, Real.negMulLog (p i) := by
        rw [← mul_assoc, mul_one_div_cancel h_card_pos.ne', one_mul]
      rw [h_cancel1] at h_mul
      have h_log_mul : Real.log ((1 / (s.card : ℝ)) * ∑ i ∈ s, p i) = Real.log (1 / (s.card : ℝ)) + Real.log (∑ i ∈ s, p i) := by
        apply Real.log_mul (one_div_pos.mpr h_card_pos).ne' hS_pos.ne'
      have h_log_inv : Real.log (1 / (s.card : ℝ)) = - Real.log (s.card : ℝ) := by
        rw [one_div, Real.log_inv]
      have h_rhs : (s.card : ℝ) * Real.negMulLog ((1 / (s.card : ℝ)) * ∑ i ∈ s, p i) =
                   Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log (s.card : ℝ) := by
        unfold Real.negMulLog
        rw [h_log_mul, h_log_inv]
        calc
          (s.card : ℝ) * (-((1 / (s.card : ℝ)) * ∑ i ∈ s, p i) * (-Real.log (s.card : ℝ) + Real.log (∑ i ∈ s, p i)))
            = ((s.card : ℝ) * (1 / (s.card : ℝ))) * (-(∑ i ∈ s, p i) * (-Real.log (s.card : ℝ) + Real.log (∑ i ∈ s, p i))) := by ring
          _ = 1 * (-(∑ i ∈ s, p i) * (-Real.log (s.card : ℝ) + Real.log (∑ i ∈ s, p i))) := by rw [mul_one_div_cancel h_card_pos.ne']
          _ = -(∑ i ∈ s, p i) * Real.log (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log (s.card : ℝ) := by ring
      rw [h_rhs] at h_mul
      exact h_mul

theorem pointwise_fano_bound {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ) (h_nn : ∀ a, 0 ≤ p a)
    (h_sum : ∑ a, p a = 1) (a_star : A) (m : ℕ) (h_card : Fintype.card A = m) (h_m : 2 ≤ m) :
    ∑ a, Real.negMulLog (p a) ≤
    Phase1.binEntropy (1 - p a_star) + (1 - p a_star) * Real.log ((m : ℝ) - 1) := by
  let s := Finset.univ.erase a_star
  have has : a_star ∉ s := by simp [s]
  have h_insert : insert a_star s = Finset.univ := Finset.insert_erase (Finset.mem_univ a_star)
  have h_split_p : ∑ a, p a = p a_star + ∑ a ∈ s, p a := by
    have h : ∑ a ∈ insert a_star s, p a = p a_star + ∑ a ∈ s, p a := Finset.sum_insert has
    rw [h_insert] at h
    exact h
  have h_q : ∑ a ∈ s, p a = 1 - p a_star := by linarith [h_sum, h_split_p]
  have h_split_ent : ∑ a, Real.negMulLog (p a) = Real.negMulLog (p a_star) + ∑ a ∈ s, Real.negMulLog (p a) := by
    have h : ∑ a ∈ insert a_star s, Real.negMulLog (p a) = Real.negMulLog (p a_star) + ∑ a ∈ s, Real.negMulLog (p a) := Finset.sum_insert has
    rw [h_insert] at h
    exact h
  have h_jensen := sum_negMulLog_le_finset s p (fun i _ => h_nn i)
  have h_m_pos : 1 ≤ m := by linarith
  have h_card_s : (s.card : ℝ) = (m : ℝ) - 1 := by
    have hc : s.card = Fintype.card A - 1 := Finset.card_erase_of_mem (Finset.mem_univ a_star)
    rw [h_card] at hc
    rw [hc]
    rw [Nat.cast_sub h_m_pos, Nat.cast_one]
  rw [h_q, h_card_s] at h_jensen
  have h_bound : ∑ a, Real.negMulLog (p a) ≤ Real.negMulLog (p a_star) + Real.negMulLog (1 - p a_star) + (1 - p a_star) * Real.log ((m : ℝ) - 1) := by
    rw [h_split_ent]
    linarith [h_jensen]
  unfold Phase1.binEntropy
  dsimp [Real.negMulLog] at h_bound ⊢
  have h_sub : 1 - (1 - p a_star) = p a_star := by ring
  rw [h_sub]
  linarith [h_bound]

theorem condEntropy_direct_fano_bound {A X : Type*}
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [DecidableEq A]
    [MeasurableSpace X]
    (h_card : 2 ≤ Fintype.card A) (a_star : A)
    (A_rv : Ω → A) (X_rv : Ω → X) (hA : Measurable A_rv) (hX : Measurable X_rv) :
    condEntropy A_rv (MeasurableSpace.comap X_rv inferInstance) ≤
    Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal +
    (ℙ {ω | A_rv ω ≠ a_star}).toReal * Real.log ((Fintype.card A : ℝ) - 1) := by
  let m_sig := MeasurableSpace.comap X_rv (inferInstance : MeasurableSpace X)
  let m := Fintype.card A
  let p := fun (a : A) (ω : Ω) => ℙ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig] ω
  have h_le : m_sig ≤ MeasureSpace.toMeasurableSpace := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact hX ht
  have h_meas_A : @MeasurableSet Ω MeasureSpace.toMeasurableSpace (A_rv ⁻¹' {a_star}) := hA (measurableSet_singleton a_star)
  have hp_nn : ∀ᵐ ω ∂ℙ, ∀ a, 0 ≤ p a ω := by
    have h1 : ∀ a, ∀ᵐ ω ∂ℙ, 0 ≤ p a ω := fun a =>
      condExp_nonneg (Eventually.of_forall (Set.indicator_nonneg (fun _ _ => zero_le_one)))
    exact Filter.eventually_all.mpr h1
  have hp_sum : ∀ᵐ ω ∂ℙ, ∑ a, p a ω = 1 := by
    have h_sum_ind : (∑ a, (A_rv ⁻¹' {a}).indicator (fun _ : Ω => (1 : ℝ))) = (fun _ => 1) := by
      ext ω
      classical
      simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
      have h_eq : (∑ a : A, if A_rv ω = a then (1 : ℝ) else 0) = ∑ a : A, if a = A_rv ω then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : A_rv ω = x
        · simp [h]
        · have h' : x ≠ A_rv ω := Ne.symm h
          simp [h, h']
      rw [h_eq]
      simp
    have h_cond_sum : ∑ a, ℙ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig] =ᵐ[ℙ]
        ℙ[∑ a, (A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig] := by
      have h_int : ∀ a ∈ Finset.univ, Integrable ((A_rv ⁻¹' {a}).indicator (fun _ : Ω => (1 : ℝ))) ℙ := by
        intro a _
        exact (integrable_const (1 : ℝ)).indicator (hA (measurableSet_singleton a))
      exact (condExp_finsetSum h_int m_sig).symm
    have h_cond_one : ℙ[fun _ : Ω => (1 : ℝ) | m_sig] =ᵐ[ℙ] fun _ => 1 :=
      ae_of_all ℙ (fun ω => congr_fun (condExp_const h_le (1 : ℝ)) ω)
    filter_upwards [h_cond_sum, h_cond_one] with ω h1 h2
    calc ∑ a, p a ω = ∑ a, ℙ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig] ω := rfl
      _ = (∑ a, ℙ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig]) ω := by rw [Finset.sum_apply]
      _ = ℙ[∑ a, (A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m_sig] ω := h1
      _ = ℙ[fun _ : Ω => (1 : ℝ) | m_sig] ω := by rw [h_sum_ind]
      _ = 1 := h2
  have h_pw_bound : ∀ᵐ ω ∂ℙ, ∑ a, Real.negMulLog (p a ω) ≤
      Phase1.binEntropy (1 - p a_star ω) + (1 - p a_star ω) * Real.log ((m : ℝ) - 1) := by
    filter_upwards [hp_nn, hp_sum] with ω h_nn h_sum
    exact pointwise_fano_bound (fun a => p a ω) h_nn h_sum a_star m rfl h_card
  have h_int_p_cond : Integrable (p a_star) ℙ := integrable_condExp
  have h_err_exp : ∫ ω, 1 - p a_star ω ∂ℙ = (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
    rw [integral_sub (integrable_const 1) h_int_p_cond]
    have h_int_1 : ∫ _ : Ω, (1 : ℝ) ∂ℙ = 1 := by
      rw [integral_const]
      change (ℙ Set.univ).toReal • (1 : ℝ) = 1
      rw [measure_univ, ENNReal.toReal_one, one_smul]
    rw [h_int_1]
    have h_int_p : ∫ ω, p a_star ω ∂ℙ = (ℙ (A_rv ⁻¹' {a_star})).toReal := by
      rw [integral_condExp h_le]
      have h_ind : ∫ ω, (A_rv ⁻¹' {a_star}).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ℙ = (ℙ (A_rv ⁻¹' {a_star})).toReal := by
        rw [integral_indicator_const (s_meas := h_meas_A)]
        change (ℙ _).toReal • (1 : ℝ) = _
        rw [smul_eq_mul, mul_one]
      exact h_ind
    rw [h_int_p]
    have hc_set : {ω | A_rv ω ≠ a_star} = (A_rv ⁻¹' {a_star})ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hc_set]
    have h_add : ℙ (A_rv ⁻¹' {a_star}) + ℙ (A_rv ⁻¹' {a_star})ᶜ = ℙ Set.univ := measure_add_measure_compl h_meas_A
    have h_top1 : ℙ (A_rv ⁻¹' {a_star}) ≠ ∞ := by
      have h_le : ℙ (A_rv ⁻¹' {a_star}) ≤ ℙ Set.univ := measure_mono (Set.subset_univ (A_rv ⁻¹' {a_star}))
      rw [measure_univ] at h_le
      exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
    have h_top2 : ℙ (A_rv ⁻¹' {a_star})ᶜ ≠ ∞ := by
      have h_le : ℙ (A_rv ⁻¹' {a_star})ᶜ ≤ ℙ Set.univ := measure_mono (Set.subset_univ (A_rv ⁻¹' {a_star})ᶜ)
      rw [measure_univ] at h_le
      exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
    have h_add_real : (ℙ (A_rv ⁻¹' {a_star})).toReal + (ℙ (A_rv ⁻¹' {a_star})ᶜ).toReal = (ℙ (Set.univ : Set Ω)).toReal := by
      rw [← h_add]
      exact (ENNReal.toReal_add h_top1 h_top2).symm
    rw [measure_univ, ENNReal.toReal_one] at h_add_real
    linarith
  let E_rv : Ω → Bool := fun ω => if A_rv ω = a_star then false else true
  have hE_meas : @Measurable Ω Bool MeasureSpace.toMeasurableSpace Bool.instMeasurableSpace E_rv :=
    Measurable.ite h_meas_A measurable_const measurable_const
  have h_le_E : condEntropy E_rv m_sig ≤ entropy E_rv := condEntropy_le_entropy E_rv hE_meas m_sig
  have h_false_set : E_rv ⁻¹' {false} = A_rv ⁻¹' {a_star} := by
    ext ω
    classical
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change (if A_rv ω = a_star then false else true) = false ↔ A_rv ω = a_star
    split_ifs with h
    · simp [h]
    · simp [h]
  have h_true_set : E_rv ⁻¹' {true} = {ω : Ω | A_rv ω ≠ a_star} := by
    ext ω
    classical
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    change (if A_rv ω = a_star then false else true) = true ↔ A_rv ω ≠ a_star
    split_ifs with h
    · simp [h]
    · simp [h]
  have h_p_true : ℙ[(E_rv ⁻¹' {true}).indicator (fun _ => (1 : ℝ)) | m_sig] =ᵐ[ℙ] fun ω => 1 - p a_star ω := by
    have hd : (E_rv ⁻¹' {true}).indicator (fun _ : Ω => (1 : ℝ)) = fun ω => 1 - (A_rv ⁻¹' {a_star}).indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      classical
      change (if ω ∈ E_rv ⁻¹' {true} then (1 : ℝ) else 0) = 1 - (if ω ∈ A_rv ⁻¹' {a_star} then (1 : ℝ) else 0)
      rw [h_true_set]
      dsimp
      by_cases h : A_rv ω = a_star
      · have hn : ¬ (A_rv ω ≠ a_star) := not_not.mpr h
        simp [h]
      · simp [h]
    have h_int_1 : Integrable (fun _ : Ω => (1 : ℝ)) ℙ := integrable_const 1
    have h_int_f : Integrable ((A_rv ⁻¹' {a_star}).indicator (fun _ : Ω => (1 : ℝ))) ℙ := (integrable_const 1).indicator h_meas_A
    have h_sub := condExp_sub h_int_1 h_int_f m_sig
    have h_c1 : ℙ[fun _ => (1 : ℝ) | m_sig] =ᵐ[ℙ] fun _ => 1 :=
      ae_of_all ℙ (fun ω => congr_fun (condExp_const h_le (1 : ℝ)) ω)
    filter_upwards [h_sub, h_c1] with ω hs hc1
    calc ℙ[(E_rv ⁻¹' {true}).indicator (fun _ => (1 : ℝ)) | m_sig] ω
      _ = ℙ[fun ω => 1 - (A_rv ⁻¹' {a_star}).indicator (fun _ => (1 : ℝ)) ω | m_sig] ω := by rw [hd]
      _ = ℙ[fun _ : Ω => (1 : ℝ) | m_sig] ω - ℙ[(A_rv ⁻¹' {a_star}).indicator (fun _ => (1 : ℝ)) | m_sig] ω := hs
      _ = 1 - p a_star ω := by rw [hc1];
  have h_integrand_eq : ∀ᵐ ω ∂ℙ, ∑ x : Bool, -(ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω * Real.log (ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω)) = Phase1.binEntropy (1 - p a_star ω) := by
    filter_upwards [h_p_true] with ω ht
    rw [Fintype.sum_bool]
    have hf : ℙ[(E_rv ⁻¹' {false}).indicator (fun _ => (1 : ℝ)) | m_sig] ω = p a_star ω := by
      have hd : (E_rv ⁻¹' {false}).indicator (fun _ : Ω => (1 : ℝ)) = (A_rv ⁻¹' {a_star}).indicator (fun _ => (1 : ℝ)) := by
        ext x
        rw [h_false_set]
      rw [hd]
    rw [ht, hf]
    unfold Phase1.binEntropy
    have h_sub : 1 - (1 - p a_star ω) = p a_star ω := by ring
    rw [h_sub]
    ring
  have h_condE_eq : condEntropy E_rv m_sig = ∫ ω, Phase1.binEntropy (1 - p a_star ω) ∂ℙ := by
    unfold condEntropy
    apply integral_congr_ae
    exact h_integrand_eq
  have h_uncond : entropy E_rv = Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
    rw [entropy, condEntropy]
    have h_meas_E : ∀ x, @MeasurableSet Ω MeasureSpace.toMeasurableSpace (E_rv ⁻¹' {x}) := fun x => hE_meas (measurableSet_singleton x)
    have h_condExp_bot : ∀ x : Bool, ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ⊥] =ᵐ[ℙ] fun _ => (ℙ (E_rv ⁻¹' {x})).toReal := by
      intro x
      let f : Ω → ℝ := (E_rv ⁻¹' {x}).indicator (fun _ => 1)
      have h_bot : ℙ[f | ⊥] = fun _ => ∫ ω, f ω ∂ℙ := condExp_bot f
      apply ae_of_all
      intro ω
      change ℙ[f | ⊥] ω = (ℙ (E_rv ⁻¹' {x})).toReal
      rw [h_bot]
      have h_ind : ∫ ω, (E_rv ⁻¹' {x}).indicator (fun _ : Ω => (1 : ℝ)) ω ∂ℙ = (ℙ (E_rv ⁻¹' {x})).toReal := by
        rw [integral_indicator_const (s_meas := h_meas_E x)]
        change (ℙ _).toReal • (1 : ℝ) = _
        rw [smul_eq_mul, mul_one]
      exact h_ind
    have h_integrand : ∀ᵐ ω ∂ℙ, ∑ x : Bool, -(ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ⊥] ω * Real.log (ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ⊥] ω)) =
      ∑ x : Bool, -((ℙ (E_rv ⁻¹' {x})).toReal * Real.log (ℙ (E_rv ⁻¹' {x})).toReal) := by
      have h_ae_all : ∀ᵐ ω ∂ℙ, ∀ x : Bool, ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | ⊥] ω = (ℙ (E_rv ⁻¹' {x})).toReal := by
        rw [Filter.eventually_all]
        exact h_condExp_bot
      filter_upwards [h_ae_all] with ω hω
      apply Finset.sum_congr rfl
      intro x _
      rw [hω x]
    rw [integral_congr_ae h_integrand]
    have h_int_const : ∫ _ : Ω, ∑ x : Bool, -((ℙ (E_rv ⁻¹' {x})).toReal * Real.log (ℙ (E_rv ⁻¹' {x})).toReal) ∂ℙ =
      ∑ x : Bool, -((ℙ (E_rv ⁻¹' {x})).toReal * Real.log (ℙ (E_rv ⁻¹' {x})).toReal) := by
      rw [integral_const]
      change (ℙ Set.univ).toReal • _ = _
      rw [measure_univ, ENNReal.toReal_one, one_smul]
    rw [h_int_const]
    rw [Fintype.sum_bool]
    have h_true_prob : (ℙ (E_rv ⁻¹' {true})).toReal = (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
      rw [h_true_set]
    have h_false_prob : (ℙ (E_rv ⁻¹' {false})).toReal = 1 - (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
      rw [h_false_set]
      have hc_set : {ω | A_rv ω ≠ a_star} = (A_rv ⁻¹' {a_star})ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hc_set]
      have h_add : ℙ (A_rv ⁻¹' {a_star}) + ℙ (A_rv ⁻¹' {a_star})ᶜ = ℙ Set.univ := measure_add_measure_compl h_meas_A
      have h_top1 : ℙ (A_rv ⁻¹' {a_star}) ≠ ∞ := by
        have h_le : ℙ (A_rv ⁻¹' {a_star}) ≤ ℙ Set.univ := measure_mono (Set.subset_univ (A_rv ⁻¹' {a_star}))
        rw [measure_univ] at h_le
        exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
      have h_top2 : ℙ (A_rv ⁻¹' {a_star})ᶜ ≠ ∞ := by
        have h_le : ℙ (A_rv ⁻¹' {a_star})ᶜ ≤ ℙ Set.univ := measure_mono (Set.subset_univ (A_rv ⁻¹' {a_star})ᶜ)
        rw [measure_univ] at h_le
        exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
      have h_add_real : (ℙ (A_rv ⁻¹' {a_star})).toReal + (ℙ (A_rv ⁻¹' {a_star})ᶜ).toReal = (ℙ (Set.univ : Set Ω)).toReal := by
        rw [← h_add]
        exact (ENNReal.toReal_add h_top1 h_top2).symm
      rw [measure_univ, ENNReal.toReal_one] at h_add_real
      linarith
    rw [h_true_prob, h_false_prob]
    unfold Phase1.binEntropy
    ring
  have h_jensen : ∫ ω, Phase1.binEntropy (1 - p a_star ω) ∂ℙ ≤
      Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
    rw [← h_condE_eq, ← h_uncond]
    exact h_le_E
  have hInt_LHS : Integrable (fun ω => ∑ a, Real.negMulLog (p a ω)) ℙ := by
    apply integrable_finsetSum
    intro a _
    exact integrable_negMulLog_indicator A_rv hA a m_sig h_le
  have hInt_1_minus_p : Integrable (fun ω => 1 - p a_star ω) ℙ :=
    (integrable_const 1).sub h_int_p_cond
  have hInt_RHS_linear : Integrable (fun ω => (1 - p a_star ω) * Real.log ((m : ℝ) - 1)) ℙ :=
    hInt_1_minus_p.mul_const _
  have hInt_RHS_binEnt : Integrable (fun ω => Phase1.binEntropy (1 - p a_star ω)) ℙ := by
    have h_int_sum : Integrable (fun ω => ∑ x : Bool, -(ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω * Real.log (ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω))) ℙ := by
      have h_rw : (fun ω => ∑ x : Bool, -(ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω * Real.log (ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω))) = fun ω => ∑ x : Bool, Real.negMulLog (ℙ[(E_rv ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) | m_sig] ω) := by
        ext ω
        apply Finset.sum_congr rfl
        intro x _
        unfold Real.negMulLog
        ring
      rw [h_rw]
      apply integrable_finsetSum
      intro x _
      exact integrable_negMulLog_indicator E_rv hE_meas x m_sig h_le
    exact h_int_sum.congr h_integrand_eq
  calc condEntropy A_rv m_sig
    _ = ∫ ω, ∑ a, Real.negMulLog (p a ω) ∂ℙ := by
        simp [condEntropy, p, Real.negMulLog]
    _ ≤ ∫ ω, Phase1.binEntropy (1 - p a_star ω) + (1 - p a_star ω) * Real.log ((m : ℝ) - 1) ∂ℙ := by
        exact integral_mono_ae hInt_LHS (hInt_RHS_binEnt.add hInt_RHS_linear) h_pw_bound
    _ = ∫ ω, Phase1.binEntropy (1 - p a_star ω) ∂ℙ + ∫ ω, (1 - p a_star ω) * Real.log ((m : ℝ) - 1) ∂ℙ := by
        exact integral_add hInt_RHS_binEnt hInt_RHS_linear
    _ = ∫ ω, Phase1.binEntropy (1 - p a_star ω) ∂ℙ + (∫ ω, 1 - p a_star ω ∂ℙ) * Real.log ((m : ℝ) - 1) := by
        rw [integral_mul_const]
    _ = ∫ ω, Phase1.binEntropy (1 - p a_star ω) ∂ℙ + (ℙ {ω | A_rv ω ≠ a_star}).toReal * Real.log ((m : ℝ) - 1) := by
        rw [h_err_exp]
    _ ≤ Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal + (ℙ {ω | A_rv ω ≠ a_star}).toReal * Real.log ((m : ℝ) - 1) := by
        exact add_le_add h_jensen (le_refl _)

theorem fano_binary_error_lower_bound {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [MeasurableSingletonClass A] [DecidableEq A]
    (hA_card : Fintype.card A = 2)
    (a_star : A) (A_rv : Ω → A) (X_rv : Ω → X)
    (hAmeas : Measurable A_rv) (hXmeas : Measurable X_rv)
    (hH_ge : ε ≤ condEntropy A_rv (MeasurableSpace.comap X_rv inferInstance)) :
    (ℙ {ω | A_rv ω ≠ a_star}).toReal ≥ Phase1.binEntropyInv ε := by
  have h_card_le : 2 ≤ Fintype.card A := by linarith
  have h_fano := condEntropy_direct_fano_bound h_card_le a_star A_rv X_rv hAmeas hXmeas
  have h_log : Real.log ((Fintype.card A : ℝ) - 1) = 0 := by
    rw [hA_card]
    norm_num
  have h_fano_simp : condEntropy A_rv (MeasurableSpace.comap X_rv inferInstance) ≤
      Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal := by
    calc condEntropy A_rv (MeasurableSpace.comap X_rv inferInstance)
      _ ≤ Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal + (ℙ {ω | A_rv ω ≠ a_star}).toReal * Real.log ((Fintype.card A : ℝ) - 1) := h_fano
      _ = Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal + (ℙ {ω | A_rv ω ≠ a_star}).toReal * 0 := by rw [h_log]
      _ = Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal := by ring
  have h_p_ge : ε ≤ Phase1.binEntropy (ℙ {ω | A_rv ω ≠ a_star}).toReal :=
    hH_ge.trans h_fano_simp
  let p := (ℙ {ω | A_rv ω ≠ a_star}).toReal
  let x := Phase1.binEntropyInv ε
  have hx_spec := Phase1.binEntropyInv_spec hε hε2
  have hx0 : 0 < x := hx_spec.1
  have hx_half : x < 1 / 2 := hx_spec.2.1
  have hx_eq : Phase1.binEntropy x = ε := hx_spec.2.2
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have h_fano2 : ∀ q, Phase1.fanoPhi q 2 = Phase1.binEntropy q := by
    intro q
    simp only [Phase1.fanoPhi]
    norm_num
  have h_mono : StrictMonoOn Phase1.binEntropy (Set.Icc 0 (1 / 2)) := by
    intro a ha b hb hab
    have h_sm := Phase1.fanoPhi_strictMono 2 (by norm_num)
    have h_interval_eq : Set.Icc (0 : ℝ) (1 - 1 / ((2 : ℕ) : ℝ)) = Set.Icc (0 : ℝ) (1 / 2) := by
      push_cast
      norm_num
    rw [h_interval_eq] at h_sm
    simpa [h_fano2] using h_sm ha hb hab
  by_cases hp_half : p < 1 / 2
  · by_contra h_not_le
    have h_lt : p < x := lt_of_not_ge h_not_le
    have hp_mem : p ∈ Set.Icc 0 (1 / 2) := ⟨hp0, hp_half.le⟩
    have hx_mem : x ∈ Set.Icc 0 (1 / 2) := ⟨hx0.le, hx_half.le⟩
    have h_strict := h_mono hp_mem hx_mem h_lt
    rw [hx_eq] at h_strict
    exact lt_irrefl _ (h_strict.trans_le h_p_ge)
  · have hp_half_le : 1 / 2 ≤ p := by linarith
    have hx_le : x ≤ 1 / 2 := by linarith
    exact hx_le.trans hp_half_le

end FanoConcrete

end SixPrimitives.Phase2
