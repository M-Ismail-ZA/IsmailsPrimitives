import SixPrimitives.Phase0
import SixPrimitives.Phase1
import SixPrimitives.Phase2
import SixPrimitives.Phase2CMI
import SixPrimitives.Phase3
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-! # Ismail's Primitives — Phase 4: Mutual Independence
This phase establishes the mutual independence of the six primitives.
For every ordered pair (Xᵢ, Xⱼ) with i ≠ j, the canonical algorithm
designed to possess Xⱼ is shown to lack Xᵢ when placed in Xᵢ's home environment.-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal

namespace SixPrimitives.Phase4

open SixPrimitives.Phase2 SixPrimitives.Phase3

-- PART A: THE CHALLENGERS (CANONICAL ALGORITHMS)

section CanonicalAlgorithms

/-- Universal Challenger Template -/
noncomputable def canonical_challenger (A O : Type)
    [MeasurableSpace A] [MeasurableSpace O]
    (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit where
  act    := policy
  update := Kernel.const _ (Measure.dirac ())
  σ₀     := ()

instance canonical_challenger_isMarkov (A O : Type)
    [MeasurableSpace A] [MeasurableSpace O]
    (policy : Kernel Unit A) [h : IsMarkovKernel policy] :
    Phase2.AlgIsMarkov (canonical_challenger A O policy) where
  act_markov := h
  update_markov := by
    dsimp [canonical_challenger]
    infer_instance

-- The 6 Canonical Algorithms

noncomputable def alg1_bayes (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg1_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg1_bayes A O policy) := canonical_challenger_isMarkov A O policy

noncomputable def alg2_safe (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg2_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg2_safe A O policy) := canonical_challenger_isMarkov A O policy

noncomputable def alg3_bridge (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg3_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg3_bridge A O policy) := canonical_challenger_isMarkov A O policy

noncomputable def alg4_ucb (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg4_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg4_ucb A O policy) := canonical_challenger_isMarkov A O policy

noncomputable def alg5_feas (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg5_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg5_feas A O policy) := canonical_challenger_isMarkov A O policy

noncomputable def alg6_shortMem (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) : SixPrimitives.Algorithm A O Unit := canonical_challenger A O policy
instance alg6_isMarkov (A O : Type) [MeasurableSpace A] [MeasurableSpace O] (policy : Kernel Unit A) [IsMarkovKernel policy] : Phase2.AlgIsMarkov (alg6_shortMem A O policy) := canonical_challenger_isMarkov A O policy

-- Failing Policies for Injection

noncomputable abbrev pol0 : Kernel Unit (Fin 2) := Kernel.const _ (Measure.dirac 0)
instance : IsMarkovKernel pol0 := inferInstance

noncomputable abbrev pol1 : Kernel Unit (Fin 2) := Kernel.const _ (Measure.dirac 1)
instance : IsMarkovKernel pol1 := inferInstance

noncomputable abbrev polR : Kernel Unit ℝ := Kernel.const _ (Measure.dirac (1/2 : ℝ))
instance : IsMarkovKernel polR := inferInstance

noncomputable def pol_eps : Kernel Unit (Fin 2) :=
  Kernel.const _ ((1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1)

instance pol_eps_isMarkov : IsMarkovKernel pol_eps := by
  constructor
  intro _
  constructor -- Unpacks `IsProbabilityMeasure` to target `μ Set.univ = 1`
  simp only [pol_eps, Kernel.const_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have h1 : Measure.dirac (0 : Fin 2) Set.univ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ _)
  have h2 : Measure.dirac (1 : Fin 2) Set.univ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ _)
  rw [h1, h2, mul_one]
  exact ENNReal.add_halves 1

end CanonicalAlgorithms

-- PART B: THE 30 HOME TURF MATCH-UPS

section IndependenceMatchups

variable (bp : Phase2.BanditParam)
variable (K : ℕ) (hK : 0 < K)
variable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
variable (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
variable (T₀ : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4)


-- 1. Home Turf: env1_0 (Lacks X₁)

instance alg2_safe_pol0_isDet : Phase2.AlgIsDeterministic (alg2_safe (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg2_lacks_x1 (bp : Phase2.BanditParam) :
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp)
      (alg2_safe (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp)
      (Phase2.env₁_1_isMarkov bp) (alg2_isMarkov (Fin 2) Bool pol0)) := by
  unfold LacksX₁
  refine ⟨0, by norm_num, ?_⟩
  have h_seq : (fun t => Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg2_safe (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg2_isMarkov (Fin 2) Bool pol0) t) = fun _ => 0 := by
    ext t
    unfold Phase3.miSeq Phase3.tvDistMeasure
    have h_eval : ∀ (env' : SixPrimitives.Env Unit (Fin 2) Bool) (hEnv' : Phase2.EnvIsMarkov env'),
        ∀ a : Fin 2, ((Phase2.actionMarginal env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg2_isMarkov (Fin 2) Bool pol0) (t + 1) ⟨t, Nat.lt_succ_self t⟩) {a}).toReal = if a = 0 then 1 else 0 := by
      intro env' hEnv' a
      dsimp [Phase2.actionMarginal]
      have h_meas_act : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) :=
        Phase2.measurable_traj_action t (Nat.lt_succ_self t)
      rw [MeasureTheory.Measure.map_apply h_meas_act (measurableSet_singleton a)]
      have h_ae := Phase2.traj_action_ae_eq_actFn env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas t (t + 1) (Nat.lt_succ_self t) hEnv'
      by_cases ha : a = 0
      · subst ha
        have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∈ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0} := by
          filter_upwards [h_ae] with ω hω
          exact hω
        haveI h_prob := Phase2.trajMeasure_isProbability env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg2_isMarkov (Fin 2) Bool pol0) (t + 1)
        have h_meas_one : (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) = 1 := by
          have h_compl : (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_eq
          have h_union : (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) ∪ ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) + (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) := MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl (h_meas_act (measurableSet_singleton 0)))
          rw [Set.union_compl_self, h_prob.measure_univ, h_compl, add_zero] at h_union
          exact h_union.symm
        simp [h_meas_one]
      · have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a} := by
          filter_upwards [h_ae] with ω hω
          intro h_contra
          change (ω ⟨t, Nat.lt_succ_self t⟩).1 = a at h_contra
          have h_act_eq_0 : (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := hω
          rw [h_act_eq_0] at h_contra
          exact ha h_contra.symm
        have h_meas_zero : (Phase2.trajMeasure env' (alg2_safe (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) = 0 := by
          have h_zero := MeasureTheory.ae_iff.mp h_ae_eq
          have h_set_eq : {a_1 : Phase2.Trajectory (Fin 2) Bool (t + 1) | ¬a_1 ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}} = ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) := by ext x; simp
          rwa [h_set_eq] at h_zero
        simp [ha, h_meas_zero]
    have h0 := h_eval (Phase2.env₁_0 bp) (Phase2.env₁_0_isMarkov bp)
    have h1 := h_eval (Phase2.env₁_1 bp) (Phase2.env₁_1_isMarkov bp)
    have h_sum : (∑ a : Fin 2, |(if a = 0 then (1 : ℝ) else 0) - (if a = 0 then (1 : ℝ) else 0)|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sub_self, abs_zero]
    simp_rw [h0, h1]
    rw [h_sum]
    ring
  rw [h_seq]
  simp [Filter.limsup_const]

instance alg3_bridge_pol0_isDet : Phase2.AlgIsDeterministic (alg3_bridge (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg3_lacks_x1 (bp : Phase2.BanditParam) :
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp)
      (alg3_bridge (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp)
      (Phase2.env₁_1_isMarkov bp) (alg3_isMarkov (Fin 2) Bool pol0)) := by
  unfold LacksX₁
  refine ⟨0, by norm_num, ?_⟩
  have h_seq : (fun t => Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg3_bridge (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg3_isMarkov (Fin 2) Bool pol0) t) = fun _ => 0 := by
    ext t
    unfold Phase3.miSeq Phase3.tvDistMeasure
    have h_eval : ∀ (env' : SixPrimitives.Env Unit (Fin 2) Bool) (hEnv' : Phase2.EnvIsMarkov env'),
        ∀ a : Fin 2, ((Phase2.actionMarginal env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg3_isMarkov (Fin 2) Bool pol0) (t + 1) ⟨t, Nat.lt_succ_self t⟩) {a}).toReal = if a = 0 then 1 else 0 := by
      intro env' hEnv' a
      dsimp [Phase2.actionMarginal]
      have h_meas_act : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) :=
        Phase2.measurable_traj_action t (Nat.lt_succ_self t)
      rw [MeasureTheory.Measure.map_apply h_meas_act (measurableSet_singleton a)]
      have h_ae := Phase2.traj_action_ae_eq_actFn env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas t (t + 1) (Nat.lt_succ_self t) hEnv'
      by_cases ha : a = 0
      · subst ha
        have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∈ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0} := by
          filter_upwards [h_ae] with ω hω
          exact hω
        haveI h_prob := Phase2.trajMeasure_isProbability env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg3_isMarkov (Fin 2) Bool pol0) (t + 1)
        have h_meas_one : (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) = 1 := by
          have h_compl : (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_eq
          have h_union : (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) ∪ ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) + (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) := MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl (h_meas_act (measurableSet_singleton 0)))
          rw [Set.union_compl_self, h_prob.measure_univ, h_compl, add_zero] at h_union
          exact h_union.symm
        simp [h_meas_one]
      · have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a} := by
          filter_upwards [h_ae] with ω hω
          intro h_contra
          change (ω ⟨t, Nat.lt_succ_self t⟩).1 = a at h_contra
          have h_act_eq_0 : (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := hω
          rw [h_act_eq_0] at h_contra
          exact ha h_contra.symm
        have h_meas_zero : (Phase2.trajMeasure env' (alg3_bridge (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) = 0 := by
          have h_zero := MeasureTheory.ae_iff.mp h_ae_eq
          have h_set_eq : {a_1 : Phase2.Trajectory (Fin 2) Bool (t + 1) | ¬a_1 ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}} = ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) := by ext x; simp
          rwa [h_set_eq] at h_zero
        simp [ha, h_meas_zero]
    have h0 := h_eval (Phase2.env₁_0 bp) (Phase2.env₁_0_isMarkov bp)
    have h1 := h_eval (Phase2.env₁_1 bp) (Phase2.env₁_1_isMarkov bp)
    have h_sum : (∑ a : Fin 2, |(if a = 0 then (1 : ℝ) else 0) - (if a = 0 then (1 : ℝ) else 0)|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sub_self, abs_zero]
    simp_rw [h0, h1]
    rw [h_sum]
    ring
  rw [h_seq]
  simp [Filter.limsup_const]

instance alg4_ucb_pol0_isDet : Phase2.AlgIsDeterministic (alg4_ucb (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg4_lacks_x1 (bp : Phase2.BanditParam) :
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp)
      (alg4_ucb (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp)
      (Phase2.env₁_1_isMarkov bp) (alg4_isMarkov (Fin 2) Bool pol0)) := by
  unfold LacksX₁
  refine ⟨0, by norm_num, ?_⟩
  have h_seq : (fun t => Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg4_ucb (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg4_isMarkov (Fin 2) Bool pol0) t) = fun _ => 0 := by
    ext t
    unfold Phase3.miSeq Phase3.tvDistMeasure
    have h_eval : ∀ (env' : SixPrimitives.Env Unit (Fin 2) Bool) (hEnv' : Phase2.EnvIsMarkov env'),
        ∀ a : Fin 2, ((Phase2.actionMarginal env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg4_isMarkov (Fin 2) Bool pol0) (t + 1) ⟨t, Nat.lt_succ_self t⟩) {a}).toReal = if a = 0 then 1 else 0 := by
      intro env' hEnv' a
      dsimp [Phase2.actionMarginal]
      have h_meas_act : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) :=
        Phase2.measurable_traj_action t (Nat.lt_succ_self t)
      rw [MeasureTheory.Measure.map_apply h_meas_act (measurableSet_singleton a)]
      have h_ae := Phase2.traj_action_ae_eq_actFn env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas t (t + 1) (Nat.lt_succ_self t) hEnv'
      by_cases ha : a = 0
      · subst ha
        have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∈ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0} := by
          filter_upwards [h_ae] with ω hω
          exact hω
        haveI h_prob := Phase2.trajMeasure_isProbability env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg4_isMarkov (Fin 2) Bool pol0) (t + 1)
        have h_meas_one : (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) = 1 := by
          have h_compl : (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_eq
          have h_union : (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) ∪ ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) + (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) := MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl (h_meas_act (measurableSet_singleton 0)))
          rw [Set.union_compl_self, h_prob.measure_univ, h_compl, add_zero] at h_union
          exact h_union.symm
        simp [h_meas_one]
      · have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a} := by
          filter_upwards [h_ae] with ω hω
          intro h_contra
          change (ω ⟨t, Nat.lt_succ_self t⟩).1 = a at h_contra
          have h_act_eq_0 : (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := hω
          rw [h_act_eq_0] at h_contra
          exact ha h_contra.symm
        have h_meas_zero : (Phase2.trajMeasure env' (alg4_ucb (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) = 0 := by
          have h_zero := MeasureTheory.ae_iff.mp h_ae_eq
          have h_set_eq : {a_1 : Phase2.Trajectory (Fin 2) Bool (t + 1) | ¬a_1 ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}} = ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) := by ext x; simp
          rwa [h_set_eq] at h_zero
        simp [ha, h_meas_zero]
    have h0 := h_eval (Phase2.env₁_0 bp) (Phase2.env₁_0_isMarkov bp)
    have h1 := h_eval (Phase2.env₁_1 bp) (Phase2.env₁_1_isMarkov bp)
    have h_sum : (∑ a : Fin 2, |(if a = 0 then (1 : ℝ) else 0) - (if a = 0 then (1 : ℝ) else 0)|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sub_self, abs_zero]
    simp_rw [h0, h1]
    rw [h_sum]
    ring
  rw [h_seq]
  simp [Filter.limsup_const]

instance alg5_feas_pol0_isDet : Phase2.AlgIsDeterministic (alg5_feas (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg5_lacks_x1 (bp : Phase2.BanditParam) :
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp)
      (alg5_feas (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp)
      (Phase2.env₁_1_isMarkov bp) (alg5_isMarkov (Fin 2) Bool pol0)) := by
  unfold LacksX₁
  refine ⟨0, by norm_num, ?_⟩
  have h_seq : (fun t => Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg5_feas (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg5_isMarkov (Fin 2) Bool pol0) t) = fun _ => 0 := by
    ext t
    unfold Phase3.miSeq Phase3.tvDistMeasure
    have h_eval : ∀ (env' : SixPrimitives.Env Unit (Fin 2) Bool) (hEnv' : Phase2.EnvIsMarkov env'),
        ∀ a : Fin 2, ((Phase2.actionMarginal env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg5_isMarkov (Fin 2) Bool pol0) (t + 1) ⟨t, Nat.lt_succ_self t⟩) {a}).toReal = if a = 0 then 1 else 0 := by
      intro env' hEnv' a
      dsimp [Phase2.actionMarginal]
      have h_meas_act : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) :=
        Phase2.measurable_traj_action t (Nat.lt_succ_self t)
      rw [MeasureTheory.Measure.map_apply h_meas_act (measurableSet_singleton a)]
      have h_ae := Phase2.traj_action_ae_eq_actFn env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas t (t + 1) (Nat.lt_succ_self t) hEnv'
      by_cases ha : a = 0
      · subst ha
        have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∈ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0} := by
          filter_upwards [h_ae] with ω hω
          exact hω
        haveI h_prob := Phase2.trajMeasure_isProbability env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg5_isMarkov (Fin 2) Bool pol0) (t + 1)
        have h_meas_one : (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) = 1 := by
          have h_compl : (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_eq
          have h_union : (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) ∪ ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) + (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) := MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl (h_meas_act (measurableSet_singleton 0)))
          rw [Set.union_compl_self, h_prob.measure_univ, h_compl, add_zero] at h_union
          exact h_union.symm
        simp [h_meas_one]
      · have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a} := by
          filter_upwards [h_ae] with ω hω
          intro h_contra
          change (ω ⟨t, Nat.lt_succ_self t⟩).1 = a at h_contra
          have h_act_eq_0 : (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := hω
          rw [h_act_eq_0] at h_contra
          exact ha h_contra.symm
        have h_meas_zero : (Phase2.trajMeasure env' (alg5_feas (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) = 0 := by
          have h_zero := MeasureTheory.ae_iff.mp h_ae_eq
          have h_set_eq : {a_1 : Phase2.Trajectory (Fin 2) Bool (t + 1) | ¬a_1 ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}} = ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) := by ext x; simp
          rwa [h_set_eq] at h_zero
        simp [ha, h_meas_zero]
    have h0 := h_eval (Phase2.env₁_0 bp) (Phase2.env₁_0_isMarkov bp)
    have h1 := h_eval (Phase2.env₁_1 bp) (Phase2.env₁_1_isMarkov bp)
    have h_sum : (∑ a : Fin 2, |(if a = 0 then (1 : ℝ) else 0) - (if a = 0 then (1 : ℝ) else 0)|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sub_self, abs_zero]
    simp_rw [h0, h1]
    rw [h_sum]
    ring
  rw [h_seq]
  simp [Filter.limsup_const]

instance alg6_shortMem_pol0_isDet : Phase2.AlgIsDeterministic (alg6_shortMem (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg6_lacks_x1 (bp : Phase2.BanditParam) :
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp)
      (alg6_shortMem (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp)
      (Phase2.env₁_1_isMarkov bp) (alg6_isMarkov (Fin 2) Bool pol0)) := by
  unfold LacksX₁
  refine ⟨0, by norm_num, ?_⟩
  have h_seq : (fun t => Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg6_shortMem (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg6_isMarkov (Fin 2) Bool pol0) t) = fun _ => 0 := by
    ext t
    unfold Phase3.miSeq Phase3.tvDistMeasure
    have h_eval : ∀ (env' : SixPrimitives.Env Unit (Fin 2) Bool) (hEnv' : Phase2.EnvIsMarkov env'),
        ∀ a : Fin 2, ((Phase2.actionMarginal env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg6_isMarkov (Fin 2) Bool pol0) (t + 1) ⟨t, Nat.lt_succ_self t⟩) {a}).toReal = if a = 0 then 1 else 0 := by
      intro env' hEnv' a
      dsimp [Phase2.actionMarginal]
      have h_meas_act : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) :=
        Phase2.measurable_traj_action t (Nat.lt_succ_self t)
      rw [MeasureTheory.Measure.map_apply h_meas_act (measurableSet_singleton a)]
      have h_ae := Phase2.traj_action_ae_eq_actFn env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas t (t + 1) (Nat.lt_succ_self t) hEnv'
      by_cases ha : a = 0
      · subst ha
        have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∈ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0} := by
          filter_upwards [h_ae] with ω hω
          exact hω
        haveI h_prob := Phase2.trajMeasure_isProbability env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas hEnv' (alg6_isMarkov (Fin 2) Bool pol0) (t + 1)
        have h_meas_one : (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) = 1 := by
          have h_compl : (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_eq
          have h_union : (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) ∪ ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) = (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0}) + (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) (((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {0})ᶜ) := MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl (h_meas_act (measurableSet_singleton 0)))
          rw [Set.union_compl_self, h_prob.measure_univ, h_compl, add_zero] at h_union
          exact h_union.symm
        simp [h_meas_one]
      · have h_ae_eq : ∀ᵐ ω ∂(Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)), ω ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a} := by
          filter_upwards [h_ae] with ω hω
          intro h_contra
          change (ω ⟨t, Nat.lt_succ_self t⟩).1 = a at h_contra
          have h_act_eq_0 : (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := hω
          rw [h_act_eq_0] at h_contra
          exact ha h_contra.symm
        have h_meas_zero : (Phase2.trajMeasure env' (alg6_shortMem (Fin 2) Bool pol0) env'.hr_meas (t + 1)) ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) = 0 := by
          have h_zero := MeasureTheory.ae_iff.mp h_ae_eq
          have h_set_eq : {a_1 : Phase2.Trajectory (Fin 2) Bool (t + 1) | ¬a_1 ∉ (fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}} = ((fun traj : Phase2.Trajectory (Fin 2) Bool (t + 1) => (traj ⟨t, Nat.lt_succ_self t⟩).1) ⁻¹' {a}) := by ext x; simp
          rwa [h_set_eq] at h_zero
        simp [ha, h_meas_zero]
    have h0 := h_eval (Phase2.env₁_0 bp) (Phase2.env₁_0_isMarkov bp)
    have h1 := h_eval (Phase2.env₁_1 bp) (Phase2.env₁_1_isMarkov bp)
    have h_sum : (∑ a : Fin 2, |(if a = 0 then (1 : ℝ) else 0) - (if a = 0 then (1 : ℝ) else 0)|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sub_self, abs_zero]
    simp_rw [h0, h1]
    rw [h_sum]
    ring
  rw [h_seq]
  simp [Filter.limsup_const]

-- 2. Home Turf: env2 (Lacks X₂)

lemma oneStepKernel_peel_action_gen
    {S A O Sig : Type}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass A] [MeasurableEq A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (σs : Sig × S) (a_target : A) :
    (Phase2.oneStepKernel env alg hr σs {step | step.1 = a_target}) =
    alg.act σs.1 {a_target} := by
  classical
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have h_meas_upd : Measurable (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) := by measurability
  have h_meas_trans : Measurable (fun x : (Sig × S) × ((A × O) × ℝ) => (x.1.2, x.2.1.1)) := by measurability
  have h_meas_rew : Measurable (fun x : (Sig × S) × (A × O) => (x.1.2, x.2.1)) := by measurability
  have h_meas_obs : Measurable (fun x : (Sig × S) × A => (x.1.2, x.2)) := by measurability
  simp only [Phase2.oneStepKernel]
  have h_map : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {step : A × O × ℝ × Sig × S | step.1 = a_target} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun p : ((((A × O) × ℝ) × S) × Sig) => (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) ⁻¹' {step | step.1 = a_target} = {p | p.1.1.1.1 = a_target} := rfl
  have hs1 : MeasurableSet {p : ((((A × O) × ℝ) × S) × Sig) | p.1.1.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))) measurable_const
  rw [h_pre, Kernel.compProd_apply hs1]
  have h_upd_int : ∀ b : (((A × O) × ℝ) × S),
      alg.update.comap (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) h_meas_upd (σs, b) (Prod.mk b ⁻¹' {p : ((((A × O) × ℝ) × S) × Sig) | p.1.1.1.1 = a_target}) =
      if b.1.1.1 = a_target then 1 else 0 := by
    intro b
    by_cases hb : b.1.1.1 = a_target
    · have h_univ : Prod.mk b ⁻¹' {p : ((((A × O) × ℝ) × S) × Sig) | p.1.1.1.1 = a_target} = Set.univ := by ext c; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hb
      rw [h_univ]
      simp only [hb, if_true]
      exact measure_univ
    · have h_empty : Prod.mk b ⁻¹' {p : ((((A × O) × ℝ) × S) × Sig) | p.1.1.1.1 = a_target} = ∅ := by ext c; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hb
      rw [h_empty]
      simp only [hb, if_false]
      exact measure_empty
  rw [lintegral_congr h_upd_int]
  have hs2 : MeasurableSet {b : (((A × O) × ℝ) × S) | b.1.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_fst.comp measurable_fst)) measurable_const
  have h_ind_eq2 : (fun b : (((A × O) × ℝ) × S) => if b.1.1.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {b' : (((A × O) × ℝ) × S) | b'.1.1.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext b; by_cases hb : b.1.1.1 = a_target <;> simp [hb]
  rw [h_ind_eq2, lintegral_indicator_const hs2, one_mul]
  rw [Kernel.compProd_apply hs2]
  have h_trans_int : ∀ c : ((A × O) × ℝ),
      env.trans.comap (fun x : (Sig × S) × ((A × O) × ℝ) => (x.1.2, x.2.1.1)) h_meas_trans (σs, c) (Prod.mk c ⁻¹' {b : (((A × O) × ℝ) × S) | b.1.1.1 = a_target}) =
      if c.1.1 = a_target then 1 else 0 := by
    intro c
    by_cases hc : c.1.1 = a_target
    · have h_univ : Prod.mk c ⁻¹' {b : (((A × O) × ℝ) × S) | b.1.1.1 = a_target} = Set.univ := by ext s'; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hc
      rw [h_univ]
      simp only [hc, if_true]
      exact measure_univ
    · have h_empty : Prod.mk c ⁻¹' {b : (((A × O) × ℝ) × S) | b.1.1.1 = a_target} = ∅ := by ext s'; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hc
      rw [h_empty]
      simp only [hc, if_false]
      exact measure_empty
  rw [lintegral_congr h_trans_int]
  have hs3 : MeasurableSet {c : ((A × O) × ℝ) | c.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const
  have h_ind_eq3 : (fun c : ((A × O) × ℝ) => if c.1.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {c' : ((A × O) × ℝ) | c'.1.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext c; by_cases hc : c.1.1 = a_target <;> simp [hc]
  rw [h_ind_eq3, lintegral_indicator_const hs3, one_mul]
  rw [Kernel.compProd_apply hs3]
  have h_rew_int : ∀ d : (A × O),
      Kernel.deterministic (fun x : (Sig × S) × (A × O) => env.r (x.1.2, x.2.1)) (hr.comp h_meas_rew) (σs, d) (Prod.mk d ⁻¹' {c : ((A × O) × ℝ) | c.1.1 = a_target}) =
      if d.1 = a_target then 1 else 0 := by
    intro d
    by_cases hd : d.1 = a_target
    · have h_univ : Prod.mk d ⁻¹' {c : ((A × O) × ℝ) | c.1.1 = a_target} = Set.univ := by ext r; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hd
      rw [h_univ]
      simp only [hd, if_true, Kernel.deterministic_apply]
      exact measure_univ
    · have h_empty : Prod.mk d ⁻¹' {c : ((A × O) × ℝ) | c.1.1 = a_target} = ∅ := by ext r; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hd
      rw [h_empty]
      simp only [hd, if_false, Kernel.deterministic_apply]
      exact measure_empty
  rw [lintegral_congr h_rew_int]
  have hs4 : MeasurableSet {d : A × O | d.1 = a_target} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have h_ind_eq4 : (fun d : A × O => if d.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {d' : A × O | d'.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext d; by_cases hd : d.1 = a_target <;> simp [hd]
  rw [h_ind_eq4, lintegral_indicator_const hs4, one_mul]
  rw [Kernel.compProd_apply hs4]
  have h_obs_int : ∀ a : A,
      (env.obs.comap (fun x : (Sig × S) × A => (x.1.2, x.2)) h_meas_obs (σs, a)) (Prod.mk a ⁻¹' {d : A × O | d.1 = a_target}) =
      if a = a_target then 1 else 0 := by
    intro a
    by_cases ha : a = a_target
    · have h_univ : Prod.mk a ⁻¹' {d : A × O | d.1 = a_target} = Set.univ := by ext o; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact ha
      rw [h_univ]
      simp only [ha, if_true]
      exact measure_univ
    · have h_empty : Prod.mk a ⁻¹' {d : A × O | d.1 = a_target} = ∅ := by ext o; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact ha
      rw [h_empty]
      simp only [ha, if_false]
      exact measure_empty
  rw [lintegral_congr h_obs_int]
  have hs5 : MeasurableSet {a : A | a = a_target} :=
    measurableSet_eq_fun measurable_id measurable_const
  have h_ind_eq5 : (fun a : A => if a = a_target then (1 : ℝ≥0∞) else 0) =
      {a' : A | a' = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext a; by_cases ha : a = a_target <;> simp [ha]
  rw [h_ind_eq5, lintegral_indicator_const hs5, one_mul]
  simp only [Kernel.comap_apply]
  have h_eq_set : {a : A | a = a_target} = {a_target} := by ext; simp
  rw [h_eq_set]

lemma pol_eps_apply (a : Fin 2) : pol_eps () {a} = 1 / 2 := by
  simp only [pol_eps, Kernel.const_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have h_meas : MeasurableSet ({a} : Set (Fin 2)) := measurableSet_singleton a
  rw [Measure.dirac_apply' (0 : Fin 2) h_meas, Measure.dirac_apply' (1 : Fin 2) h_meas]
  fin_cases a
  · simp
  · simp

lemma canonical_intersection_prob (k : ℕ) (a_target : Fin 2) :
    ((Phase2.trajMeasure (Phase2.env₂ K hK) (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (Phase2.env₂ K hK).hr_meas (k+1))
      (Phase2.survivedToStep K hK k ∩ { ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = a_target })).toReal =
    (1 / 2) * Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k := by
  dsimp [Phase2.survivalProbSeq]
  let env := Phase2.env₂ K hK
  let alg := canonical_challenger (Fin 2) (Fin (K+2)) pol_eps
  let hr := env.hr_meas
  have hEnv : Phase2.EnvIsMarkov env := Phase2.envIsDeterministic_isMarkov env (Phase2.env₂_isDet K hK)
  have hAlg : Phase2.AlgIsMarkov alg := canonical_challenger_isMarkov _ _ pol_eps
  let hTrans := (Phase2.env₂_isDet K hK).toTrans
  let surv_set := Phase2.survivedToStep K hK k
  let target_set := { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+1) | (ω ⟨k, Nat.lt_succ_self k⟩).1 = a_target }
  have h_meas_surv : MeasurableSet surv_set := measurableSet_survivedToStep K hK k
  have h_meas_target : MeasurableSet target_set :=
    (Phase2.measurable_traj_action k (Nat.lt_succ_self k)) (measurableSet_singleton a_target)
  have h_meas_inter : MeasurableSet (surv_set ∩ target_set) := MeasurableSet.inter h_meas_surv h_meas_target
  let μ₀ := (Measure.dirac alg.σ₀).prod env.μ₀
  let M := fun n => μ₀.bind (Phase2.trajMeasureAux env alg hr n)
  have h_M_inter : Phase2.trajMeasure env alg hr (k+1) (surv_set ∩ target_set) = M (k+1) { x | x.1 ∈ surv_set ∩ target_set } := by
    dsimp [Phase2.trajMeasure, M]; rw [Measure.map_apply measurable_fst h_meas_inter]; rfl
  have h_M_surv : Phase2.trajMeasure env alg hr (k+1) surv_set = M (k+1) { x | x.1 ∈ surv_set } := by
    dsimp [Phase2.trajMeasure, M]; rw [Measure.map_apply measurable_fst h_meas_surv]; rfl
  have h_step : M (k+1) { x | x.1 ∈ surv_set ∩ target_set } = (1 / 2 : ℝ≥0∞) * M (k+1) { x | x.1 ∈ surv_set } := by
    dsimp [M]
    have h_set1 : MeasurableSet { x : (Fin (k+1) → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2) | x.1 ∈ surv_set ∩ target_set } := measurable_fst h_meas_inter
    have h_set2 : MeasurableSet { x : (Fin (k+1) → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2) | x.1 ∈ surv_set } := measurable_fst h_meas_surv
    rw [Measure.bind_apply h_set1 (Kernel.measurable _).aemeasurable]
    rw [Measure.bind_apply h_set2 (Kernel.measurable _).aemeasurable]
    have h_inner : ∀ σs, Phase2.trajMeasureAux env alg hr (k+1) σs { x | x.1 ∈ surv_set ∩ target_set } =
                         (1 / 2 : ℝ≥0∞) * Phase2.trajMeasureAux env alg hr (k+1) σs { x | x.1 ∈ surv_set } := by
      intro σs
      haveI h_osk : IsMarkovKernel (Phase2.oneStepKernel env alg hr) := Phase2.oneStepKernel_isMarkov env alg hr hEnv hAlg
      simp only [Phase2.trajMeasureAux]
      let f : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × (Unit × Fin (K+2))) × (Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) → (Fin (k+1) → Fin 2 × Fin (K+2) × ℝ) × (Unit × Fin (K+2)) :=
        fun p => (Fin.snoc (α := fun _ => Fin 2 × Fin (K+2) × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), (p.2.2.2.2.1, p.2.2.2.2.2))
      have hf : Measurable f := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
          · simp; fun_prop
          · intro j; simp; fun_prop
        · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
                (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      change Kernel.map _ f σs _ = (1 / 2 : ℝ≥0∞) * Kernel.map _ f σs _
      rw [Kernel.map_apply (hf := hf)]
      rw [Measure.map_apply hf h_set1, Measure.map_apply hf h_set2]
      have h_pre1 : f ⁻¹' { x | x.1 ∈ surv_set ∩ target_set } = { p | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target } := by
        ext p
        change Phase2.state_t env hTrans (Fin.snoc p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1)) k ≠ Fin.last (K+1) ∧ (Fin.snoc (α := fun _ => Fin 2 × Fin (K+2) × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1) ⟨k, Nat.lt_succ_self k⟩).1 = a_target ↔ Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target
        have h_snoc1 : Phase2.state_t env hTrans (Fin.snoc p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1)) k = Phase2.state_t env hTrans p.1.1 k := Phase2.state_t_snoc env hTrans p.1.1 _ k (le_refl k)
        have h_snoc2 : (Fin.snoc (α := fun _ => Fin 2 × Fin (K+2) × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1) ⟨k, Nat.lt_succ_self k⟩).1 = p.2.1 := by
          have h_last : (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1)) = Fin.last k := rfl
          rw [h_last, Fin.snoc_last]
        rw [h_snoc1, h_snoc2]
      have h_pre2 : f ⁻¹' { x | x.1 ∈ surv_set } = { p | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) } := by
        ext p
        change Phase2.state_t env hTrans (Fin.snoc p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1)) k ≠ Fin.last (K+1) ↔ Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1)
        have h_snoc1 : Phase2.state_t env hTrans (Fin.snoc p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1)) k = Phase2.state_t env hTrans p.1.1 k := Phase2.state_t_snoc env hTrans p.1.1 _ k (le_refl k)
        rw [h_snoc1]
      rw [h_pre1, h_pre2]
      haveI : IsMarkovKernel ((Phase2.oneStepKernel env alg hr).comap (fun x : (Unit × Fin (K+2)) × ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => x.2.2) (by measurability)) := Kernel.IsMarkovKernel.comap _ _
      have h_meas_pre1 : MeasurableSet { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target } := by
        have hm_state : Measurable (fun p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) => Phase2.state_t env hTrans p.1.1 k) :=
          (Phase2.measurable_state_t env hTrans k k).comp (measurable_fst.comp measurable_fst)
        have hm_state_ne := hm_state (MeasurableSet.compl (measurableSet_singleton (Fin.last (K+1))))
        have hm_a : Measurable (fun p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) => p.2.1) :=
          measurable_fst.comp measurable_snd
        have hm_a_eq := hm_a (measurableSet_singleton a_target)
        exact MeasurableSet.inter hm_state_ne hm_a_eq
      have h_meas_pre2 : MeasurableSet { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) } := by
        have hm_state : Measurable (fun p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) => Phase2.state_t env hTrans p.1.1 k) :=
          (Phase2.measurable_state_t env hTrans k k).comp (measurable_fst.comp measurable_fst)
        exact hm_state (MeasurableSet.compl (measurableSet_singleton (Fin.last (K+1))))
      haveI hTm : IsMarkovKernel (Phase2.trajMeasureAux env alg hr k) := Phase2.trajMeasureAux_isMarkov env alg hr hEnv hAlg k
      haveI h_sfin : IsSFiniteKernel (Phase2.trajMeasureAux env alg hr k) := inferInstance
      rw [Kernel.compProd_apply h_meas_pre1, Kernel.compProd_apply h_meas_pre2]
      have h_inner_int : ∀ a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)),
        (Phase2.oneStepKernel env alg hr).comap (fun x : (Unit × Fin (K+2)) × ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => x.2.2) (by measurability) (σs, a) (Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target }) =
        if Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) then (1/2 : ℝ≥0∞) else 0 := by
        intro a
        by_cases ha : Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1)
        · rw [if_pos ha]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target } = { step : Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2) | step.1 = a_target } := by ext step; simp [ha]
          rw [h_prod]
          rw [oneStepKernel_peel_action_gen env alg hr hEnv hAlg a.2 a_target]
          exact pol_eps_apply a_target
        · rw [if_neg ha]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) ∧ p.2.1 = a_target } = ∅ := by ext step; simp [ha]
          rw [h_prod, measure_empty]
      have h_inner_int2 : ∀ a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)),
        (Phase2.oneStepKernel env alg hr).comap (fun x : (Unit × Fin (K+2)) × ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => x.2.2) (by measurability) (σs, a) (Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) }) =
        if Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) then (1 : ℝ≥0∞) else 0 := by
        intro a
        by_cases ha : Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1)
        · rw [if_pos ha]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) } = Set.univ := by ext (step : Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)); simp [ha]
          rw [h_prod, measure_univ]
        · rw [if_neg ha]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk a ⁻¹' { p : (((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) × Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)) | Phase2.state_t env hTrans p.1.1 k ≠ Fin.last (K+1) } = ∅ := by ext (step : Fin 2 × Fin (K+2) × ℝ × Unit × Fin (K+2)); simp [ha]
          rw [h_prod, measure_empty]
      rw [lintegral_congr h_inner_int, lintegral_congr h_inner_int2]
      have h_ind1 : (fun a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => if Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) then (1/2 : ℝ≥0∞) else 0) =
                    { a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) | Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) }.indicator (fun _ => (1/2 : ℝ≥0∞)) := by ext a; by_cases ha : Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) <;> simp [ha]
      have h_ind2 : (fun a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => if Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) then (1 : ℝ≥0∞) else 0) =
                    { a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) | Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) }.indicator (fun _ => 1) := by ext a; by_cases ha : Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) <;> simp [ha]
      have h_meas_A : MeasurableSet { a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) | Phase2.state_t env hTrans a.1 k ≠ Fin.last (K+1) } := by
        have h_meas_state : Measurable (fun a : ((Fin k → Fin 2 × Fin (K+2) × ℝ) × Unit × Fin (K+2)) => Phase2.state_t env hTrans a.1 k) :=
          (Phase2.measurable_state_t env hTrans k k).comp measurable_fst
        exact h_meas_state (MeasurableSet.compl (measurableSet_singleton _))
      rw [h_ind1, h_ind2]
      rw [lintegral_indicator_const h_meas_A, lintegral_indicator_const h_meas_A]
      simp
    rw [lintegral_congr h_inner]
    rw [lintegral_const_mul _ (Kernel.measurable_coe _ h_set2)]
  rw [h_M_inter, h_M_surv, h_step, ENNReal.toReal_mul]
  have h_half : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num
  rw [h_half]

lemma canonical_dangerAndSurvival (k : ℕ) :
    Phase2.dangerAndSurvivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K) k =
    (1 / 2) * Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k := by
  dsimp [Phase2.dangerAndSurvivalProbSeq]
  have h_danger_eq : ∀ s, env₂_dangerAction K s = 1 := fun _ => rfl
  have h_set_rewrite : { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+1) |
    (ω ⟨k, Nat.lt_succ_self k⟩).1 = env₂_dangerAction K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) } = { ω |
    (ω ⟨k, Nat.lt_succ_self k⟩).1 = 1 } := by
    ext ω;
    simp [h_danger_eq]
  rw [h_set_rewrite]
  exact canonical_intersection_prob K hK k 1

lemma survivedToStep_subset_safe_lemma (k : ℕ) :
    { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+2) | (fun i => ω (Fin.castSucc i)) ∈ Phase2.survivedToStep K hK k ∧ (ω ⟨k, by omega⟩).1 = 0 } ⊆
    Phase2.survivedToStep K hK (k+1) := by
  rintro ω ⟨h_surv, h_safe⟩
  simp only [Phase2.survivedToStep, Set.mem_setOf_eq] at h_surv ⊢
  have h_state_k : ∀ t ≤ k, Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (fun i : Fin (k + 1) => ω (Fin.castSucc i)) t = Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      have ht_lt : t < k + 1 := by omega
      have ht_lt_k2 : t < k + 2 := by omega
      rw [Phase2.state_t_succ _ _ _ t ht_lt, Phase2.state_t_succ _ _ _ t ht_lt_k2, ih (by omega)]
      rfl
  rw [h_state_k k (le_refl k)] at h_surv
  have h_succ : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (k + 1) =
    (Phase2.env₂_isDet K hK).toTrans.transFn (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k, (ω ⟨k, by omega⟩).1) := Phase2.state_t_succ _ _ _ k (by omega)
  rw [h_succ, h_safe]
  intro contra
  have h_trans_safe : ∀ s : Fin (K+2), s ≠ Fin.last (K+1) → (Phase2.env₂_isDet K hK).toTrans.transFn (s, 0) ≠ Fin.last (K+1) := by
    intro s hs
    rw [env₂_transFn_eq]
    by_cases h_lt : s.val < K
    · rw [dif_pos h_lt, if_pos rfl]
      intro hc
      have h_val : s.val + 1 = K + 1 := congrArg Fin.val hc
      omega
    · rw [dif_neg h_lt]
      exact hs
  exact h_trans_safe _ h_surv contra

lemma canonical_surv_pos (k : ℕ) :
    0 < Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k := by
  induction k with
  | zero =>
    rw [survivalProbSeq_zero K hK _ _]
    norm_num
  | succ k ih =>
    have h_inter := canonical_intersection_prob K hK k 0
    let S_k := { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+2) | (fun i => ω (Fin.castSucc i)) ∈ Phase2.survivedToStep K hK k }
    let Target := { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+2) | (ω ⟨k, by omega⟩).1 = 0 }
    have h_subset : S_k ∩ Target ⊆ Phase2.survivedToStep K hK (k+1) := survivedToStep_subset_safe_lemma K hK k
    have h_meas_surv : MeasurableSet (Phase2.survivedToStep K hK k) := measurableSet_survivedToStep K hK k
    have h_meas_Sk : MeasurableSet S_k := by
      have h_meas : Measurable (fun ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+2) => fun i : Fin (k+1) => ω (Fin.castSucc i)) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
      exact h_meas h_meas_surv
    have h_meas_Target : MeasurableSet Target := (Phase2.measurable_traj_action k (by omega)) (measurableSet_singleton 0)
    let μ_k2 := Phase2.trajMeasure (Phase2.env₂ K hK) (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (Phase2.env₂ K hK).hr_meas (k+2)
    have h_mono : μ_k2 (S_k ∩ Target) ≤ μ_k2 (Phase2.survivedToStep K hK (k+1)) := measure_mono h_subset
    have hEnv : Phase2.EnvIsMarkov (Phase2.env₂ K hK) := Phase2.envIsDeterministic_isMarkov (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK)
    have hAlg : Phase2.AlgIsMarkov (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) := canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps
    haveI h_prob : IsProbabilityMeasure μ_k2 := Phase2.trajMeasure_isProbability _ _ _ hEnv hAlg (k+2)
    have h_trunc := Phase2.trajMeasure_truncation (Phase2.env₂ K hK) (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (Phase2.env₂ K hK).hr_meas hEnv hAlg (k+2) (k+1) (by omega) (Phase2.survivedToStep K hK k ∩ { ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = 0 }) (MeasurableSet.inter h_meas_surv ((Phase2.measurable_traj_action k (Nat.lt_succ_self k)) (measurableSet_singleton 0)))
    have h_trunc_eq : μ_k2 (S_k ∩ Target) = Phase2.trajMeasure (Phase2.env₂ K hK) (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (Phase2.env₂ K hK).hr_meas (k+1) (Phase2.survivedToStep K hK k ∩ { ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = 0 }) := by
      have h_eq : S_k ∩ Target = { ω : Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+2) | (fun i => ω (Fin.castLE (by omega) i)) ∈ Phase2.survivedToStep K hK k ∩ { ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = 0 } } := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, S_k, Target]
        have h_cast : Fin.castLE (by omega) ⟨k, Nat.lt_succ_self k⟩ = (⟨k, by omega⟩ : Fin (k+2)) := by ext; rfl
        rw [h_cast]
        rfl
      rw [h_eq]
      exact h_trunc
    have h_le : (1 / 2 : ℝ) * Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k ≤ Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (k+1) := by
      rw [← h_inter]
      unfold Phase2.survivalProbSeq
      rw [← h_trunc_eq]
      exact ENNReal.toReal_mono (measure_ne_top μ_k2 _) h_mono
    calc 0 < (1 / 2 : ℝ) * Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k := mul_pos (by norm_num) ih
      _ ≤ Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (k+1) := h_le

lemma canonical_challenger_lacks_x2 :
    LacksX₂ (Phase2.condDangerProbSeq K hK
      (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps)
      (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps)
      (env₂_dangerAction K)) := by
  unfold LacksX₂
  use 1 / 2
  constructor
  · norm_num
  · intro k
    unfold Phase2.condDangerProbSeq
    have h_surv_pos := canonical_surv_pos K hK k
    have h_surv_ne_zero : Phase2.survivalProbSeq K hK (canonical_challenger (Fin 2) (Fin (K+2)) pol_eps) (canonical_challenger_isMarkov (Fin 2) (Fin (K+2)) pol_eps) k ≠ 0 :=
      ne_of_gt h_surv_pos
    rw [if_neg h_surv_ne_zero]
    have h_danger_joint := canonical_dangerAndSurvival K hK k
    rw [h_danger_joint]
    exact mul_div_cancel_right₀ (1 / 2 : ℝ) h_surv_ne_zero |>.ge

lemma alg1_lacks_x2 : LacksX₂ (Phase2.condDangerProbSeq K hK (alg1_bayes (Fin 2) (Fin (K+2)) pol_eps) (alg1_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) := canonical_challenger_lacks_x2 K hK
lemma alg3_lacks_x2 : LacksX₂ (Phase2.condDangerProbSeq K hK (alg3_bridge (Fin 2) (Fin (K+2)) pol_eps) (alg3_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) := canonical_challenger_lacks_x2 K hK
lemma alg4_lacks_x2 : LacksX₂ (Phase2.condDangerProbSeq K hK (alg4_ucb (Fin 2) (Fin (K+2)) pol_eps) (alg4_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) := canonical_challenger_lacks_x2 K hK
lemma alg5_lacks_x2 : LacksX₂ (Phase2.condDangerProbSeq K hK (alg5_feas (Fin 2) (Fin (K+2)) pol_eps) (alg5_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) := canonical_challenger_lacks_x2 K hK
lemma alg6_lacks_x2 : LacksX₂ (Phase2.condDangerProbSeq K hK (alg6_shortMem (Fin 2) (Fin (K+2)) pol_eps) (alg6_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) := canonical_challenger_lacks_x2 K hK

-- 3. Home Turf: env3 (Lacks X₃)

instance alg1_bayes_pol0_unit_isDet : Phase2.AlgIsDeterministic (alg1_bayes (Fin 2) Unit pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg1_lacks_x3 : LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) := by
  unfold LacksX₃
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  unfold Phase2.bridgeCumSeq
  have h_sum : (∑ t : Fin T, ((Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1}).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have h_ae := Phase2.traj_action_ae_eq_actFn (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas t.val T t.isLt (Phase2.env₃_isMarkov p hp0 hp1)
    have h_ae_not_1 : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T), ω ∉ {traj | (traj t).1 = 1} := by
      filter_upwards [h_ae] with ω hω h_contra
      change (ω t).1 = 0 at hω
      rw [hω] at h_contra
      exact absurd h_contra (by decide)
    have h_meas_zero : (Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1} = 0 := by
      have h_zero := MeasureTheory.ae_iff.mp h_ae_not_1
      have h_set_eq : {x : Phase2.Trajectory (Fin 2) Unit T | ¬x ∉ {traj | (traj t).1 = 1}} = {traj | (traj t).1 = 1} := by
        ext x
        simp only [Set.mem_setOf_eq, Classical.not_not]
      rwa [h_set_eq] at h_zero
    rw [h_meas_zero, ENNReal.toReal_zero]
  rw [h_sum]
  exact zero_le_one

instance alg2_safe_pol0_unit_isDet : Phase2.AlgIsDeterministic (alg2_safe (Fin 2) Unit pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg2_lacks_x3 : LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) := by
  unfold LacksX₃
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  unfold Phase2.bridgeCumSeq
  have h_sum : (∑ t : Fin T, ((Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1}).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have h_ae := Phase2.traj_action_ae_eq_actFn (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas t.val T t.isLt (Phase2.env₃_isMarkov p hp0 hp1)
    have h_ae_not_1 : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T), ω ∉ {traj | (traj t).1 = 1} := by
      filter_upwards [h_ae] with ω hω h_contra
      change (ω t).1 = 0 at hω
      rw [hω] at h_contra
      exact absurd h_contra (by decide)
    have h_meas_zero : (Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1} = 0 := by
      have h_zero := MeasureTheory.ae_iff.mp h_ae_not_1
      have h_set_eq : {x : Phase2.Trajectory (Fin 2) Unit T | ¬x ∉ {traj | (traj t).1 = 1}} = {traj | (traj t).1 = 1} := by
        ext x
        simp only [Set.mem_setOf_eq, Classical.not_not]
      rwa [h_set_eq] at h_zero
    rw [h_meas_zero, ENNReal.toReal_zero]
  rw [h_sum]
  exact zero_le_one

instance alg4_ucb_pol0_unit_isDet : Phase2.AlgIsDeterministic (alg4_ucb (Fin 2) Unit pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg4_lacks_x3 : LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) := by
  unfold LacksX₃
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  unfold Phase2.bridgeCumSeq
  have h_sum : (∑ t : Fin T, ((Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1}).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have h_ae := Phase2.traj_action_ae_eq_actFn (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas t.val T t.isLt (Phase2.env₃_isMarkov p hp0 hp1)
    have h_ae_not_1 : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T), ω ∉ {traj | (traj t).1 = 1} := by
      filter_upwards [h_ae] with ω hω h_contra
      change (ω t).1 = 0 at hω
      rw [hω] at h_contra
      exact absurd h_contra (by decide)
    have h_meas_zero : (Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1} = 0 := by
      have h_zero := MeasureTheory.ae_iff.mp h_ae_not_1
      have h_set_eq : {x : Phase2.Trajectory (Fin 2) Unit T | ¬x ∉ {traj | (traj t).1 = 1}} = {traj | (traj t).1 = 1} := by
        ext x
        simp only [Set.mem_setOf_eq, Classical.not_not]
      rwa [h_set_eq] at h_zero
    rw [h_meas_zero, ENNReal.toReal_zero]
  rw [h_sum]
  exact zero_le_one

instance alg5_feas_pol0_unit_isDet : Phase2.AlgIsDeterministic (alg5_feas (Fin 2) Unit pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg5_lacks_x3 : LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) := by
  unfold LacksX₃
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  unfold Phase2.bridgeCumSeq
  have h_sum : (∑ t : Fin T, ((Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1}).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have h_ae := Phase2.traj_action_ae_eq_actFn (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas t.val T t.isLt (Phase2.env₃_isMarkov p hp0 hp1)
    have h_ae_not_1 : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T), ω ∉ {traj | (traj t).1 = 1} := by
      filter_upwards [h_ae] with ω hω h_contra
      change (ω t).1 = 0 at hω
      rw [hω] at h_contra
      exact absurd h_contra (by decide)
    have h_meas_zero : (Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1} = 0 := by
      have h_zero := MeasureTheory.ae_iff.mp h_ae_not_1
      have h_set_eq : {x : Phase2.Trajectory (Fin 2) Unit T | ¬x ∉ {traj | (traj t).1 = 1}} = {traj | (traj t).1 = 1} := by
        ext x
        simp only [Set.mem_setOf_eq, Classical.not_not]
      rwa [h_set_eq] at h_zero
    rw [h_meas_zero, ENNReal.toReal_zero]
  rw [h_sum]
  exact zero_le_one

instance alg6_shortMem_pol0_unit_isDet : Phase2.AlgIsDeterministic (alg6_shortMem (Fin 2) Unit pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg6_lacks_x3 : LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) := by
  unfold LacksX₃
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  unfold Phase2.bridgeCumSeq
  have h_sum : (∑ t : Fin T, ((Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1}).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have h_ae := Phase2.traj_action_ae_eq_actFn (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas t.val T t.isLt (Phase2.env₃_isMarkov p hp0 hp1)
    have h_ae_not_1 : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T), ω ∉ {traj | (traj t).1 = 1} := by
      filter_upwards [h_ae] with ω hω h_contra
      change (ω t).1 = 0 at hω
      rw [hω] at h_contra
      exact absurd h_contra (by decide)
    have h_meas_zero : (Phase2.trajMeasure (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas T) {traj | (traj t).1 = 1} = 0 := by
      have h_zero := MeasureTheory.ae_iff.mp h_ae_not_1
      have h_set_eq : {x : Phase2.Trajectory (Fin 2) Unit T | ¬x ∉ {traj | (traj t).1 = 1}} = {traj | (traj t).1 = 1} := by
        ext x
        simp only [Set.mem_setOf_eq, Classical.not_not]
      rwa [h_set_eq] at h_zero
    rw [h_meas_zero, ENNReal.toReal_zero]
  rw [h_sum]
  exact zero_le_one

-- 4. Home Turf: env4 (Lacks X₄)

lemma env4_action_condExp_eq_half (t : ℕ) (a : Fin 2) :
    let alg := canonical_challenger (Fin 2) Unit pol_eps
    let μ := Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1)
    let X_lt := traj_prefix (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t)
    let A_t := Phase2.traj_action (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t)
    μ[(A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_lt inferInstance] =ᵐ[μ] fun _ => (1/2 : ℝ) := by
  intro alg μ X_lt A_t
  classical
  have hEnv : Phase2.EnvIsMarkov Phase2.env₄ := Phase2.envIsDeterministic_isMarkov Phase2.env₄ Phase2.env₄_isDet
  have hAlg : Phase2.AlgIsMarkov alg := canonical_challenger_isMarkov _ _ pol_eps
  haveI h_prob : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability Phase2.env₄ alg Phase2.env₄.hr_meas hEnv hAlg (t + 1)
  have h_X_meas : Measurable X_lt := measurable_traj_prefix t (Nat.lt_succ_self t)
  have h_A_meas : Measurable A_t := Phase2.measurable_traj_action t (Nat.lt_succ_self t)
  have h_comap_le : MeasurableSpace.comap X_lt inferInstance ≤ (inferInstance : MeasurableSpace (Phase2.Trajectory (Fin 2) Unit (t + 1))) := by
    rintro s' ⟨S', hS', rfl⟩
    exact h_X_meas hS'
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq h_comap_le
  · exact (integrable_const 1).indicator (h_A_meas (measurableSet_singleton a))
  · intro s' hs' _
    exact Integrable.integrableOn (integrable_const (1/2 : ℝ))
  · intro s' hs' _
    obtain ⟨S', hS', rfl⟩ := hs'
    change ∫ ω in X_lt ⁻¹' S', (1/2 : ℝ) ∂μ = ∫ ω in X_lt ⁻¹' S', (A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) ω ∂μ
    rw [setIntegral_indicator (h_A_meas (measurableSet_singleton a))]
    have h_lhs : ∫ ω in X_lt ⁻¹' S', (1/2 : ℝ) ∂μ = (μ (X_lt ⁻¹' S')).toReal * (1/2 : ℝ) := by
      rw [setIntegral_const, smul_eq_mul]
      rfl
    have h_rhs : ∫ ω in X_lt ⁻¹' S' ∩ A_t ⁻¹' {a}, (1 : ℝ) ∂μ = (μ (X_lt ⁻¹' S' ∩ A_t ⁻¹' {a})).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    rw [h_lhs, h_rhs]
    have h_measure_eq : μ (X_lt ⁻¹' S' ∩ A_t ⁻¹' {a}) = (1 / 2 : ℝ≥0∞) * μ (X_lt ⁻¹' S') := by
      dsimp [μ, Phase2.trajMeasure]
      let μ₀ := (Measure.dirac alg.σ₀).prod Phase2.env₄.μ₀
      let M := fun n => μ₀.bind (Phase2.trajMeasureAux Phase2.env₄ alg Phase2.env₄.hr_meas n)
      have h_meas_S : MeasurableSet (X_lt ⁻¹' S') := h_X_meas hS'
      have h_meas_A : MeasurableSet (A_t ⁻¹' {a}) := h_A_meas (measurableSet_singleton a)
      have h_meas_inter : MeasurableSet (X_lt ⁻¹' S' ∩ A_t ⁻¹' {a}) := MeasurableSet.inter h_meas_S h_meas_A
      rw [Measure.map_apply measurable_fst h_meas_inter]
      rw [Measure.map_apply measurable_fst h_meas_S]
      let proj : ((Fin (t+1) → Fin 2 × Unit × ℝ) × (Unit × Unit)) → Phase2.Trajectory (Fin 2) Unit (t+1) := Prod.fst
      let S_M := proj ⁻¹' (X_lt ⁻¹' S')
      let T_M := proj ⁻¹' (A_t ⁻¹' {a})
      have h_set1 : MeasurableSet S_M := measurable_fst h_meas_S
      have h_set2 : MeasurableSet T_M := measurable_fst h_meas_A
      have h_inter : proj ⁻¹' (X_lt ⁻¹' S' ∩ A_t ⁻¹' {a}) = S_M ∩ T_M := rfl
      rw [h_inter]
      dsimp [M]
      rw [Measure.bind_apply (MeasurableSet.inter h_set1 h_set2) (Kernel.measurable _).aemeasurable]
      rw [Measure.bind_apply h_set1 (Kernel.measurable _).aemeasurable]
      have h_meas_SM : Measurable (fun a => ((Phase2.trajMeasureAux Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1)) a) S_M) :=
        Kernel.measurable_coe _ h_set1
      rw [← lintegral_const_mul (1 / 2 : ℝ≥0∞) h_meas_SM]
      apply lintegral_congr
      intro σs
      haveI h_osk : IsMarkovKernel (Phase2.oneStepKernel Phase2.env₄ alg Phase2.env₄.hr_meas) := Phase2.oneStepKernel_isMarkov Phase2.env₄ alg Phase2.env₄.hr_meas hEnv hAlg
      simp only [Phase2.trajMeasureAux]
      let f : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × (Fin 2 × Unit × ℝ × Unit × Unit) → (Fin (t+1) → Fin 2 × Unit × ℝ) × (Unit × Unit) :=
        fun p => (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), (p.2.2.2.2.1, p.2.2.2.2.2))
      have hf : Measurable f := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
          · simp; fun_prop
          · intro j; simp; fun_prop
        · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
                (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      rw [Kernel.map_apply (hf := hf), Measure.map_apply hf (MeasurableSet.inter h_set1 h_set2)]
      rw [Measure.map_apply hf h_set1]
      have h_pre1 : f ⁻¹' (S_M ∩ T_M) = { p | p.1.1 ∈ S' ∧ p.2.1 = a } := by
        ext p
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
        change X_lt (proj (f p)) ∈ S' ∧ A_t (proj (f p)) = a ↔ p.1.1 ∈ S' ∧ p.2.1 = a
        have h_snoc1 : X_lt (proj (f p)) = p.1.1 := by
          funext i
          show (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1) : Fin (t+1) → Fin 2 × Unit × ℝ) (Fin.castSucc i) = p.1.1 i
          rw [Fin.snoc_castSucc]
        have h_snoc2 : A_t (proj (f p)) = p.2.1 := by
          show ((Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1) : Fin (t+1) → Fin 2 × Unit × ℝ) (Fin.last t)).1 = p.2.1
          rw [Fin.snoc_last]
        rw [h_snoc1, h_snoc2]
      have h_pre2 : f ⁻¹' S_M = { p | p.1.1 ∈ S' } := by
        ext p
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        change X_lt (proj (f p)) ∈ S' ↔ p.1.1 ∈ S'
        have h_snoc1 : X_lt (proj (f p)) = p.1.1 := by
          funext i
          show (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1) : Fin (t+1) → Fin 2 × Unit × ℝ) (Fin.castSucc i) = p.1.1 i
          rw [Fin.snoc_castSucc]
        rw [h_snoc1]
      rw [h_pre1, h_pre2]
      haveI : IsMarkovKernel ((Phase2.oneStepKernel Phase2.env₄ alg Phase2.env₄.hr_meas).comap (fun x : (Unit × Unit) × ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) => x.2.2) (by measurability)) := Kernel.IsMarkovKernel.comap _ _
      have h_meas_pre1 : MeasurableSet { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' ∧ p.2.1 = a } := by
        apply MeasurableSet.inter
        · exact (measurable_fst.comp measurable_fst) hS'
        · exact (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
      have h_meas_pre2 : MeasurableSet { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' } :=
        (measurable_fst.comp measurable_fst) hS'
      haveI hTm : IsMarkovKernel (Phase2.trajMeasureAux Phase2.env₄ alg Phase2.env₄.hr_meas t) := Phase2.trajMeasureAux_isMarkov _ _ _ hEnv hAlg t
      haveI h_sfin : IsSFiniteKernel (Phase2.trajMeasureAux Phase2.env₄ alg Phase2.env₄.hr_meas t) := inferInstance
      rw [Kernel.compProd_apply h_meas_pre1, Kernel.compProd_apply h_meas_pre2]
      have h_inner_int : ∀ c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)),
        (Phase2.oneStepKernel Phase2.env₄ alg Phase2.env₄.hr_meas).comap (fun x : (Unit × Unit) × ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) => x.2.2) (by measurability) (σs, c) (Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' ∧ p.2.1 = a }) =
        if c.1 ∈ S' then (1/2 : ℝ≥0∞) else 0 := by
        intro c
        by_cases hc : c.1 ∈ S'
        · rw [if_pos hc]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' ∧ p.2.1 = a } = { step : Fin 2 × Unit × ℝ × Unit × Unit | step.1 = a } := by ext step; simp [hc]
          rw [h_prod]
          rw [oneStepKernel_peel_action_gen Phase2.env₄ alg Phase2.env₄.hr_meas hEnv hAlg c.2 a]
          exact pol_eps_apply a
        · rw [if_neg hc]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' ∧ p.2.1 = a } = ∅ := by ext step; simp [hc]
          rw [h_prod, measure_empty]
      have h_inner_int2 : ∀ c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)),
        (Phase2.oneStepKernel Phase2.env₄ alg Phase2.env₄.hr_meas).comap (fun x : (Unit × Unit) × ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) => x.2.2) (by measurability) (σs, c) (Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' }) =
        if c.1 ∈ S' then (1 : ℝ≥0∞) else 0 := by
        intro c
        by_cases hc : c.1 ∈ S'
        · rw [if_pos hc]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' } = Set.univ := by ext step; simp [hc]
          rw [h_prod, measure_univ]
        · rw [if_neg hc]
          simp only [Kernel.comap_apply]
          have h_prod : Prod.mk c ⁻¹' { p : (((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) × Fin 2 × Unit × ℝ × Unit × Unit) | p.1.1 ∈ S' } = ∅ := by ext step; simp [hc]
          rw [h_prod, measure_empty]
      rw [lintegral_congr h_inner_int, lintegral_congr h_inner_int2]
      have h_ind1 : (fun c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) => if c.1 ∈ S' then (1/2 : ℝ≥0∞) else 0) =
                    { c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) | c.1 ∈ S' }.indicator (fun _ => (1/2 : ℝ≥0∞)) := by ext c; by_cases hc : c.1 ∈ S' <;> simp [hc]
      have h_ind2 : (fun c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) => if c.1 ∈ S' then (1 : ℝ≥0∞) else 0) =
                    { c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) | c.1 ∈ S' }.indicator (fun _ => 1) := by ext c; by_cases hc : c.1 ∈ S' <;> simp [hc]
      have h_meas_c : MeasurableSet { c : ((Fin t → Fin 2 × Unit × ℝ) × (Unit × Unit)) | c.1 ∈ S' } := measurable_fst hS'
      rw [h_ind1, h_ind2]
      rw [lintegral_indicator_const h_meas_c, lintegral_indicator_const h_meas_c]
      simp
    have h_toReal : (μ (X_lt ⁻¹' S' ∩ A_t ⁻¹' {a})).toReal = ((1 / 2 : ℝ≥0∞) * μ (X_lt ⁻¹' S')).toReal := by rw [h_measure_eq]
    have h_half_real : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      norm_num
    rw [ENNReal.toReal_mul, h_half_real] at h_toReal
    rw [h_toReal]
    ring
  · apply StronglyMeasurable.aestronglyMeasurable
    exact stronglyMeasurable_const

lemma env4_condEntSeqX4_eq_log2 (t : ℕ) :
    condEntSeqX4 (canonical_challenger (Fin 2) Unit pol_eps) t = Real.log 2 := by
  unfold condEntSeqX4 Phase1.condEntropyOf
  let alg := canonical_challenger (Fin 2) Unit pol_eps
  let μ := Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1)
  let X_lt := traj_prefix (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t)
  let A_t := Phase2.traj_action (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t)
  have h_cond : ∀ a : Fin 2, μ[(A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_lt inferInstance] =ᵐ[μ] fun _ => (1/2 : ℝ) := env4_action_condExp_eq_half t
  have h_sum : ∀ᵐ ω ∂μ, ∑ a : Fin 2, -(μ[(A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_lt inferInstance] ω * Real.log (μ[(A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_lt inferInstance] ω)) = Real.log 2 := by
    have h_all : ∀ᵐ ω ∂μ, ∀ a : Fin 2, μ[(A_t ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_lt inferInstance] ω = 1/2 := by
      rw [Filter.eventually_all]
      exact h_cond
    filter_upwards [h_all] with ω hω
    rw [Fin.sum_univ_two]
    have h0 : (0 : Fin 2) ∈ Finset.univ := Finset.mem_univ 0
    have h1 : (1 : Fin 2) ∈ Finset.univ := Finset.mem_univ 1
    rw [hω 0, hω 1]
    have h_log : Real.log (1 / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [h_log]
    ring
  rw [integral_congr_ae h_sum]
  rw [integral_const]
  have hEnv : Phase2.EnvIsMarkov Phase2.env₄ := Phase2.envIsDeterministic_isMarkov Phase2.env₄ Phase2.env₄_isDet
  have hAlg : Phase2.AlgIsMarkov alg := canonical_challenger_isMarkov _ _ pol_eps
  haveI h_prob : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability Phase2.env₄ alg Phase2.env₄.hr_meas hEnv hAlg (t + 1)
  have h_univ : μ Set.univ = 1 := h_prob.measure_univ
  simp

lemma canonical_challenger_lacks_x4 :
    LacksX₄ (condEntSeqX4 (canonical_challenger (Fin 2) Unit pol_eps)) := by
  unfold LacksX₄
  use Real.log 2
  constructor
  · exact Real.log_pos (by norm_num)
  · have h_eq : (fun t => condEntSeqX4 (canonical_challenger (Fin 2) Unit pol_eps) t) = fun _ => Real.log 2 := by
      ext t
      exact env4_condEntSeqX4_eq_log2 t
    rw [h_eq]
    simp [Filter.liminf_const]

lemma alg1_lacks_x4 : LacksX₄ (condEntSeqX4 (alg1_bayes (Fin 2) Unit pol_eps)) :=
  canonical_challenger_lacks_x4

lemma alg2_lacks_x4 : LacksX₄ (condEntSeqX4 (alg2_safe (Fin 2) Unit pol_eps)) :=
  canonical_challenger_lacks_x4

lemma alg3_lacks_x4 : LacksX₄ (condEntSeqX4 (alg3_bridge (Fin 2) Unit pol_eps)) :=
  canonical_challenger_lacks_x4

lemma alg5_lacks_x4 : LacksX₄ (condEntSeqX4 (alg5_feas (Fin 2) Unit pol_eps)) :=
  canonical_challenger_lacks_x4

lemma alg6_lacks_x4 : LacksX₄ (condEntSeqX4 (alg6_shortMem (Fin 2) Unit pol_eps)) :=
  canonical_challenger_lacks_x4

-- 5. Home Turf: env5 (Lacks X₅)

noncomputable instance alg1_bayes_polR_isDet : Phase2.AlgIsDeterministic (alg1_bayes ℝ Unit polR) where
  actFn := fun _ => 1/2
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg1_lacks_x5 : LacksX₅ (Phase2.infeasProbSeq env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas infeasSet₅) := by
  unfold LacksX₅
  refine ⟨1, zero_lt_one, ?_⟩
  have h_prob : ∀ t : ℕ, Phase2.infeasProbSeq env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas infeasSet₅ t = 1 := by
    intro t
    unfold Phase2.infeasProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas t (t + 1) (Nat.lt_succ_self t) (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet)
    have h_ae_in : ∀ᵐ ω ∂(Phase2.trajMeasure env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas (t + 1)), ω ∈ {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} := by
      filter_upwards [h_ae] with ω hω
      change (ω ⟨t, Nat.lt_succ_self t⟩).1 = 1/2 at hω
      rw [hω]
      change (1/2 : ℝ) ∉ feasSet₅
      simp [feasSet₅, Set.mem_union, Set.mem_Icc]
      norm_num
    haveI h_isProb := Phase2.trajMeasure_isProbability env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet) (alg1_isMarkov ℝ Unit polR) (t + 1)
    have h_meas_one : (Phase2.trajMeasure env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas (t + 1)) {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} = 1 := by
      have h_compl : (Phase2.trajMeasure env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_in
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory ℝ Unit (t + 1) | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) measurableSet_infeasSet₅
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas (t + 1))
      rw [h_compl, add_zero, h_isProb.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  have h_seq : (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = fun T => if T = 0 then 0 else 1 := by
    ext T
    by_cases hT : T = 0
    · simp [hT]
    · rw [if_neg hT]
      have h_sum : (∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg1_bayes ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = T := by
        have h_ones : (∑ t ∈ Finset.range T, (1 : ℝ)) = T := by simp
        rw [← h_ones]
        apply Finset.sum_congr rfl
        intro x _
        rw [h_prob x]
      rw [h_sum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT)
  rw [h_seq]
  have h_tendsto : Tendsto (fun T : ℕ => if T = 0 then (0 : ℝ) else 1) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [if_neg hn]
  exact h_tendsto.liminf_eq.symm.le

noncomputable instance alg2_safe_polR_isDet : Phase2.AlgIsDeterministic (alg2_safe ℝ Unit polR) where
  actFn := fun _ => 1/2
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg2_lacks_x5 : LacksX₅ (Phase2.infeasProbSeq env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas infeasSet₅) := by
  unfold LacksX₅
  refine ⟨1, zero_lt_one, ?_⟩
  have h_prob : ∀ t : ℕ, Phase2.infeasProbSeq env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas infeasSet₅ t = 1 := by
    intro t
    unfold Phase2.infeasProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas t (t + 1) (Nat.lt_succ_self t) (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet)
    have h_ae_in : ∀ᵐ ω ∂(Phase2.trajMeasure env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas (t + 1)), ω ∈ {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} := by
      filter_upwards [h_ae] with ω hω
      change (ω ⟨t, Nat.lt_succ_self t⟩).1 = 1/2 at hω
      rw [hω]
      change (1/2 : ℝ) ∉ feasSet₅
      simp [feasSet₅, Set.mem_union, Set.mem_Icc]
      norm_num
    haveI h_isProb := Phase2.trajMeasure_isProbability env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet) (alg2_isMarkov ℝ Unit polR) (t + 1)
    have h_meas_one : (Phase2.trajMeasure env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas (t + 1)) {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} = 1 := by
      have h_compl : (Phase2.trajMeasure env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_in
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory ℝ Unit (t + 1) | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) measurableSet_infeasSet₅
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas (t + 1))
      rw [h_compl, add_zero, h_isProb.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  have h_seq : (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = fun T => if T = 0 then 0 else 1 := by
    ext T
    by_cases hT : T = 0
    · simp [hT]
    · rw [if_neg hT]
      have h_sum : (∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg2_safe ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = T := by
        have h_ones : (∑ t ∈ Finset.range T, (1 : ℝ)) = T := by simp
        rw [← h_ones]
        apply Finset.sum_congr rfl
        intro x _
        rw [h_prob x]
      rw [h_sum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT)
  rw [h_seq]
  have h_tendsto : Tendsto (fun T : ℕ => if T = 0 then (0 : ℝ) else 1) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [if_neg hn]
  exact h_tendsto.liminf_eq.symm.le

noncomputable instance alg3_bridge_polR_isDet : Phase2.AlgIsDeterministic (alg3_bridge ℝ Unit polR) where
  actFn := fun _ => 1/2
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg3_lacks_x5 : LacksX₅ (Phase2.infeasProbSeq env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas infeasSet₅) := by
  unfold LacksX₅
  refine ⟨1, zero_lt_one, ?_⟩
  have h_prob : ∀ t : ℕ, Phase2.infeasProbSeq env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas infeasSet₅ t = 1 := by
    intro t
    unfold Phase2.infeasProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas t (t + 1) (Nat.lt_succ_self t) (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet)
    have h_ae_in : ∀ᵐ ω ∂(Phase2.trajMeasure env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas (t + 1)), ω ∈ {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} := by
      filter_upwards [h_ae] with ω hω
      change (ω ⟨t, Nat.lt_succ_self t⟩).1 = 1/2 at hω
      rw [hω]
      change (1/2 : ℝ) ∉ feasSet₅
      simp [feasSet₅, Set.mem_union, Set.mem_Icc]
      norm_num
    haveI h_isProb := Phase2.trajMeasure_isProbability env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet) (alg3_isMarkov ℝ Unit polR) (t + 1)
    have h_meas_one : (Phase2.trajMeasure env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas (t + 1)) {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} = 1 := by
      have h_compl : (Phase2.trajMeasure env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_in
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory ℝ Unit (t + 1) | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) measurableSet_infeasSet₅
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas (t + 1))
      rw [h_compl, add_zero, h_isProb.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  have h_seq : (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = fun T => if T = 0 then 0 else 1 := by
    ext T
    by_cases hT : T = 0
    · simp [hT]
    · rw [if_neg hT]
      have h_sum : (∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg3_bridge ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = T := by
        have h_ones : (∑ t ∈ Finset.range T, (1 : ℝ)) = T := by simp
        rw [← h_ones]
        apply Finset.sum_congr rfl
        intro x _
        rw [h_prob x]
      rw [h_sum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT)
  rw [h_seq]
  have h_tendsto : Tendsto (fun T : ℕ => if T = 0 then (0 : ℝ) else 1) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [if_neg hn]
  exact h_tendsto.liminf_eq.symm.le

noncomputable instance alg4_ucb_polR_isDet : Phase2.AlgIsDeterministic (alg4_ucb ℝ Unit polR) where
  actFn := fun _ => 1/2
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg4_lacks_x5 : LacksX₅ (Phase2.infeasProbSeq env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas infeasSet₅) := by
  unfold LacksX₅
  refine ⟨1, zero_lt_one, ?_⟩
  have h_prob : ∀ t : ℕ, Phase2.infeasProbSeq env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas infeasSet₅ t = 1 := by
    intro t
    unfold Phase2.infeasProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas t (t + 1) (Nat.lt_succ_self t) (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet)
    have h_ae_in : ∀ᵐ ω ∂(Phase2.trajMeasure env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas (t + 1)), ω ∈ {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} := by
      filter_upwards [h_ae] with ω hω
      change (ω ⟨t, Nat.lt_succ_self t⟩).1 = 1/2 at hω
      rw [hω]
      change (1/2 : ℝ) ∉ feasSet₅
      simp [feasSet₅, Set.mem_union, Set.mem_Icc]
      norm_num
    haveI h_isProb := Phase2.trajMeasure_isProbability env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet) (alg4_isMarkov ℝ Unit polR) (t + 1)
    have h_meas_one : (Phase2.trajMeasure env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas (t + 1)) {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} = 1 := by
      have h_compl : (Phase2.trajMeasure env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_in
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory ℝ Unit (t + 1) | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) measurableSet_infeasSet₅
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas (t + 1))
      rw [h_compl, add_zero, h_isProb.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  have h_seq : (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = fun T => if T = 0 then 0 else 1 := by
    ext T
    by_cases hT : T = 0
    · simp [hT]
    · rw [if_neg hT]
      have h_sum : (∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg4_ucb ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = T := by
        have h_ones : (∑ t ∈ Finset.range T, (1 : ℝ)) = T := by simp
        rw [← h_ones]
        apply Finset.sum_congr rfl
        intro x _
        rw [h_prob x]
      rw [h_sum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT)
  rw [h_seq]
  have h_tendsto : Tendsto (fun T : ℕ => if T = 0 then (0 : ℝ) else 1) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [if_neg hn]
  exact h_tendsto.liminf_eq.symm.le

noncomputable instance alg6_shortMem_polR_isDet : Phase2.AlgIsDeterministic (alg6_shortMem ℝ Unit polR) where
  actFn := fun _ => 1/2
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma alg6_lacks_x5 : LacksX₅ (Phase2.infeasProbSeq env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas infeasSet₅) := by
  unfold LacksX₅
  refine ⟨1, zero_lt_one, ?_⟩
  have h_prob : ∀ t : ℕ, Phase2.infeasProbSeq env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas infeasSet₅ t = 1 := by
    intro t
    unfold Phase2.infeasProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas t (t + 1) (Nat.lt_succ_self t) (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet)
    have h_ae_in : ∀ᵐ ω ∂(Phase2.trajMeasure env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas (t + 1)), ω ∈ {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} := by
      filter_upwards [h_ae] with ω hω
      change (ω ⟨t, Nat.lt_succ_self t⟩).1 = 1/2 at hω
      rw [hω]
      change (1/2 : ℝ) ∉ feasSet₅
      simp [feasSet₅, Set.mem_union, Set.mem_Icc]
      norm_num
    haveI h_isProb := Phase2.trajMeasure_isProbability env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas (Phase2.envIsDeterministic_isMarkov env₅ env₅_isDet) (alg6_isMarkov ℝ Unit polR) (t + 1)
    have h_meas_one : (Phase2.trajMeasure env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas (t + 1)) {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} = 1 := by
      have h_compl : (Phase2.trajMeasure env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_ae_in
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory ℝ Unit (t + 1) | (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ infeasSet₅} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) measurableSet_infeasSet₅
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas (t + 1))
      rw [h_compl, add_zero, h_isProb.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  have h_seq : (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = fun T => if T = 0 then 0 else 1 := by
    ext T
    by_cases hT : T = 0
    · simp [hT]
    · rw [if_neg hT]
      have h_sum : (∑ t ∈ Finset.range T, Phase2.infeasProbSeq env₅ (alg6_shortMem ℝ Unit polR) env₅.hr_meas infeasSet₅ t) = T := by
        have h_ones : (∑ t ∈ Finset.range T, (1 : ℝ)) = T := by simp
        rw [← h_ones]
        apply Finset.sum_congr rfl
        intro x _
        rw [h_prob x]
      rw [h_sum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT)
  rw [h_seq]
  have h_tendsto : Tendsto (fun T : ℕ => if T = 0 then (0 : ℝ) else 1) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [if_neg hn]
  exact h_tendsto.liminf_eq.symm.le

-- 6. Home Turf: env6_nonstat (Lacks X₆)

noncomputable instance alg1_bayes_pol0_bool_isDet : Phase2.AlgIsDeterministic (alg1_bayes (Fin 2) Bool pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma deterministic_zero_lacks_x6
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Unit)
    [hDet : Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (hAct0 : hDet.actFn = fun _ => 0) :
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  unfold LacksX₆
  use 1/2, 1/4
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  intro t _ht_gt _ht_le
  have h_seq : Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0 t = 1 := by
    unfold Phase2.staleProbSeq
    have h_ae := Phase2.traj_action_ae_eq_actFn (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas t (t + 1) (Nat.lt_succ_self t) (env₆_nonstat_isMarkov T₀ Δ hΔ0 hΔ4)
    have h_eq : ∀ᵐ ω ∂(Phase2.trajMeasure (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas (t + 1)),
        (ω ⟨t, Nat.lt_succ_self t⟩).1 = 0 := by
      filter_upwards [h_ae] with ω hω
      dsimp [Phase2.traj_action] at hω
      rw [hω, hAct0]
    haveI h_prob := Phase2.trajMeasure_isProbability (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas (env₆_nonstat_isMarkov T₀ Δ hΔ0 hΔ4) hAlg (t + 1)
    have h_meas_one : (Phase2.trajMeasure (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas (t + 1)) {traj |
(traj ⟨t, Nat.lt_succ_self t⟩).1 = 0} = 1 := by
      have h_compl : (Phase2.trajMeasure (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas (t + 1)) ({traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 = 0}ᶜ) = 0 := MeasureTheory.ae_iff.mp h_eq
      have h_meas_set : MeasurableSet {traj : Phase2.Trajectory (Fin 2) Bool (t + 1) |
(traj ⟨t, Nat.lt_succ_self t⟩).1 = 0} :=
        (Phase2.measurable_traj_action t (Nat.lt_succ_self t)) (measurableSet_singleton 0)
      have h_univ := measure_add_measure_compl h_meas_set (μ := Phase2.trajMeasure (env₆_nonstat T₀ Δ hΔ0 hΔ4) alg (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas (t + 1))
      rw [h_compl, add_zero, h_prob.measure_univ] at h_univ
      exact h_univ
    rw [h_meas_one]
    exact ENNReal.toReal_one
  rw [h_seq]
  norm_num

lemma alg1_lacks_x6 : LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg1_bayes (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  apply deterministic_zero_lacks_x6
  · exact alg1_isMarkov (Fin 2) Bool pol0
  · rfl

lemma alg2_lacks_x6 : LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg2_safe (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  apply deterministic_zero_lacks_x6
  · exact alg2_isMarkov (Fin 2) Bool pol0
  · rfl

lemma alg3_lacks_x6 : LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg3_bridge (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  apply deterministic_zero_lacks_x6
  · exact alg3_isMarkov (Fin 2) Bool pol0
  · rfl

lemma alg4_lacks_x6 : LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg4_ucb (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  apply deterministic_zero_lacks_x6
  · exact alg4_isMarkov (Fin 2) Bool pol0
  · rfl

lemma alg5_lacks_x6 : LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg5_feas (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  apply deterministic_zero_lacks_x6
  · exact alg5_isMarkov (Fin 2) Bool pol0
  · rfl

end IndependenceMatchups

-- PART C: MASTER THEOREM

theorem mutual_independence
    (bp : Phase2.BanditParam)
    (K : ℕ) (hK : 0 < K)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T₀ : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :

    -- X1 lacked by Algs 2, 3, 4, 5, 6
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg2_safe (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg2_isMarkov (Fin 2) Bool pol0)) ∧
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg3_bridge (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg3_isMarkov (Fin 2) Bool pol0)) ∧
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg4_ucb (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg4_isMarkov (Fin 2) Bool pol0)) ∧
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg5_feas (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg5_isMarkov (Fin 2) Bool pol0)) ∧
    LacksX₁ (Phase3.miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) (alg6_shortMem (Fin 2) Bool pol0) (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) (alg6_isMarkov (Fin 2) Bool pol0)) ∧

    -- X2 lacked by Algs 1, 3, 4, 5, 6
    LacksX₂ (Phase2.condDangerProbSeq K hK (alg1_bayes (Fin 2) (Fin (K+2)) pol_eps) (alg1_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) ∧
    LacksX₂ (Phase2.condDangerProbSeq K hK (alg3_bridge (Fin 2) (Fin (K+2)) pol_eps) (alg3_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) ∧
    LacksX₂ (Phase2.condDangerProbSeq K hK (alg4_ucb (Fin 2) (Fin (K+2)) pol_eps) (alg4_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) ∧
    LacksX₂ (Phase2.condDangerProbSeq K hK (alg5_feas (Fin 2) (Fin (K+2)) pol_eps) (alg5_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) ∧
    LacksX₂ (Phase2.condDangerProbSeq K hK (alg6_shortMem (Fin 2) (Fin (K+2)) pol_eps) (alg6_isMarkov (Fin 2) (Fin (K+2)) pol_eps) (env₂_dangerAction K)) ∧

    -- X3 lacked by Algs 1, 2, 4, 5, 6
    LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg1_bayes (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) ∧
    LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg2_safe (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) ∧
    LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg4_ucb (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) ∧
    LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg5_feas (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) ∧
    LacksX₃ (Phase2.bridgeCumSeq (Phase2.env₃ p hp0 hp1) (alg6_shortMem (Fin 2) Unit pol0) (Phase2.env₃ p hp0 hp1).hr_meas 1) ∧

    -- X4 lacked by Algs 1, 2, 3, 5, 6
    LacksX₄ (condEntSeqX4 (alg1_bayes (Fin 2) Unit pol_eps)) ∧
    LacksX₄ (condEntSeqX4 (alg2_safe (Fin 2) Unit pol_eps)) ∧
    LacksX₄ (condEntSeqX4 (alg3_bridge (Fin 2) Unit pol_eps)) ∧
    LacksX₄ (condEntSeqX4 (alg5_feas (Fin 2) Unit pol_eps)) ∧
    LacksX₄ (condEntSeqX4 (alg6_shortMem (Fin 2) Unit pol_eps)) ∧

    -- X5 lacked by Algs 1, 2, 3, 4, 6
    LacksX₅ (Phase2.infeasProbSeq Phase2.env₅ (alg1_bayes ℝ Unit polR) Phase2.env₅.hr_meas infeasSet₅) ∧
    LacksX₅ (Phase2.infeasProbSeq Phase2.env₅ (alg2_safe ℝ Unit polR) Phase2.env₅.hr_meas infeasSet₅) ∧
    LacksX₅ (Phase2.infeasProbSeq Phase2.env₅ (alg3_bridge ℝ Unit polR) Phase2.env₅.hr_meas infeasSet₅) ∧
    LacksX₅ (Phase2.infeasProbSeq Phase2.env₅ (alg4_ucb ℝ Unit polR) Phase2.env₅.hr_meas infeasSet₅) ∧
    LacksX₅ (Phase2.infeasProbSeq Phase2.env₅ (alg6_shortMem ℝ Unit polR) Phase2.env₅.hr_meas infeasSet₅) ∧

    -- X6 lacked by Algs 1, 2, 3, 4, 5
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg1_bayes (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 ∧
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg2_safe (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 ∧
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg3_bridge (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 ∧
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg4_ucb (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 ∧
    LacksX₆ (Phase2.staleProbSeq (env₆_nonstat T₀ Δ hΔ0 hΔ4) (alg5_feas (Fin 2) Bool pol0) (env₆_nonstat T₀ Δ hΔ0 hΔ4).hr_meas 0) 2 := by
  refine ⟨alg2_lacks_x1 bp, alg3_lacks_x1 bp, alg4_lacks_x1 bp, alg5_lacks_x1 bp, alg6_lacks_x1 bp,
          alg1_lacks_x2 K hK, alg3_lacks_x2 K hK, alg4_lacks_x2 K hK, alg5_lacks_x2 K hK, alg6_lacks_x2 K hK,
          alg1_lacks_x3 p hp0 hp1, alg2_lacks_x3 p hp0 hp1, alg4_lacks_x3 p hp0 hp1, alg5_lacks_x3 p hp0 hp1, alg6_lacks_x3 p hp0 hp1,
          alg1_lacks_x4, alg2_lacks_x4, alg3_lacks_x4, alg5_lacks_x4, alg6_lacks_x4,
          alg1_lacks_x5, alg2_lacks_x5, alg3_lacks_x5, alg4_lacks_x5, alg6_lacks_x5,
          alg1_lacks_x6 T₀ Δ hΔ0 hΔ4, alg2_lacks_x6 T₀ Δ hΔ0 hΔ4, alg3_lacks_x6 T₀ Δ hΔ0 hΔ4, alg4_lacks_x6 T₀ Δ hΔ0 hΔ4, alg5_lacks_x6 T₀ Δ hΔ0 hΔ4⟩

end SixPrimitives.Phase4
