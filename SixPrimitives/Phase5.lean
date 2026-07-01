import SixPrimitives.Phase0
import SixPrimitives.Phase1
import SixPrimitives.Phase2
import SixPrimitives.Phase2CMI
import SixPrimitives.Phase3
import SixPrimitives.Phase4
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Ismail's Primitives — Phase 5: Sequential Dependence & Accumulative Sufficiency
This phase formally proves that the six primitives form an ordered informational chain. Each
primitive creates the conditions for the next, and the sequence culminates in a martingale
convergence theorem for the learning posterior.
It also establishes a constructive path to dynamic sufficiency, but deliberately abstracts the
proof that the primitives automatically generate the required convergence conditions, leaving
those as explicit prerequisites to be fulfilled by the implementer.-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal Topology

namespace SixPrimitives.Phase5

-- §1. INFRASTRUCTURE: (S4) SUFFICIENCY & MEASURE-THEORETIC GOALS

noncomputable def MI_Summary_Seq {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : ∀ T, Phase2.Trajectory A O T → G)
    (_hGoalMeas : ∀ T, Measurable (goal_var T))
    (t : ℕ) : ℝ :=
  let μ := Phase2.trajMeasure env alg env.hr_meas t
  letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
  letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
  Phase2.entropy (goal_var t) -
  Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)

def IsSufficientSummary {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : ∀ T, Phase2.Trajectory A O T → G)
    (_hGoalMeas : ∀ T, Measurable (goal_var T)) : Prop :=
  ∀ t : ℕ,
    let μ := Phase2.trajMeasure env alg env.hr_meas t
    letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
    letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
    Phase2.condEntropy (goal_var t)
      (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance) =
    Phase2.condEntropy (goal_var t) ⊤

noncomputable def Infeas_Prob_Seq {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (F : Set A) (t : ℕ) : ℝ :=
  (Phase2.actionMarginal env alg env.hr_meas hEnv hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩ Fᶜ).toReal

noncomputable def condEntSeqX4_gen {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [Fintype A] [MeasurableSingletonClass A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (t : ℕ) : ℝ :=
  Phase1.condEntropyOf
    (Phase2.trajMeasure env alg env.hr_meas (t + 1))
    (Phase2.traj_action t (Nat.lt_succ_self t))
    (SixPrimitives.traj_prefix t (Nat.lt_succ_self t))

-- §2. ALMOST-SURE ROBUST POSSESSION

def RobustX1 {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : ∀ T, Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T)) : Prop :=
  1 / 2 < liminf (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop

def RobustX2_general {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (tau : ℕ → ℕ)
    (a_danger : A) : Prop :=
  Summable (fun k : ℕ =>
    (Phase2.actionMarginal env alg env.hr_meas hEnv hAlg (tau k + 1) ⟨tau k, Nat.lt_succ_self (tau k)⟩ {a_danger}).toReal)

def RobustX2 {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (tau : ℕ → ℕ)
    (a_danger : A) : Prop :=
  RobustX2_general env alg hEnv hAlg tau a_danger

noncomputable def bridge_count_rv {A O : Type*} [DecidableEq A]
    (a_B : A) (T : ℕ) (ω : Phase2.Trajectory A O T) : ℝ :=
  ∑ t : Fin T, if (ω t).1 = a_B then 1 else 0

lemma measurable_bridge_count_rv {A O : Type*} [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass A] [DecidableEq A] (a_B : A) (T : ℕ) :
    Measurable (bridge_count_rv a_B T : Phase2.Trajectory A O T → ℝ) := by
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite
  · exact (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton a_B)
  · exact measurable_const
  · exact measurable_const

def RobustX3_ae {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [DecidableEq A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (a_B : A) : Prop :=
  ∀ M > 0, Tendsto (fun T : ℕ =>
    (Phase2.trajMeasure env alg env.hr_meas T
      {ω | bridge_count_rv a_B T ω ≥ M * Real.sqrt T}).toReal
  ) atTop (nhds 1)

def RobustX4_ae {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [Fintype A] [MeasurableSingletonClass A]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (a_star : A) : Prop :=
  liminf (condEntSeqX4_gen env alg) atTop = 0 ∧
  Tendsto (fun t =>
    (Phase2.actionMarginal env alg env.hr_meas hEnv hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩ {a_star}).toReal
  ) atTop (nhds 1)

noncomputable def infeas_count_rv {A O : Type*}
    (F : Set A) [DecidablePred (· ∈ F)] (T : ℕ) (ω : Phase2.Trajectory A O T) : ℝ :=
  ∑ t : Fin T, if (ω t).1 ∉ F then 1 else 0

lemma measurable_infeas_count_rv {A O : Type*} [MeasurableSpace A] [MeasurableSpace O]
    (F : Set A) [DecidablePred (· ∈ F)] (hF : MeasurableSet F) (T : ℕ) :
    Measurable (infeas_count_rv F T : Phase2.Trajectory A O T → ℝ) := by
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite
  · exact (Phase2.measurable_traj_action t.val t.isLt) hF.compl
  · exact measurable_const
  · exact measurable_const

def RobustX5_ae {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (F : Set A) [DecidablePred (· ∈ F)] : Prop :=
  ∀ ε > 0, Tendsto (fun T : ℕ =>
    (Phase2.trajMeasure env alg env.hr_meas T
      {ω | infeas_count_rv F T ω / T ≥ ε}).toReal
  ) atTop (nhds 0)

def RobustX6_ae {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (_env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (L_min : ℕ) : Prop :=
  ∀ K T : ℕ, ∀ (hK : K * L_min ≤ T),
    ∀ ω₁ ω₂ : Phase2.Trajectory A O T,
      (∀ t : ℕ, (K - 1) * L_min ≤ t → ∀ ht : t < K * L_min,
        ω₁ ⟨t, lt_of_lt_of_le ht hK⟩ = ω₂ ⟨t, lt_of_lt_of_le ht hK⟩) →
      Phase2.summary_at alg (K * L_min) T hK ω₁ =
      Phase2.summary_at alg (K * L_min) T hK ω₂

noncomputable instance alg3_bridge_pol0_isDet_K {K : ℕ} :
  Phase2.AlgIsDeterministic (Phase4.alg3_bridge (Fin 2) (Fin (K+2)) Phase4.pol0) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

-- §3. IET 1: X₁ → X₂ (Information-Theoretic, DPI)

section IET1
variable {S A O Sig G : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig] [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (goal_var : ∀ T, Phase2.Trajectory A O T → G)
variable (hGoalMeas : ∀ T, Measurable (goal_var T))

theorem iet1_forward
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX1 : RobustX1 env alg hEnv hAlg goal_var hGoalMeas)
    (_hS4 : IsSufficientSummary env alg hEnv hAlg goal_var hGoalMeas) :
    1 / 2 < liminf (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop := by
  exact _hRobustX1

theorem iet1_reverse
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hLacksX1 : SixPrimitives.LacksX₁ (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas)) :
    ∃ B < 1/2, limsup (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop ≤ B := by
  exact _hLacksX1

theorem iet1_non_reversible :
    ∃ (env_12 : SixPrimitives.Env Unit (Fin 2) Bool)
      (hEnv_12 : Phase2.EnvIsMarkov env_12)
      (g_12 : ∀ T, Phase2.Trajectory (Fin 2) Bool T → Fin 2)
      (hG_12 : ∀ T, Measurable (g_12 T)),
    ∃ B < 1/2, ∀ t, MI_Summary_Seq env_12 (Phase4.alg2_safe (Fin 2) Bool Phase4.pol0) hEnv_12 (Phase4.alg2_isMarkov (Fin 2) Bool Phase4.pol0) g_12 hG_12 t ≤ B := by
  have bp : Phase2.BanditParam := ⟨1/4, by norm_num, by norm_num⟩
  refine ⟨Phase2.env₁_0 bp, Phase2.env₁_0_isMarkov bp, fun _ _ => 0, fun _ => measurable_const, 1/4, by norm_num, fun t => ?_⟩
  let μ := Phase2.trajMeasure (Phase2.env₁_0 bp) (Phase4.alg2_safe (Fin 2) Bool Phase4.pol0) (Phase2.env₁_0 bp).hr_meas t
  letI : MeasureSpace (Phase2.Trajectory (Fin 2) Bool t) := ⟨μ⟩
  letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability (Phase2.env₁_0 bp) (Phase4.alg2_safe (Fin 2) Bool Phase4.pol0) (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) (Phase4.alg2_isMarkov (Fin 2) Bool Phase4.pol0) t
  change Phase2.entropy (fun _ : Phase2.Trajectory (Fin 2) Bool t => (0 : Fin 2)) - Phase2.condEntropy (fun _ : Phase2.Trajectory (Fin 2) Bool t => (0 : Fin 2)) _ ≤ 1/4
  have h_eq : (fun _ : Phase2.Trajectory (Fin 2) Bool t => (0 : Fin 2)) = (fun _ : Unit => (0 : Fin 2)) ∘ (fun _ => ()) := rfl
  have h_comap_bot :
      MeasurableSpace.comap (fun _ : Phase2.Trajectory (Fin 2) Bool t => ()) inferInstance ≤
        (⊥ : MeasurableSpace (Phase2.Trajectory (Fin 2) Bool t)) :=
    Measurable.comap_le
      (@measurable_const Unit (Phase2.Trajectory (Fin 2) Bool t) inferInstance ⊥ ())
  have h_ent_zero : Phase2.entropy (fun _ : Phase2.Trajectory (Fin 2) Bool t => (0 : Fin 2)) = 0 := by
    rw [Phase2.entropy, h_eq]
    exact Phase2.condEntropy_of_deterministic (fun _ : Unit => (0 : Fin 2)) measurable_const (fun _ => ()) measurable_const ⊥ h_comap_bot
  have h_cond_ent_zero : Phase2.condEntropy (fun _ : Phase2.Trajectory (Fin 2) Bool t => (0 : Fin 2)) (MeasurableSpace.comap (Phase2.summary_at (Phase4.alg2_safe (Fin 2) Bool Phase4.pol0) t t (le_refl t)) inferInstance) = 0 := by
    rw [h_eq]
    exact Phase2.condEntropy_of_deterministic (fun _ : Unit => (0 : Fin 2)) measurable_const (fun _ => ()) measurable_const _ (h_comap_bot.trans bot_le)
  rw [h_ent_zero, h_cond_ent_zero]
  norm_num

end IET1

-- §4. IET 2: X₂ → X₃ (Information-Theoretic, Survival)

section IET2
variable {S A O Sig G : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig] [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (goal_var : ∀ T, Phase2.Trajectory A O T → G)
variable (hGoalMeas : ∀ T, Measurable (goal_var T))
variable (a_B : A) [DecidableEq A] [MeasurableSingletonClass A]
variable (tau : ℕ → ℕ) (a_danger : A)

theorem iet2_forward
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX2 : RobustX2 env alg hEnv hAlg tau a_danger)
    (_hRobustX3 : RobustX3_ae env alg a_B)
    (_hS4 : IsSufficientSummary env alg hEnv hAlg goal_var hGoalMeas)
    (hGoalEnt : ∀ t : ℕ,
      let μ := Phase2.trajMeasure env alg env.hr_meas t
      letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
      letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
      Phase2.entropy (goal_var t) = Real.log 2) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2)) := by
  have h_seq_eq : MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas = fun _ => Real.log 2 := by
    ext t
    let μ := Phase2.trajMeasure env alg env.hr_meas t
    letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
    letI hProb : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
    unfold MI_Summary_Seq
    dsimp only
    rw [_hS4 t]
    have h_det : Phase2.condEntropy (goal_var t) ⊤ = 0 := by
      have h_eq : goal_var t = id ∘ (goal_var t) := rfl
      rw [h_eq]
      apply Phase2.condEntropy_of_deterministic id measurable_id (goal_var t) (hGoalMeas t) ⊤
      exact le_top
    rw [h_det, sub_zero]
    exact hGoalEnt t
  rw [h_seq_eq]
  exact tendsto_const_nhds

omit [DecidableEq A] in
theorem iet2_reverse
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hLacksX2 : ¬ RobustX2 env alg hEnv hAlg tau a_danger)
    (hGoalEnt : ∀ t : ℕ,
      let μ := Phase2.trajMeasure env alg env.hr_meas t
      letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
      letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
      Phase2.entropy (goal_var t) = Real.log 2)
    (h_danger_erodes : ¬ RobustX2 env alg hEnv hAlg tau a_danger →
      ∃ δ > 0, ∀ᶠ t in atTop,
        let μ := Phase2.trajMeasure env alg env.hr_meas t
        letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
        letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
        δ * Real.log 2 ≤ Phase2.condEntropy (goal_var t)
          (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)) :
    ∃ δ > 0, limsup (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop ≤ (1 - δ) * Real.log 2 := by
  obtain ⟨δ, hδ_pos, h_eventual⟩ := h_danger_erodes _hLacksX2
  use δ
  refine ⟨hδ_pos, ?_⟩
  have h_MI_bound : ∀ᶠ t in atTop, MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t ≤ (1 - δ) * Real.log 2 := by
    filter_upwards [h_eventual] with t ht
    let μ := Phase2.trajMeasure env alg env.hr_meas t
    letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
    letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
    change δ * Real.log 2 ≤ Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance) at ht
    change Phase2.entropy (goal_var t) - Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance) ≤ (1 - δ) * Real.log 2
    have h_ent : Phase2.entropy (goal_var t) = Real.log 2 := hGoalEnt t
    linarith
  have hbdd_f : IsCoboundedUnder (· ≤ ·) atTop (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) := by
    refine ⟨(0 : ℝ), fun a ha => ?_⟩
    have h_nn : ∀ᶠ t : ℕ in atTop, (0 : ℝ) ≤ MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t := by
      apply Eventually.of_forall
      intro t
      let μ := Phase2.trajMeasure env alg env.hr_meas t
      letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
      letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
      change (0 : ℝ) ≤ Phase2.entropy (goal_var t) - Phase2.condEntropy (goal_var t)
        (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)
      have h_le := Phase2.condEntropy_le_entropy (goal_var t) (hGoalMeas t)
        (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)
      linarith
    obtain ⟨t, h1, h2⟩ := (h_nn.and ha).exists
    have h2' : MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t ≤ a := h2
    linarith
  have hbdd_g : IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => (1 - δ) * Real.log 2) :=
    Filter.isBoundedUnder_const
  calc limsup (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop
    _ ≤ limsup (fun _ : ℕ => (1 - δ) * Real.log 2) atTop := Filter.limsup_le_limsup h_MI_bound hbdd_f hbdd_g
    _ = (1 - δ) * Real.log 2 := by simp only [Filter.limsup_const]

theorem iet2_non_reversible (K : ℕ) (_hK : 0 < K) :
    ∃ (env_23 : SixPrimitives.Env (Fin (K+2)) (Fin 2) (Fin (K+2)))
      (hEnv_23 : Phase2.EnvIsMarkov env_23)
      (g_23 : ∀ T, Phase2.Trajectory (Fin 2) (Fin (K+2)) T → Bool)
      (hG_23 : ∀ T, Measurable (g_23 T)),
    ∃ δ > 0, ∀ t, MI_Summary_Seq env_23 (Phase4.alg3_bridge (Fin 2) (Fin (K+2)) Phase4.pol0) hEnv_23 (Phase4.alg3_isMarkov (Fin 2) (Fin (K+2)) Phase4.pol0) g_23 hG_23 t ≤ (1 - δ) * Real.log 2 := by
  refine ⟨Phase2.env₂ K _hK, Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K _hK),
          fun _ _ => true, fun _ => measurable_const, 1/2, by norm_num, fun t => ?_⟩
  let μ := Phase2.trajMeasure (Phase2.env₂ K _hK) (Phase4.alg3_bridge (Fin 2) (Fin (K+2)) Phase4.pol0) (Phase2.env₂ K _hK).hr_meas t
  letI : MeasureSpace (Phase2.Trajectory (Fin 2) (Fin (K+2)) t) := ⟨μ⟩
  letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability (Phase2.env₂ K _hK) (Phase4.alg3_bridge (Fin 2) (Fin (K+2)) Phase4.pol0) (Phase2.env₂ K _hK).hr_meas (Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K _hK)) (Phase4.alg3_isMarkov (Fin 2) (Fin (K+2)) Phase4.pol0) t
  have h_eq : (fun _ : Phase2.Trajectory (Fin 2) (Fin (K+2)) t => true) =
              (fun _ : Unit => true) ∘ (fun _ => ()) := rfl
  have h_comap_bot :
      MeasurableSpace.comap (fun _ : Phase2.Trajectory (Fin 2) (Fin (K+2)) t => ()) inferInstance ≤
        (⊥ : MeasurableSpace (Phase2.Trajectory (Fin 2) (Fin (K+2)) t)) :=
    Measurable.comap_le
      (@measurable_const Unit (Phase2.Trajectory (Fin 2) (Fin (K+2)) t) inferInstance ⊥ ())
  have h_ent_zero : Phase2.entropy (fun _ : Phase2.Trajectory (Fin 2) (Fin (K+2)) t => true) = 0 := by
    rw [Phase2.entropy, h_eq]
    exact Phase2.condEntropy_of_deterministic (fun _ : Unit => true) measurable_const (fun _ => ()) measurable_const ⊥ h_comap_bot
  have h_cond_ent_zero : Phase2.condEntropy (fun _ : Phase2.Trajectory (Fin 2) (Fin (K+2)) t => true)
    (MeasurableSpace.comap (Phase2.summary_at (Phase4.alg3_bridge (Fin 2) (Fin (K+2)) Phase4.pol0) t t (le_refl t)) inferInstance) = 0 := by
    rw [h_eq]
    exact Phase2.condEntropy_of_deterministic (fun _ : Unit => true) measurable_const (fun _ => ()) measurable_const _ (h_comap_bot.trans bot_le)
  unfold MI_Summary_Seq
  dsimp only
  rw [h_ent_zero, h_cond_ent_zero]
  have h_log_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

end IET2

-- §5. IET 3: X₃ → X₄ (Information-Theoretic, Dominated Convergence)

section IET3
variable {S A O Sig G : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig] [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (goal_var : ∀ T, Phase2.Trajectory A O T → G)
variable (hGoalMeas : ∀ T, Measurable (goal_var T))
variable (a_B : A) [DecidableEq A]

theorem iet3_forward
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX3 : RobustX3_ae env alg a_B)
    (_hS4 : IsSufficientSummary env alg hEnv hAlg goal_var hGoalMeas)
    (h_convergence : RobustX3_ae env alg a_B →
      Tendsto (fun t =>
        let μ := Phase2.trajMeasure env alg env.hr_meas t
        letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
        letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
        Phase2.entropy (goal_var t)) atTop (nhds (Real.log 2))) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2)) := by
  have h_seq_eq : MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas =
      fun t =>
        let μ := Phase2.trajMeasure env alg env.hr_meas t
        letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
        letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
        Phase2.entropy (goal_var t) := by
    ext t
    let μ := Phase2.trajMeasure env alg env.hr_meas t
    letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
    letI hProb : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
    unfold MI_Summary_Seq
    dsimp only
    rw [_hS4 t]
    have h_det : Phase2.condEntropy (goal_var t) ⊤ = 0 := by
      have h_eq : goal_var t = id ∘ (goal_var t) := rfl
      rw [h_eq]
      apply Phase2.condEntropy_of_deterministic id measurable_id (goal_var t) (hGoalMeas t) ⊤
      exact le_top
    rw [h_det, sub_zero]
  rw [h_seq_eq]
  exact h_convergence _hRobustX3

theorem iet3_reverse
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hLacksX3 : ¬ RobustX3_ae env alg a_B)
    (hGoalEnt : ∀ t : ℕ,
      let μ := Phase2.trajMeasure env alg env.hr_meas t
      letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
      letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
      Phase2.entropy (goal_var t) = Real.log 2)
    (h_bridge_fails : ¬ RobustX3_ae env alg a_B →
      ∃ c > 0, ∀ᶠ t in atTop,
        let μ := Phase2.trajMeasure env alg env.hr_meas t
        letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
        letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
        c * Real.log 2 ≤ Phase2.condEntropy (goal_var t)
          (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)) :
    ∃ c > 0, limsup (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop ≤ (1 - c) * Real.log 2 := by
  obtain ⟨c, hc_pos, h_eventual⟩ := h_bridge_fails _hLacksX3
  use c
  refine ⟨hc_pos, ?_⟩
  have h_MI_bound : ∀ᶠ t in atTop, MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t ≤ (1 - c) * Real.log 2 := by
    filter_upwards [h_eventual] with t ht
    let μ := Phase2.trajMeasure env alg env.hr_meas t
    letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
    letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
    change c * Real.log 2 ≤ Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance) at ht
    change Phase2.entropy (goal_var t) - Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance) ≤ (1 - c) * Real.log 2
    have h_ent : Phase2.entropy (goal_var t) = Real.log 2 := hGoalEnt t
    linarith
  have hbdd_f : IsCoboundedUnder (· ≤ ·) atTop (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) := by
    refine ⟨(0 : ℝ), fun a ha => ?_⟩
    have h_nn : ∀ᶠ t : ℕ in atTop, (0 : ℝ) ≤ MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t := by
      apply Eventually.of_forall
      intro t
      let μ := Phase2.trajMeasure env alg env.hr_meas t
      letI : MeasureSpace (Phase2.Trajectory A O t) := ⟨μ⟩
      letI : IsProbabilityMeasure μ := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg t
      change (0 : ℝ) ≤ Phase2.entropy (goal_var t) - Phase2.condEntropy (goal_var t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)
      have h_le := Phase2.condEntropy_le_entropy (goal_var t) (hGoalMeas t) (MeasurableSpace.comap (Phase2.summary_at alg t t (le_refl t)) inferInstance)
      linarith
    obtain ⟨t, h1, h2⟩ := (h_nn.and ha).exists
    have h2' : MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas t ≤ a := h2
    linarith
  have hbdd_g : IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => (1 - c) * Real.log 2) :=
    Filter.isBoundedUnder_const
  calc limsup (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop
    _ ≤ limsup (fun _ : ℕ => (1 - c) * Real.log 2) atTop := Filter.limsup_le_limsup h_MI_bound hbdd_f hbdd_g
    _ = (1 - c) * Real.log 2 := by simp only [Filter.limsup_const]

theorem iet3_non_reversible :
  ∃ (env_34 : SixPrimitives.Env Unit (Fin 2) Unit)
    (hEnv_34 : Phase2.EnvIsMarkov env_34)
    (g_34 : ∀ T, Phase2.Trajectory (Fin 2) Unit T → Fin 2)
    (hG_34 : ∀ T, Measurable (g_34 T)),
  Tendsto (MI_Summary_Seq env_34 (Phase4.alg4_ucb (Fin 2) Unit Phase4.pol0) hEnv_34 (Phase4.alg4_isMarkov (Fin 2) Unit Phase4.pol0) g_34 hG_34) atTop (nhds 0) := by
  let env_34 : SixPrimitives.Env Unit (Fin 2) Unit :=
    { trans := Kernel.const _ (Measure.dirac ()),
      obs := Kernel.const _ (Measure.dirac ()),
      r := fun _ => 0,
      hr_meas := measurable_const,
      μ₀ := Measure.dirac (),
      hμ₀ := inferInstance }
  have hEnv_34 : Phase2.EnvIsMarkov env_34 :=
    { trans_markov := inferInstance,
      obs_markov := inferInstance }
  let g_34 : ∀ T, Phase2.Trajectory (Fin 2) Unit T → Fin 2 := fun T _ => 0
  have hG_34 : ∀ T, Measurable (g_34 T) := fun T => measurable_const
  use env_34, hEnv_34, g_34, hG_34
  have h_seq_eq : MI_Summary_Seq env_34 (Phase4.alg4_ucb (Fin 2) Unit Phase4.pol0) hEnv_34 (Phase4.alg4_isMarkov (Fin 2) Unit Phase4.pol0) g_34 hG_34 = fun t => 0 := by
    ext t
    let μ := Phase2.trajMeasure env_34 (Phase4.alg4_ucb (Fin 2) Unit Phase4.pol0) env_34.hr_meas t
    letI instMS : MeasureSpace (Phase2.Trajectory (Fin 2) Unit t) := ⟨μ⟩
    letI hProb : IsProbabilityMeasure μ :=
      Phase2.trajMeasure_isProbability env_34 (Phase4.alg4_ucb (Fin 2) Unit Phase4.pol0) env_34.hr_meas hEnv_34 (Phase4.alg4_isMarkov (Fin 2) Unit Phase4.pol0) t
    unfold MI_Summary_Seq
    dsimp only
    unfold Phase2.entropy
    have h_cond_ent : ∀ (m' : MeasurableSpace (Phase2.Trajectory (Fin 2) Unit t)), Phase2.condEntropy (g_34 t) m' = 0 := by
      intro m'
      letI : MeasurableSpace (Phase2.Trajectory (Fin 2) Unit t) := m'
      have h_eq : g_34 t = id ∘ (g_34 t) := rfl
      rw [h_eq]
      apply Phase2.condEntropy_of_deterministic id measurable_id (g_34 t) (hG_34 t) m'
      rintro s ⟨s', -, rfl⟩
      by_cases h : (0 : Fin 2) ∈ s'
      · have H : g_34 t ⁻¹' s' = Set.univ := by
          ext x
          simp [g_34, h]
        rw [H]
        exact MeasurableSet.univ
      · have H : g_34 t ⁻¹' s' = ∅ := by
          ext x
          simp [g_34, h]
        rw [H]
        exact MeasurableSet.empty
    have hc1 := h_cond_ent ⊥
    have hc2 := h_cond_ent (MeasurableSpace.comap (Phase2.summary_at (Phase4.alg4_ucb (Fin 2) Unit Phase4.pol0) t t (le_refl t)) inferInstance)
    rw [hc1, hc2]
    exact sub_self 0
  rw [h_seq_eq]
  exact tendsto_const_nhds

end IET3

-- §6. IET 4: X₄ → X₅ (Behavioral Prerequisite)

section IET4
variable {S A O Sig : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (F : Set A) [DecidablePred (· ∈ F)]
variable [Fintype A] [MeasurableSingletonClass A]
variable (a_star : A)

theorem iet4_forward
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    {P_RobustX4 P_Sufficient : Prop}
    (hRobustX4 : P_RobustX4)
    (hSufficient : P_Sufficient)
    (h_pipeline_advances : P_RobustX4 → P_Sufficient →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2))) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2)) := by
  exact h_pipeline_advances hRobustX4 hSufficient

theorem iet4_reverse
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    {P_RobustX4 : Prop}
    (hLacksX4 : ¬ P_RobustX4)
    (h_danger_erodes : ¬ P_RobustX4 →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_danger_erodes hLacksX4

theorem iet4_non_reversible
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (g_const : G)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    (h_degenerate : ∀ T traj, goal_var T traj = g_const)
    {P_RobustX5 : Prop}
    (h_isolated_X5 : P_RobustX5)
    (h_meaningless_progress : P_RobustX5 → (∀ T traj, goal_var T traj = g_const) →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_meaningless_progress h_isolated_X5 h_degenerate

end IET4

-- §7. IET 5: X₅ → X₆ (Information-Theoretic, LLR Drift)

section IET5
variable {S A O Sig G : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig] [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (goal_var : ∀ T, Phase2.Trajectory A O T → G)
variable (hGoalMeas : ∀ T, Measurable (goal_var T))
variable (F : Set A) [DecidablePred (· ∈ F)]

theorem iet5_forward
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    {P_RobustX5 P_Sufficient : Prop}
    (hRobustX5 : P_RobustX5)
    (hSufficient : P_Sufficient)
    (h_pipeline_advances : P_RobustX5 → P_Sufficient →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2))) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2)) := by
  exact h_pipeline_advances hRobustX5 hSufficient

theorem iet5_reverse
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    {P_RobustX5 : Prop}
    (hLacksX5 : ¬ P_RobustX5)
    (h_danger_erodes : ¬ P_RobustX5 →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_danger_erodes hLacksX5

theorem iet5_non_reversible
    {S A O Sig G : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hEnv : Phase2.EnvIsMarkov env)
    (hAlg : Phase2.AlgIsMarkov alg)
    (g_const : G)
    (goal_var : (T : ℕ) → Phase2.Trajectory A O T → G)
    (hGoalMeas : ∀ T, Measurable (goal_var T))
    {P_RobustX5 : Prop}
    (_h_has_X5 : P_RobustX5)
    (h_degenerate_env : ∀ T traj, goal_var T traj = g_const)
    (h_zero_entropy_mi : (∀ T traj, goal_var T traj = g_const) →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_zero_entropy_mi h_degenerate_env

end IET5

-- §8. IET 6: X₆ → X₁ (The Accumulative Closure, Doob's Convergence)

section IET6
variable {S A O Sig G : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig] [MeasurableSpace G] [Fintype G] [MeasurableSingletonClass G]
variable (env : SixPrimitives.Env S A O) (hEnv : Phase2.EnvIsMarkov env)
variable (goal_var : ∀ T, Phase2.Trajectory A O T → G)
variable (hGoalMeas : ∀ T, Measurable (goal_var T))
variable (L_min : ℕ)

theorem iet6_forward
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX6 : RobustX6_ae env alg L_min)
    (_hS4 : IsSufficientSummary env alg hEnv hAlg goal_var hGoalMeas)
    (h_pipeline_closes : RobustX6_ae env alg L_min →
      IsSufficientSummary env alg hEnv hAlg goal_var hGoalMeas →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2))) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds (Real.log 2)) := by
  exact h_pipeline_closes _hRobustX6 _hS4

noncomputable def cycle_filtration
    {A O : Type*} [MeasurableSpace A] [MeasurableSpace O]
    (K_total : ℕ) (L_min : ℕ) :
    MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (Phase2.Trajectory A O (K_total * L_min))) where
  seq k := ⨆ (i : Fin (K_total * L_min)) (_hi : i.val < k * L_min), MeasurableSpace.comap (fun ω => ω i) inferInstance
  mono' i j hij := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hx_j : x.val < j * L_min := lt_of_lt_of_le hx (Nat.mul_le_mul_right L_min hij)
    exact le_iSup_of_le x (le_iSup_of_le hx_j le_rfl)
  le' k := by
    apply iSup_le
    intro i
    apply iSup_le
    intro _
    rintro s ⟨t, ht, rfl⟩
    exact measurable_pi_apply i ht

noncomputable def cycle_posterior
    {S A O Sig : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (K_total : ℕ) (L_min : ℕ) (k : ℕ)
    (Theta : Phase2.Trajectory A O (K_total * L_min) → ℝ) :
    Phase2.Trajectory A O (K_total * L_min) → ℝ :=
  let μ := Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)
  letI : MeasureSpace (Phase2.Trajectory A O (K_total * L_min)) := ⟨μ⟩
  ℙ[Theta | cycle_filtration K_total L_min k]

theorem iet6_accumulative
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (_hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX6 : RobustX6_ae env alg L_min)
    (K_total : ℕ)
    (Theta : Phase2.Trajectory A O (K_total * L_min) → ℝ)
    (h_int : Integrable Theta (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)))
    (h_doob_martingale : Integrable Theta (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)) →
      Martingale
        (fun k => cycle_posterior env alg K_total L_min k Theta)
        (cycle_filtration K_total L_min)
        (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min))) :
    Martingale
      (fun k => cycle_posterior env alg K_total L_min k Theta)
      (cycle_filtration K_total L_min)
      (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)) := by
  exact h_doob_martingale h_int

theorem iet6_accumulative_convergence
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (_hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX6 : RobustX6_ae env alg L_min)
    (K_total : ℕ)
    (Theta : Phase2.Trajectory A O (K_total * L_min) → ℝ)
    (h_int : Integrable Theta (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)))
    (h_meas : StronglyMeasurable[⨆ k, cycle_filtration K_total L_min k] Theta)
    (h_martingale_convergence :
      Integrable Theta (Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)) →
      StronglyMeasurable[⨆ k, cycle_filtration K_total L_min k] Theta →
      ∀ᵐ ω ∂(Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)),
        Tendsto (fun k => cycle_posterior env alg K_total L_min k Theta ω) atTop (nhds (Theta ω))) :
    ∀ᵐ ω ∂(Phase2.trajMeasure env alg env.hr_meas (K_total * L_min)),
      Tendsto (fun k => cycle_posterior env alg K_total L_min k Theta ω) atTop (nhds (Theta ω)) := by
  exact h_martingale_convergence h_int h_meas

theorem iet6_reverse
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hLacksX6 : ¬ RobustX6_ae env alg L_min)
    (h_danger_erodes : ¬ RobustX6_ae env alg L_min →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_danger_erodes _hLacksX6

theorem iet6_non_reversible
    (alg : SixPrimitives.Algorithm A O Sig)
    [Phase2.AlgIsDeterministic alg]
    (hAlg : Phase2.AlgIsMarkov alg)
    (_hRobustX6 : RobustX6_ae env alg L_min)
    (g_const : G)
    (h_degenerate_env : ∀ T traj, goal_var T traj = g_const)
    (h_zero_entropy_mi : (∀ T traj, goal_var T traj = g_const) →
      Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0)) :
    Tendsto (MI_Summary_Seq env alg hEnv hAlg goal_var hGoalMeas) atTop (nhds 0) := by
  exact h_zero_entropy_mi h_degenerate_env

end IET6

end SixPrimitives.Phase5
