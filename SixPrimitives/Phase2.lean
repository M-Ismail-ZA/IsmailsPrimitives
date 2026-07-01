import SixPrimitives.Phase0
import SixPrimitives.Phase1
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

/-! # Ismail's Primitives — Phase 2: Trajectory Measure & Environments -/

open MeasureTheory ProbabilityTheory Filter Real BigOperators
open scoped ENNReal NNReal
set_option synthInstance.maxHeartbeats 500000

namespace SixPrimitives.Phase2

-- MARKOV-KERNEL BUNDLES

structure EnvIsMarkov {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : SixPrimitives.Env S A O) : Prop where
  trans_markov : IsMarkovKernel env.trans
  obs_markov   : IsMarkovKernel env.obs

structure AlgIsMarkov {A O Sig : Type*}
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (alg : SixPrimitives.Algorithm A O Sig) : Prop where
  act_markov    : IsMarkovKernel alg.act
  update_markov : IsMarkovKernel alg.update

-- DETERMINISTIC-KERNEL BUNDLES

structure EnvIsDeterministic {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : SixPrimitives.Env S A O) where
  s₀           : S
  μ₀_eq        : env.μ₀ = Measure.dirac s₀
  transFn      : S × A → S
  transFn_meas : Measurable transFn
  trans_eq     : ∀ x, env.trans x = Measure.dirac (transFn x)
  obsFn        : S × A → O
  obsFn_meas   : Measurable obsFn
  obs_eq       : ∀ x, env.obs x = Measure.dirac (obsFn x)

structure TransIsDeterministic {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : SixPrimitives.Env S A O) where
  s₀           : S
  μ₀_eq        : env.μ₀ = Measure.dirac s₀
  transFn      : S × A → S
  transFn_meas : Measurable transFn
  trans_eq     : ∀ x, env.trans x = Measure.dirac (transFn x)

def EnvIsDeterministic.toTrans {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    {env : SixPrimitives.Env S A O}
    (hD : EnvIsDeterministic env) : TransIsDeterministic env where
  s₀ := hD.s₀
  μ₀_eq := hD.μ₀_eq
  transFn := hD.transFn
  transFn_meas := hD.transFn_meas
  trans_eq := hD.trans_eq

class AlgIsDeterministic {A O Sig : Type*}
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (alg : SixPrimitives.Algorithm A O Sig) where
  actFn         : Sig → A
  actFn_meas    : Measurable actFn
  act_eq        : ∀ σ, alg.act σ = Measure.dirac (actFn σ)
  updateFn      : Sig × A × O × ℝ → Sig
  updateFn_meas : Measurable updateFn
  update_eq     : ∀ x, alg.update x = Measure.dirac (updateFn x)

instance algIsDeterministic_isMarkov {A O Sig : Type*}
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (alg : SixPrimitives.Algorithm A O Sig) [h : AlgIsDeterministic alg] :
    AlgIsMarkov alg where
  act_markov := by
    have heq : alg.act = Kernel.deterministic h.actFn h.actFn_meas :=
      DFunLike.ext _ _ (fun σ => by rw [h.act_eq, Kernel.deterministic_apply])
    rw [heq]; infer_instance
  update_markov := by
    have heq : alg.update = Kernel.deterministic h.updateFn h.updateFn_meas :=
      DFunLike.ext _ _ (fun x => by rw [h.update_eq, Kernel.deterministic_apply])
    rw [heq]; infer_instance

instance envIsDeterministic_isMarkov {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : SixPrimitives.Env S A O) (hD : EnvIsDeterministic env) :
    EnvIsMarkov env where
  trans_markov := by
    have heq : env.trans = Kernel.deterministic hD.transFn hD.transFn_meas :=
      DFunLike.ext _ _ (fun x => by rw [hD.trans_eq, Kernel.deterministic_apply])
    rw [heq]; infer_instance
  obs_markov := by
    have heq : env.obs = Kernel.deterministic hD.obsFn hD.obsFn_meas :=
      DFunLike.ext _ _ (fun x => by rw [hD.obs_eq, Kernel.deterministic_apply])
    rw [heq]; infer_instance

-- ONE-STEP KERNEL

variable {S A O Sig : Type*}
  [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]

noncomputable def oneStepKernel
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) :
    Kernel (Sig × S) (A × O × ℝ × Sig × S) :=
  let actK : Kernel (Sig × S) A :=
    alg.act.comap Prod.fst measurable_fst
  let obsK : Kernel ((Sig × S) × A) O :=
    env.obs.comap (fun x : (Sig × S) × A => (x.1.2, x.2)) (by measurability)
  let rewK : Kernel ((Sig × S) × (A × O)) ℝ :=
    Kernel.deterministic (fun x : (Sig × S) × (A × O) => env.r (x.1.2, x.2.1))
      (hr.comp (by measurability))
  let transK : Kernel ((Sig × S) × ((A × O) × ℝ)) S :=
    env.trans.comap (fun x : (Sig × S) × ((A × O) × ℝ) => (x.1.2, x.2.1.1)) (by measurability)
  let updK : Kernel ((Sig × S) × (((A × O) × ℝ) × S)) Sig :=
    alg.update.comap
      (fun x : (Sig × S) × (((A × O) × ℝ) × S) =>
         (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2))
      (by measurability)
  let chain := (((actK.compProd obsK).compProd rewK).compProd transK).compProd updK
  chain.map (fun p : ((((A × O) × ℝ) × S) × Sig) =>
                (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2))

theorem oneStepKernel_isMarkov
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg) :
    IsMarkovKernel (oneStepKernel env alg hr) := by
  simp only [oneStepKernel]
  haveI := hAlg.act_markov
  haveI := hAlg.update_markov
  haveI := hEnv.trans_markov
  haveI := hEnv.obs_markov
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

-- RECURSIVE TRAJECTORY KERNEL (AUXILIARY)

noncomputable def trajMeasureAux
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) :
    ∀ T : ℕ, Kernel (Sig × S) ((Fin T → A × O × ℝ) × (Sig × S))
  | 0 =>
    Kernel.id.map (fun σs => (Fin.elim0, σs))
  | T + 1 =>
    let κT := trajMeasureAux env alg hr T
    let η : Kernel ((Sig × S) × ((Fin T → A × O × ℝ) × (Sig × S))) (A × O × ℝ × Sig × S) :=
      (oneStepKernel env alg hr).comap (fun x => x.2.2)
        (measurable_snd.comp measurable_snd)
    (κT.compProd η).map
      (fun x =>
        (Fin.snoc x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), (x.2.2.2.2.1, x.2.2.2.2.2)))

theorem trajMeasureAux_isMarkov
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg) :
    ∀ T : ℕ, IsMarkovKernel (trajMeasureAux env alg hr T) := by
  intro T; induction T with
  | zero =>
    simp only [trajMeasureAux]
    exact Kernel.IsMarkovKernel.map _ (by fun_prop)
  | succ T ih =>
    simp only [trajMeasureAux]
    haveI h_osk : IsMarkovKernel (oneStepKernel env alg hr) :=
      oneStepKernel_isMarkov env alg hr hEnv hAlg
    haveI hκT : IsMarkovKernel (trajMeasureAux env alg hr T) := ih
    apply Kernel.IsMarkovKernel.map
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]
        fun_prop
      · intro j
        simp only [Fin.snoc_castSucc]
        fun_prop
    · fun_prop

-- TRAJECTORY MEASURE (PUBLIC INTERFACE)

abbrev Trajectory (A O : Type*) (T : ℕ) := Fin T → A × O × ℝ

noncomputable def trajMeasure
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (T : ℕ) : Measure (Trajectory A O T) :=
  let κT := trajMeasureAux env alg hr T
  let μ₀ : Measure (Sig × S) := (Measure.dirac alg.σ₀).prod env.μ₀
  (μ₀.bind κT).map Prod.fst

lemma trajMeasure_isProbability
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg) (T : ℕ) :
    IsProbabilityMeasure (trajMeasure env alg hr T) := by
  simp only [trajMeasure]
  haveI hMark := trajMeasureAux_isMarkov env alg hr hEnv hAlg T
  haveI henv : IsProbabilityMeasure env.μ₀ := env.hμ₀
  haveI hdirac : IsProbabilityMeasure (Measure.dirac (α := Sig) alg.σ₀) := inferInstance
  haveI hprod : IsProbabilityMeasure ((Measure.dirac alg.σ₀).prod env.μ₀) := inferInstance
  haveI hbind : IsProbabilityMeasure
      (((Measure.dirac alg.σ₀).prod env.μ₀).bind ↑(trajMeasureAux env alg hr T)) := by
    apply isProbabilityMeasure_bind
    · exact (trajMeasureAux env alg hr T).measurable'.aemeasurable
    · exact ae_of_all _ (fun x => inferInstance)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- STATE MARGINAL AND EXPECTED VISITS

noncomputable def stateMarginal
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr  : Measurable env.r)
    (t   : ℕ) : Measure S :=
  let μ₀ : Measure (Sig × S) := (Measure.dirac alg.σ₀).prod env.μ₀
  ((μ₀.bind (trajMeasureAux env alg hr (t + 1))).map (Prod.snd ∘ Prod.snd))

lemma stateMarginal_isProbability
    (env  : SixPrimitives.Env S A O)
    (alg  : SixPrimitives.Algorithm A O Sig)
    (hr   : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (t    : ℕ) : IsProbabilityMeasure (stateMarginal env alg hr t) := by
  simp only [stateMarginal]
  haveI henv : IsProbabilityMeasure env.μ₀ := env.hμ₀
  haveI hdirac : IsProbabilityMeasure (Measure.dirac (α := Sig) alg.σ₀) := inferInstance
  haveI h1 : IsProbabilityMeasure ((Measure.dirac alg.σ₀).prod env.μ₀) := inferInstance
  haveI h2 : IsMarkovKernel (trajMeasureAux env alg hr (t + 1)) :=
    trajMeasureAux_isMarkov env alg hr hEnv hAlg (t + 1)
  haveI h3 : IsProbabilityMeasure
      (((Measure.dirac alg.σ₀).prod env.μ₀).bind (trajMeasureAux env alg hr (t + 1))) := by
    apply isProbabilityMeasure_bind
    · exact (trajMeasureAux env alg hr (t + 1)).measurable'.aemeasurable
    · exact ae_of_all _ (fun _ => inferInstance)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def expectedVisits
    [MeasurableSingletonClass S]
    (env    : SixPrimitives.Env S A O)
    (alg    : SixPrimitives.Algorithm A O Sig)
    (hr     : Measurable env.r)
    (T      : ℕ)
    (s_star : S) : ℝ :=
  ∑ t : Fin T, (stateMarginal env alg hr t.val {s_star}).toReal

-- BACKWARD-COMPAT LEMMA

lemma expectedVisits_unit_state {A O : Type*}
    [MeasurableSpace A] [MeasurableSpace O]
    (env  : SixPrimitives.Env Unit A O)
    (alg  : SixPrimitives.Algorithm A O Sig)
    (hr   : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T    : ℕ) : expectedVisits env alg hr T () = T := by
  classical
  simp only [expectedVisits]
  have h_one : ∀ t : Fin T,
      (stateMarginal env alg hr t.val {()}).toReal = 1 := by
    intro t
    have hProb : IsProbabilityMeasure (stateMarginal env alg hr t.val) :=
      stateMarginal_isProbability env alg hr hEnv hAlg t.val
    have hUniv : ({()} : Set Unit) = Set.univ := by
      ext x
      constructor
      · intro _
        exact trivial
      · intro _
        cases x
        rfl
    have hval : (stateMarginal env alg hr t.val) {()} = 1 := by
      rw [hUniv]
      exact hProb.measure_univ
    rw [hval, ENNReal.toReal_one]
  have h_sum : ∑ t : Fin T, (1 : ℝ) = T := by
    simp [Finset.sum_const]
  simp [h_one]

-- STATE / SUMMARY PROJECTIONS

noncomputable def summary_t
    (alg : SixPrimitives.Algorithm A O Sig)
    [h : AlgIsDeterministic alg] :
    ∀ (t : ℕ), (Fin t → A × O × ℝ) → Sig
  | 0, _ => alg.σ₀
  | t + 1, ω =>
      h.updateFn
        (summary_t alg t (fun i => ω (Fin.castSucc i)),
         (ω (Fin.last t)).1,
         (ω (Fin.last t)).2.1,
         (ω (Fin.last t)).2.2)

noncomputable def state_t
    (env : SixPrimitives.Env S A O)
    (hD : TransIsDeterministic env)
    {T : ℕ} (ω : Fin T → A × O × ℝ) : ℕ → S
  | 0     => hD.s₀
  | t + 1 =>
      if h : t < T then
        hD.transFn (state_t env hD ω t, (ω ⟨t, h⟩).1)
      else
        state_t env hD ω t

@[simp]
lemma state_t_zero (env : SixPrimitives.Env S A O)
    (hD : TransIsDeterministic env) {T : ℕ} (ω : Fin T → A × O × ℝ) :
    state_t env hD ω 0 = hD.s₀ := rfl

lemma state_t_succ (env : SixPrimitives.Env S A O)
    (hD : TransIsDeterministic env) {T : ℕ} (ω : Fin T → A × O × ℝ)
    (t : ℕ) (ht : t < T) :
    state_t env hD ω (t + 1) = hD.transFn (state_t env hD ω t, (ω ⟨t, ht⟩).1) := by
  simp [state_t, ht]

@[simp]
lemma summary_t_zero (alg : SixPrimitives.Algorithm A O Sig)
    [AlgIsDeterministic alg] (ω : Fin 0 → A × O × ℝ) :
    summary_t alg 0 ω = alg.σ₀ := rfl

@[simp]
lemma summary_t_succ (alg : SixPrimitives.Algorithm A O Sig)
    [h : AlgIsDeterministic alg] {t : ℕ} (ω : Fin (t + 1) → A × O × ℝ) :
    summary_t alg (t + 1) ω =
      h.updateFn
        (summary_t alg t (fun i => ω (Fin.castSucc i)),
         (ω (Fin.last t)).1,
         (ω (Fin.last t)).2.1,
         (ω (Fin.last t)).2.2) := rfl

-- TRAJECTORY PROJECTIONS AND SUMMARY INFRASTRUCTURE

def traj_action (t : ℕ) {T : ℕ} (ht : t < T) : Trajectory A O T → A :=
  fun ω => (ω ⟨t, ht⟩).1

def traj_observation (t : ℕ) {T : ℕ} (ht : t < T) : Trajectory A O T → O :=
  fun ω => (ω ⟨t, ht⟩).2.1

def traj_reward (t : ℕ) {T : ℕ} (ht : t < T) : Trajectory A O T → ℝ :=
  fun ω => (ω ⟨t, ht⟩).2.2

lemma measurable_traj_action (t : ℕ) {T : ℕ} (ht : t < T) :
    Measurable (traj_action (A := A) (O := O) t ht) :=
  measurable_fst.comp (measurable_pi_apply (⟨t, ht⟩ : Fin T))

lemma measurable_traj_observation (t : ℕ) {T : ℕ} (ht : t < T) :
    Measurable (traj_observation (A := A) (O := O) t ht) :=
  (measurable_fst.comp measurable_snd).comp (measurable_pi_apply (⟨t, ht⟩ : Fin T))

lemma measurable_traj_reward (t : ℕ) {T : ℕ} (ht : t < T) :
    Measurable (traj_reward (A := A) (O := O) t ht) :=
  (measurable_snd.comp measurable_snd).comp (measurable_pi_apply (⟨t, ht⟩ : Fin T))

noncomputable def summary_at
    (alg : SixPrimitives.Algorithm A O Sig) [AlgIsDeterministic alg]
    (t T : ℕ) (ht : t ≤ T) : Trajectory A O T → Sig :=
  fun ω => summary_t alg t (fun (i : Fin t) => ω (Fin.castLE ht i))

@[simp]
lemma summary_at_zero
    (alg : SixPrimitives.Algorithm A O Sig) [AlgIsDeterministic alg] (T : ℕ) :
    summary_at alg 0 T (Nat.zero_le T) = fun _ => alg.σ₀ := by
  ext ω; simp [summary_at]

lemma summary_at_succ
    (alg : SixPrimitives.Algorithm A O Sig) [h : AlgIsDeterministic alg]
    (t T : ℕ) (ht : t + 1 ≤ T) (ω : Trajectory A O T) :
    summary_at alg (t + 1) T ht ω =
      h.updateFn
        (summary_at alg t T (Nat.le_of_succ_le ht) ω,
         traj_action t (Nat.lt_of_succ_le ht) ω,
         traj_observation t (Nat.lt_of_succ_le ht) ω,
         traj_reward t (Nat.lt_of_succ_le ht) ω) := by
  simp only [summary_at, summary_t_succ, traj_action, traj_observation, traj_reward]
  have h_cast : ∀ i : Fin t,
      Fin.castLE ht (Fin.castSucc i) = Fin.castLE (Nat.le_of_succ_le ht) i :=
    fun i => Fin.ext (by simp)
  have h_last : Fin.castLE ht (Fin.last t) = ⟨t, Nat.lt_of_succ_le ht⟩ :=
    Fin.ext (by simp)
  simp_rw [h_cast, h_last]

lemma summary_at_measurable
    (alg : SixPrimitives.Algorithm A O Sig) [h : AlgIsDeterministic alg]
    (t T : ℕ) (ht : t ≤ T) :
    Measurable (summary_at alg t T ht) := by
  induction t with
  | zero =>
    simp [summary_at_zero]
  | succ t ih =>
    have ht' : t ≤ T := Nat.le_of_succ_le ht
    have htlt : t < T := Nat.lt_of_succ_le ht
    have h_eq : summary_at alg (t + 1) T ht =
        h.updateFn ∘ (fun ω : Trajectory A O T =>
          (summary_at alg t T ht' ω,
           traj_action t htlt ω,
           traj_observation t htlt ω,
           traj_reward t htlt ω)) := by
      ext ω; exact summary_at_succ alg t T ht ω
    rw [h_eq]
    apply h.updateFn_meas.comp
    apply Measurable.prodMk (ih ht')
    apply Measurable.prodMk (measurable_traj_action t htlt)
    apply Measurable.prodMk (measurable_traj_observation t htlt)
    exact measurable_traj_reward t htlt

-- ALMOST-SURE CONSISTENCY

lemma oneStepKernel_act_ae_eq
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) [h : AlgIsDeterministic alg] [hA : MeasurableSingletonClass A]
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (σ : Sig) (s : S) :
    ∀ᵐ step ∂(oneStepKernel env alg hr (σ, s)), step.1 = h.actFn σ := by
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have hmf_step : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp
          (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp
            (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {x : A × O × ℝ × Sig × S | x.1 = h.actFn σ} := by
    measurability
  simp only [oneStepKernel]
  rw [Kernel.map_apply (hf := hmf_step)]
  rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set]
  rw [Kernel.ae_compProd_iff (by measurability)]
  rw [Kernel.ae_compProd_iff (by measurability)]
  rw [Kernel.ae_compProd_iff (by measurability)]
  rw [Kernel.ae_compProd_iff (by measurability)]
  simp only [Kernel.comap_apply, h.act_eq, ae_dirac_eq, Filter.eventually_pure]
  apply ae_of_all; intro o
  apply ae_of_all; intro r
  apply ae_of_all; intro s'
  apply ae_of_all; intro σ'
  simp

lemma oneStepKernel_update_ae_eq
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) [h : AlgIsDeterministic alg]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (hAlg : AlgIsMarkov alg)
    (σ : Sig) (s : S) :
    ∀ᵐ step ∂(oneStepKernel env alg hr (σ, s)),
      step.2.2.2.1 = h.updateFn (σ, step.1, step.2.1, step.2.2.1) := by
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have hmf_step : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp
          (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp
            (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {x : A × O × ℝ × Sig × S |
      x.2.2.2.1 = h.updateFn (σ, x.1, x.2.1, x.2.2.1)} := by
    apply measurableSet_eq_fun
    · exact measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    · exact h.updateFn_meas.comp
        (measurable_const.prodMk
          (measurable_fst.prodMk
            ((measurable_fst.comp measurable_snd).prodMk
              (measurable_fst.comp (measurable_snd.comp measurable_snd)))))
  simp only [oneStepKernel]
  rw [Kernel.map_apply (hf := hmf_step)]
  rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set]
  refine (Kernel.ae_compProd_iff (hmf_step h_set)).mpr ?_
  apply ae_of_all; intro a
  simp only [Kernel.comap_apply, h.update_eq, Set.mem_setOf_eq, ae_dirac_eq, Filter.eventually_pure]

lemma trajMeasureAux_ae_consistency
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) [AlgIsDeterministic alg]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig] [MeasurableSingletonClass A] [MeasurableEq A]
    (hEnv : EnvIsMarkov env)
    (T : ℕ) (s₀ : S) :
    ∀ᵐ x ∂(trajMeasureAux env alg hr T (alg.σ₀, s₀)),
      x.2.1 = summary_t alg T x.1
      ∧ ∀ t (ht : t < T),
          (x.1 ⟨t, ht⟩).1 =
            AlgIsDeterministic.actFn alg
              (summary_t alg t (fun i => x.1 ⟨i.1, Nat.lt_trans i.2 ht⟩)) := by
  induction T with
  | zero =>
    simp only [trajMeasureAux, summary_t_zero]
    have h_meas : Measurable (fun σs : Sig × S => ((Fin.elim0 : Fin 0 → A × O × ℝ), σs)) :=
      Measurable.prodMk measurable_const measurable_id
    have h_set : MeasurableSet {x : (Fin 0 → A × O × ℝ) × Sig × S |
      x.2.1 = alg.σ₀ ∧ ∀ (t : ℕ) (ht : t < 0),
        (x.1 ⟨t, ht⟩).1 = AlgIsDeterministic.actFn alg
          (summary_t alg t fun i => x.1 ⟨↑i, Nat.lt_trans i.2 ht⟩)} := by
      have h_eq : {x : (Fin 0 → A × O × ℝ) × Sig × S |
        x.2.1 = alg.σ₀ ∧ ∀ (t : ℕ) (ht : t < 0),
          (x.1 ⟨t, ht⟩).1 = AlgIsDeterministic.actFn alg
            (summary_t alg t fun i => x.1 ⟨↑i, Nat.lt_trans i.2 ht⟩)} =
        {x : (Fin 0 → A × O × ℝ) × Sig × S | x.2.1 = alg.σ₀} := by
        ext x; simp
      rw [h_eq]
      measurability
    rw [Kernel.map_apply (hf := h_meas), Kernel.id_apply]
    rw [MeasureTheory.ae_map_iff h_meas.aemeasurable h_set]
    rw [MeasureTheory.ae_dirac_iff]
    · constructor
      · rfl
      · intro t ht
        exact (Nat.not_lt_zero t ht).elim
    · measurability
  | succ T' ih =>
    simp only [trajMeasureAux]
    have hAlg : AlgIsMarkov alg := algIsDeterministic_isMarkov alg
    haveI h_osk : IsMarkovKernel (oneStepKernel env alg hr) :=
      oneStepKernel_isMarkov env alg hr hEnv hAlg
    haveI hκT : IsMarkovKernel (trajMeasureAux env alg hr T') :=
      trajMeasureAux_isMarkov env alg hr hEnv hAlg T'
    let f : ((Fin T' → A × O × ℝ) × (Sig × S)) × (A × O × ℝ × Sig × S) →
              (Fin (T' + 1) → A × O × ℝ) × (Sig × S) :=
      fun p => (Fin.snoc (α := fun _ => A × O × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2.1, p.2.2.2.2.2)
    have h_f_meas : Measurable f := by
      apply Measurable.prodMk
      · apply measurable_pi_lambda
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; fun_prop
        · intro j; simp only [Fin.snoc_castSucc]; fun_prop
      · apply Measurable.prodMk
        · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have h_set₁ : MeasurableSet {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S | x.2.1 = summary_t alg (T' + 1) x.1} := by
      have h_sum : Measurable (fun x : (Fin (T' + 1) → A × O × ℝ) × Sig × S => summary_t alg (T' + 1) x.1) := by
        change Measurable (summary_at alg (T' + 1) (T' + 1) (le_refl _) ∘ Prod.fst)
        exact (summary_at_measurable alg (T' + 1) (T' + 1) (le_refl _)).comp measurable_fst
      exact measurableSet_eq_fun (measurable_fst.comp measurable_snd) h_sum
    have h_set₂ : MeasurableSet {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S |
        ∀ t (ht : t < T' + 1), (x.1 ⟨t, ht⟩).1 =
          AlgIsDeterministic.actFn alg (summary_t alg t fun i => x.1 ⟨i.1, Nat.lt_trans i.2 ht⟩)} := by
      have h_eq : {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S |
          ∀ t (ht : t < T' + 1), (x.1 ⟨t, ht⟩).1 =
            AlgIsDeterministic.actFn alg (summary_t alg t fun i => x.1 ⟨i.1, Nat.lt_trans i.2 ht⟩)} =
          ⋂ (i : Fin (T' + 1)), {x | (x.1 i).1 =
            AlgIsDeterministic.actFn alg (summary_at alg i.1 (T' + 1) (Nat.le_of_lt i.2) x.1)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i
          have h_at : summary_t alg i.1 (fun j => x.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩) =
            summary_at alg i.1 (T' + 1) (Nat.le_of_lt i.2) x.1 := rfl
          rw [← h_at]
          exact h i.1 i.2
        · intro h t ht
          exact h ⟨t, ht⟩
      rw [h_eq]
      apply MeasurableSet.iInter
      intro i
      have h_lhs : Measurable (fun x : (Fin (T' + 1) → A × O × ℝ) × Sig × S => (x.1 i).1) :=
        measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)
      have h_rhs : Measurable (fun x : (Fin (T' + 1) → A × O × ℝ) × Sig × S =>
        AlgIsDeterministic.actFn alg (summary_at alg i.1 (T' + 1) (Nat.le_of_lt i.2) x.1)) := by
        apply AlgIsDeterministic.actFn_meas.comp
        exact (summary_at_measurable alg i.1 (T' + 1) (Nat.le_of_lt i.2)).comp measurable_fst
      exact measurableSet_eq_fun h_lhs h_rhs
    have h_set : MeasurableSet {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S |
        x.2.1 = summary_t alg (T' + 1) x.1 ∧
        ∀ t (ht : t < T' + 1), (x.1 ⟨t, ht⟩).1 =
          AlgIsDeterministic.actFn alg (summary_t alg t fun i => x.1 ⟨i.1, Nat.lt_trans i.2 ht⟩)} :=
      MeasurableSet.inter h_set₁ h_set₂
    rw [Kernel.map_apply (hf := h_f_meas)]
    rw [MeasureTheory.ae_map_iff h_f_meas.aemeasurable h_set]
    refine (Kernel.ae_compProd_iff (h_f_meas h_set)).mpr ?_
    filter_upwards [ih] with a ha
    rcases ha with ⟨h_sum_a, h_act_a⟩
    simp only [Kernel.comap_apply]
    change ∀ᵐ b ∂(oneStepKernel env alg hr (a.2.1, a.2.2)), _
    have h_act_step := oneStepKernel_act_ae_eq env alg hr hEnv hAlg a.2.1 a.2.2
    have h_upd_step := oneStepKernel_update_ae_eq env alg hr hAlg a.2.1 a.2.2
    filter_upwards [h_act_step, h_upd_step] with b hb_act hb_upd
    constructor
    · change b.2.2.2.1 = AlgIsDeterministic.updateFn alg
        (summary_t alg T' (fun i => Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.castSucc i)),
         (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.last T')).1,
         (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.last T')).2.1,
         (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.last T')).2.2)
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [← h_sum_a]
      exact hb_upd
    · intro t ht
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with ht_lt | ht_eq
      · change (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.castSucc ⟨t, ht_lt⟩)).1 =
          AlgIsDeterministic.actFn alg (summary_t alg t (fun i => Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) ⟨i.1, Nat.lt_trans i.2 ht⟩))
        rw [Fin.snoc_castSucc]
        have h_eq : (fun i : Fin t => (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1)) ⟨i.val, Nat.lt_trans i.isLt ht⟩) =
                    (fun i : Fin t => a.1 ⟨i.val, Nat.lt_trans i.isLt ht_lt⟩) := by
          funext i
          have h_cast_i : (⟨i.val, Nat.lt_trans i.isLt ht⟩ : Fin (T' + 1)) = Fin.castSucc ⟨i.val, Nat.lt_trans i.isLt ht_lt⟩ := rfl
          rw [h_cast_i, Fin.snoc_castSucc]
        rw [h_eq]
        exact h_act_a t ht_lt
      · subst t
        change (Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) (Fin.last T')).1 =
          AlgIsDeterministic.actFn alg (summary_t alg T' (fun i => Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) ⟨i.1, Nat.lt_trans i.2 ht⟩))
        rw [Fin.snoc_last]
        have h_eq_T' : (fun i : Fin T' => Fin.snoc (α := fun _ => A × O × ℝ) a.1 (b.1, b.2.1, b.2.2.1) ⟨i.1, Nat.lt_trans i.2 ht⟩) = a.1 := by
          funext i
          have h_cast_i : (⟨i.1, Nat.lt_trans i.2 ht⟩ : Fin (T' + 1)) = Fin.castSucc i := rfl
          rw [h_cast_i, Fin.snoc_castSucc]
        rw [h_eq_T']
        rw [← h_sum_a]
        exact hb_act

lemma trajMeasure_reward_le
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (t : Fin T) (R_max : ℝ) (h_bound : ∀ s a, |env.r (s, a)| ≤ R_max) :
    ∀ᵐ traj ∂(trajMeasure env alg hr T), |(traj t).2.2| ≤ R_max := by
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  haveI hOSK : IsMarkovKernel (oneStepKernel env alg hr) :=
    oneStepKernel_isMarkov env alg hr hEnv hAlg
  have hmf_step : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp
          (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp
            (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set_step : MeasurableSet {x : A × O × ℝ × Sig × S | |x.2.2.1| ≤ R_max} := by
    measurability
  have hstep : ∀ σs : Sig × S,
      ∀ᵐ step ∂(oneStepKernel env alg hr σs), |step.2.2.1| ≤ R_max := by
    intro ⟨σ, s⟩
    simp only [oneStepKernel]
    rw [Kernel.map_apply (hf := hmf_step)]
    rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set_step]
    rw [Kernel.ae_compProd_iff (by measurability)]
    rw [Kernel.ae_compProd_iff (by measurability)]
    rw [Kernel.ae_compProd_iff (by measurability)]
    apply ae_of_all; intro ao
    simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
    exact ae_of_all _ (fun _ => ae_of_all _ (fun _ => h_bound s ao.1))
  have h_aux : ∀ (T' : ℕ) (σs : Sig × S) (k : Fin T'),
      ∀ᵐ p ∂(trajMeasureAux env alg hr T' σs), |(p.1 k).2.2| ≤ R_max := by
    intro T'
    induction T' with
    | zero => intro _ k; exact k.elim0
    | succ T' ih =>
      haveI := trajMeasureAux_isMarkov env alg hr hEnv hAlg T'
      intro σs k
      have hmf : Measurable (fun x : ((Fin T' → A × O × ℝ) × (Sig × S)) ×
          (A × O × ℝ × Sig × S) =>
          ((Fin.snoc x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1) : Fin (T' + 1) → A × O × ℝ),
           (x.2.2.2.2.1, x.2.2.2.2.2))) := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i
          refine Fin.lastCases ?_ ?_ i
          · simp; fun_prop
          · intro j; simp; fun_prop
        · fun_prop
      have h_set_fin (j : Fin (T' + 1)) :
          MeasurableSet {p : (Fin (T' + 1) → A × O × ℝ) × Sig × S | |(p.1 j).2.2| ≤ R_max} := by
        measurability
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := hmf)]
      refine Fin.lastCases ?_ ?_ k
      · rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.last T'))]
        rw [Kernel.ae_compProd_iff (by measurability)]
        simp only [Fin.snoc_last]
        apply ae_of_all; intro p
        simp only [Kernel.comap_apply]
        exact hstep p.2
      · intro j
        rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.castSucc j))]
        rw [Kernel.ae_compProd_iff (by measurability)]
        simp only [Fin.snoc_castSucc]
        filter_upwards [ih σs j] with p hp
        exact ae_of_all _ (fun _ => hp)
  simp only [trajMeasure]
  rw [MeasureTheory.ae_map_iff measurable_fst.aemeasurable (by measurability)]
  rw [ae_iff]
  change ((trajMeasureAux env alg hr T).toFun ∘ₘ (Measure.dirac alg.σ₀).prod env.μ₀)
      {a | ¬|(a.1 t).2.2| ≤ R_max} = 0
  rw [Measure.bind_apply (by measurability)
      (trajMeasureAux env alg hr T).measurable'.aemeasurable]
  calc ∫⁻ σs : Sig × S,
        (trajMeasureAux env alg hr T σs) {a | ¬|(a.1 t).2.2| ≤ R_max}
      ∂((Measure.dirac alg.σ₀).prod env.μ₀)
      = ∫⁻ _ : Sig × S, 0 ∂((Measure.dirac alg.σ₀).prod env.μ₀) :=
          lintegral_congr (fun σs => by rw [← ae_iff]; exact h_aux T σs t)
    _ = 0 := lintegral_zero

theorem traj_action_ae_eq_actFn
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) [h : AlgIsDeterministic alg]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig] [MeasurableSingletonClass A] [MeasurableEq A]
    (t T : ℕ) (ht : t < T) (hEnv : EnvIsMarkov env) :
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      traj_action t ht ω = h.actFn (summary_at alg t T (Nat.le_of_lt ht) ω) := by
  haveI : IsProbabilityMeasure env.μ₀ := env.hμ₀
  haveI : IsProbabilityMeasure (Measure.dirac alg.σ₀) := inferInstance
  have h_set : MeasurableSet {ω : Fin T → A × O × ℝ |
    traj_action t ht ω = h.actFn (summary_at alg t T (Nat.le_of_lt ht) ω)} := by
    apply measurableSet_eq_fun
    · exact measurable_fst.comp (measurable_pi_apply _)
    · exact h.actFn_meas.comp (summary_at_measurable alg t T (Nat.le_of_lt ht))
  have h_set_not : MeasurableSet {a : ((Fin T → A × O × ℝ) × (Sig × S)) |
    ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)} := by
    exact (h_set.preimage measurable_fst).compl
  simp only [trajMeasure]
  rw [MeasureTheory.ae_map_iff measurable_fst.aemeasurable h_set]
  rw [ae_iff]
  change ((trajMeasureAux env alg hr T).toFun ∘ₘ (Measure.dirac alg.σ₀).prod env.μ₀) {a |
    ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)} = 0
  rw [Measure.bind_apply h_set_not (trajMeasureAux env alg hr T).measurable'.aemeasurable]
  have h_func_meas : Measurable (fun σs : Sig × S => (trajMeasureAux env alg hr T σs) {a | ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)}) := by
    exact Kernel.measurable_coe (trajMeasureAux env alg hr T) h_set_not
  calc ∫⁻ σs : Sig × S, (trajMeasureAux env alg hr T σs) {a |
    ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)} ∂((Measure.dirac alg.σ₀).prod env.μ₀)
    _ = ∫⁻ σ, ∫⁻ s, (trajMeasureAux env alg hr T (σ, s)) {a |
    ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)} ∂env.μ₀ ∂(Measure.dirac alg.σ₀) := by
      apply MeasureTheory.lintegral_prod
      exact h_func_meas.aemeasurable
    _ = ∫⁻ s, (trajMeasureAux env alg hr T (alg.σ₀, s)) {a |
    ¬traj_action t ht a.1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) a.1)} ∂env.μ₀ := by
      simp only [MeasureTheory.lintegral_dirac]
    _ = ∫⁻ s, 0 ∂env.μ₀ := by
      apply lintegral_congr
      intro s
      have h_ae := trajMeasureAux_ae_consistency env alg hr hEnv T s
      rw [← ae_iff]
      filter_upwards [h_ae] with x hx
      change (x.1 ⟨t, ht⟩).1 = h.actFn (summary_at alg t T (Nat.le_of_lt ht) x.1)
      have h_sum_eq : summary_t alg t (fun i => x.1 ⟨i.1, Nat.lt_trans i.2 ht⟩) = summary_at alg t T (Nat.le_of_lt ht) x.1 := rfl
      rw [← h_sum_eq]
      exact hx.2 t ht
    _ = 0 := by rw [lintegral_zero]

theorem summary_at_succ_ae_eq
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) [h : AlgIsDeterministic alg]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig] [MeasurableSingletonClass A] [MeasurableEq A]
    (t T : ℕ) (ht : t + 1 ≤ T) (hEnv : EnvIsMarkov env) :
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      summary_at alg (t + 1) T ht ω =
        h.updateFn
          (summary_at alg t T (Nat.le_of_succ_le ht) ω,
           h.actFn (summary_at alg t T (Nat.le_of_succ_le ht) ω),
           traj_observation t (Nat.lt_of_succ_le ht) ω,
           traj_reward t (Nat.lt_of_succ_le ht) ω) := by
  have h_act_ae := traj_action_ae_eq_actFn env alg hr t T (Nat.lt_of_succ_le ht) hEnv
  filter_upwards [h_act_ae] with ω h_act_eq
  rw [summary_at_succ alg t T ht ω]
  rw [h_act_eq]

-- REWARD CORRECTNESS

lemma oneStepKernel_reward_ae_eq {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (σs : Sig × S) :
    ∀ᵐ step ∂(oneStepKernel env alg hr σs), step.2.2.1 = env.r (σs.2, step.1) := by
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have hmf_step : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {x : A × O × ℝ × Sig × S | x.2.2.1 = env.r (σs.2, x.1)} := by
    apply measurableSet_eq_fun
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact hr.comp (measurable_const.prodMk measurable_fst)
  simp only [oneStepKernel]
  rw [Kernel.map_apply (hf := hmf_step)]
  rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set]
  rw [Kernel.ae_compProd_iff (by measurability)]
  rw [Kernel.ae_compProd_iff (by measurability)]
  rw [Kernel.ae_compProd_iff (by measurability)]
  apply ae_of_all; intro ao
  simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
  exact ae_of_all _ (fun _ => ae_of_all _ (fun _ => trivial))

-- STATE CONSISTENCY

lemma measurable_state_t (env : SixPrimitives.Env S A O) (hD : TransIsDeterministic env) (T : ℕ) (t : ℕ) :
    Measurable (fun ω : Fin T → A × O × ℝ => state_t env hD ω t) := by
  induction t with
  | zero =>
    simp only [state_t_zero]
    exact measurable_const
  | succ t ih =>
    by_cases h : t < T
    · have h_eq : (fun ω : Fin T → A × O × ℝ => state_t env hD ω (t + 1)) =
                  (fun ω => hD.transFn (state_t env hD ω t, (ω ⟨t, h⟩).1)) := by
        ext ω
        rw [state_t]
        rw [dif_pos h]
      rw [h_eq]
      apply Measurable.comp hD.transFn_meas
      apply Measurable.prodMk ih
      exact measurable_fst.comp (measurable_pi_apply (⟨t, h⟩ : Fin T))
    · have h_eq : (fun ω : Fin T → A × O × ℝ => state_t env hD ω (t + 1)) =
                  (fun ω => state_t env hD ω t) := by
        ext ω
        rw [state_t]
        rw [dif_neg h]
      rw [h_eq]
      exact ih

lemma state_t_snoc {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : SixPrimitives.Env S A O) (hD : TransIsDeterministic env)
    {T : ℕ} (ω : Fin T → A × O × ℝ) (x : A × O × ℝ) (t : ℕ) (ht : t ≤ T) :
    state_t env hD (Fin.snoc (α := fun _ => A × O × ℝ) ω x) t = state_t env hD ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht_lt : t < T := Nat.lt_of_succ_le ht
    have ht_lt_succ : t < T + 1 := Nat.lt_succ_of_lt ht_lt
    rw [state_t_succ env hD _ t ht_lt_succ]
    rw [state_t_succ env hD _ t ht_lt]
    rw [ih (Nat.le_of_lt ht_lt)]
    congr 2
    change (Fin.snoc (α := fun _ => A × O × ℝ) ω x (Fin.castSucc ⟨t, ht_lt⟩)).1 = (ω ⟨t, ht_lt⟩).1
    rw [Fin.snoc_castSucc]

lemma oneStepKernel_state_ae_eq {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass S] [MeasurableEq S]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hD : TransIsDeterministic env) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (σs : Sig × S) :
    ∀ᵐ step ∂(oneStepKernel env alg hr σs), step.2.2.2.2 = hD.transFn (σs.2, step.1) := by
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have hmf_step : Measurable (fun p : ((((A × O) × ℝ) × S) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {x : A × O × ℝ × Sig × S | x.2.2.2.2 = hD.transFn (σs.2, x.1)} := by
    apply measurableSet_eq_fun
    · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    · exact hD.transFn_meas.comp (measurable_const.prodMk measurable_fst)
  simp only [oneStepKernel]
  rw [Kernel.map_apply (hf := hmf_step)]
  rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set]
  have hs5 : MeasurableSet {p : ((((A × O) × ℝ) × S) × Sig) | p.1.2 = hD.transFn (σs.2, p.1.1.1.1)} :=
    hmf_step h_set
  rw [Kernel.ae_compProd_iff hs5]
  have hs4_eq : {p : (((A × O) × ℝ) × S) | ∀ᵐ (b : Sig) ∂alg.update.comap (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) (σs, p), p.2 = hD.transFn (σs.2, p.1.1.1)} = {p : (((A × O) × ℝ) × S) | p.2 = hD.transFn (σs.2, p.1.1.1)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_cases hp : p.2 = hD.transFn (σs.2, p.1.1.1)
      · exact hp
      · have h_false : ∀ᵐ (_b : Sig) ∂alg.update.comap (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) (σs, p), False := h.mono (fun _ hb => hp hb)
        rw [ae_iff] at h_false
        have h_set_eq : {a : Sig | ¬False} = Set.univ := by ext; simp
        rw [h_set_eq] at h_false
        have h_meas : IsProbabilityMeasure ((alg.update.comap (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) (σs, p))) := inferInstance
        have h_univ_one := h_meas.measure_univ
        rw [h_univ_one] at h_false
        exact False.elim (one_ne_zero h_false)
    · intro h
      exact ae_of_all _ (fun _ => h)
  have hs4 : MeasurableSet {p : (((A × O) × ℝ) × S) | ∀ᵐ (b : Sig) ∂alg.update.comap (fun x : (Sig × S) × (((A × O) × ℝ) × S) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) (σs, p), p.2 = hD.transFn (σs.2, p.1.1.1)} := by
    rw [hs4_eq]
    apply measurableSet_eq_fun
    · exact measurable_snd
    · exact hD.transFn_meas.comp (measurable_const.prodMk (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  rw [Kernel.ae_compProd_iff hs4]
  apply ae_of_all; intro a
  simp only [Kernel.comap_apply, hD.trans_eq, ae_dirac_eq, Filter.eventually_pure]
  exact ae_of_all _ (fun _ => trivial)

lemma trajMeasureAux_state_ae_eq {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass S] [MeasurableEq S]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hD : TransIsDeterministic env) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (σ₀ : Sig) :
    ∀ᵐ x ∂(trajMeasureAux env alg hr T (σ₀, hD.s₀)), x.2.2 = state_t env hD x.1 T := by
  induction T with
  | zero =>
    simp only [trajMeasureAux, state_t_zero]
    have h_meas : Measurable (fun σs : Sig × S => ((Fin.elim0 : Fin 0 → A × O × ℝ), σs)) :=
      Measurable.prodMk measurable_const measurable_id
    have h_set : MeasurableSet {x : (Fin 0 → A × O × ℝ) × Sig × S | x.2.2 = hD.s₀} := by
      apply measurableSet_eq_fun
      · exact measurable_snd.comp measurable_snd
      · exact measurable_const
    rw [Kernel.map_apply (hf := h_meas), Kernel.id_apply]
    rw [MeasureTheory.ae_map_iff h_meas.aemeasurable h_set]
    have h_set_dirac : MeasurableSet {x : Sig × S | ((Fin.elim0 : Fin 0 → A × O × ℝ), x).2.2 = hD.s₀} := h_meas h_set
    rw [MeasureTheory.ae_dirac_iff h_set_dirac]
  | succ T ih =>
    simp only [trajMeasureAux]
    haveI := oneStepKernel_isMarkov env alg hr hEnv hAlg
    haveI := trajMeasureAux_isMarkov env alg hr hEnv hAlg T
    let f : ((Fin T → A × O × ℝ) × (Sig × S)) × (A × O × ℝ × Sig × S) → (Fin (T + 1) → A × O × ℝ) × (Sig × S) :=
      fun p => (Fin.snoc (α := fun _ => A × O × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2.1, p.2.2.2.2.2)
    have h_f_meas : Measurable f := by
      apply Measurable.prodMk
      · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; fun_prop
        · intro j; simp only [Fin.snoc_castSucc]; fun_prop
      · apply Measurable.prodMk
        · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have h_set : MeasurableSet {x : (Fin (T + 1) → A × O × ℝ) × Sig × S | x.2.2 = state_t env hD x.1 (T + 1)} := by
      apply measurableSet_eq_fun
      · exact measurable_snd.comp measurable_snd
      · exact (measurable_state_t env hD (T + 1) (T + 1)).comp measurable_fst
    rw [Kernel.map_apply (hf := h_f_meas)]
    rw [MeasureTheory.ae_map_iff h_f_meas.aemeasurable h_set]
    refine (Kernel.ae_compProd_iff (h_f_meas h_set)).mpr ?_
    filter_upwards [ih] with a ha
    simp only [Kernel.comap_apply]
    have h_step := oneStepKernel_state_ae_eq env alg hr hD hEnv hAlg a.2
    filter_upwards [h_step] with b hb
    dsimp only [f]
    have ht_lt : T < T + 1 := Nat.lt_succ_self T
    rw [state_t_succ env hD _ T ht_lt]
    have h_last : (⟨T, ht_lt⟩ : Fin (T + 1)) = Fin.last T := rfl
    rw [h_last, Fin.snoc_last]
    rw [state_t_snoc env hD a.1 (b.1, b.2.1, b.2.2.1) T (le_refl T)]
    rw [← ha]
    exact hb

-- FINAL REWARD LEMMA

lemma trajMeasureAux_reward_last {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass S] [MeasurableEq S]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hD : TransIsDeterministic env) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (hT : 0 < T) (σ₀ : Sig) :
    ∀ᵐ x ∂(trajMeasureAux env alg hr T (σ₀, hD.s₀)),
      (x.1 ⟨T - 1, Nat.sub_lt hT one_pos⟩).2.2 =
        env.r (state_t env hD x.1 (T - 1),
               (x.1 ⟨T - 1, Nat.sub_lt hT one_pos⟩).1) := by
  obtain ⟨T', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  change ∀ᵐ x ∂(trajMeasureAux env alg hr (T' + 1) (σ₀, hD.s₀)),
    (x.1 (Fin.last T')).2.2 =
      env.r (state_t env hD x.1 T', (x.1 (Fin.last T')).1)
  haveI h_osk : IsMarkovKernel (oneStepKernel env alg hr) := oneStepKernel_isMarkov env alg hr hEnv hAlg
  haveI hκT : IsMarkovKernel (trajMeasureAux env alg hr T') := trajMeasureAux_isMarkov env alg hr hEnv hAlg T'
  simp only [trajMeasureAux]
  let f : ((Fin T' → A × O × ℝ) × (Sig × S)) × (A × O × ℝ × Sig × S) → (Fin (T' + 1) → A × O × ℝ) × (Sig × S) :=
    fun p => (Fin.snoc (α := fun _ => A × O × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2.1, p.2.2.2.2.2)
  have h_f_meas : Measurable f := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; fun_prop
      · intro j; simp only [Fin.snoc_castSucc]; fun_prop
    · apply Measurable.prodMk
      · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have h_set : MeasurableSet {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S | (x.1 (Fin.last T')).2.2 = env.r (state_t env hD x.1 T', (x.1 (Fin.last T')).1)} := by
    apply measurableSet_eq_fun
    · exact (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply (Fin.last T')).comp measurable_fst)
    · exact hr.comp (Measurable.prodMk
        ((measurable_state_t env hD (T' + 1) T').comp measurable_fst)
        (measurable_fst.comp ((measurable_pi_apply (Fin.last T')).comp measurable_fst)))
  rw [Kernel.map_apply (hf := h_f_meas)]
  rw [MeasureTheory.ae_map_iff h_f_meas.aemeasurable h_set]
  refine (Kernel.ae_compProd_iff (h_f_meas h_set)).mpr ?_
  have h_state_cons := trajMeasureAux_state_ae_eq env alg hr hD hEnv hAlg T' σ₀
  filter_upwards [h_state_cons] with a ha_state
  simp only [Kernel.comap_apply]
  have h_step_rew := oneStepKernel_reward_ae_eq env alg hr hEnv hAlg a.2
  filter_upwards [h_step_rew] with b hb_rew
  dsimp only [f]
  simp only [Fin.snoc_last]
  have h_state_t_prefix := state_t_snoc env hD a.1 (b.1, b.2.1, b.2.2.1) T' (le_refl T')
  rw [h_state_t_prefix, ← ha_state]
  exact hb_rew

lemma trajMeasure_step_reward_eq
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hD : TransIsDeterministic env)
    [MeasurableSingletonClass S] [MeasurableEq S]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T t : ℕ) (ht : t < T) :
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      (ω ⟨t, ht⟩).2.2 = env.r (state_t env hD ω t, (ω ⟨t, ht⟩).1) := by
  haveI : IsProbabilityMeasure env.μ₀ := env.hμ₀
  haveI : IsProbabilityMeasure (Measure.dirac (α := Sig) alg.σ₀) := inferInstance
  have h_aux : ∀ (T' : ℕ) (ht' : t < T'),
      ∀ᵐ x ∂(trajMeasureAux env alg hr T' (alg.σ₀, hD.s₀)),
        (x.1 ⟨t, ht'⟩).2.2 = env.r (state_t env hD x.1 t, (x.1 ⟨t, ht'⟩).1) := by
    intro T'
    induction T' with
    | zero =>
      intro ht'
      exact (Nat.not_lt_zero t ht').elim
    | succ T' ih =>
      intro ht_succ
      haveI h_osk : IsMarkovKernel (oneStepKernel env alg hr) := oneStepKernel_isMarkov env alg hr hEnv hAlg
      haveI hκT : IsMarkovKernel (trajMeasureAux env alg hr T') := trajMeasureAux_isMarkov env alg hr hEnv hAlg T'
      let f : ((Fin T' → A × O × ℝ) × (Sig × S)) × (A × O × ℝ × Sig × S) → (Fin (T' + 1) → A × O × ℝ) × (Sig × S) :=
        fun p => (Fin.snoc (α := fun _ => A × O × ℝ) p.1.1 (p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2.1, p.2.2.2.2.2)
      have h_f_meas : Measurable f := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.snoc_last]; fun_prop
          · intro j; simp only [Fin.snoc_castSucc]; fun_prop
        · apply Measurable.prodMk
          · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
          · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      have h_set : MeasurableSet {x : (Fin (T' + 1) → A × O × ℝ) × Sig × S | (x.1 ⟨t, ht_succ⟩).2.2 = env.r (state_t env hD x.1 t, (x.1 ⟨t, ht_succ⟩).1)} := by
        apply measurableSet_eq_fun
        · exact (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply (⟨t, ht_succ⟩ : Fin (T' + 1))).comp measurable_fst)
        · exact hr.comp (Measurable.prodMk
            ((measurable_state_t env hD (T' + 1) t).comp measurable_fst)
            (measurable_fst.comp ((measurable_pi_apply (⟨t, ht_succ⟩ : Fin (T' + 1))).comp measurable_fst)))
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := h_f_meas)]
      rw [MeasureTheory.ae_map_iff h_f_meas.aemeasurable h_set]
      refine (Kernel.ae_compProd_iff (h_f_meas h_set)).mpr ?_
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht_succ) with ht_lt | rfl
      · filter_upwards [ih ht_lt] with a ha
        simp only [Kernel.comap_apply]
        apply ae_of_all; intro b
        dsimp only [f, Set.mem_setOf_eq]
        have h_cast : (⟨t, ht_succ⟩ : Fin (T' + 1)) = Fin.castSucc (⟨t, ht_lt⟩ : Fin T') := rfl
        rw [h_cast, Fin.snoc_castSucc]
        rw [state_t_snoc env hD a.1 (b.1, b.2.1, b.2.2.1) t (Nat.le_of_lt ht_lt)]
        exact ha
      · have h_state_cons := trajMeasureAux_state_ae_eq env alg hr hD hEnv hAlg t alg.σ₀
        filter_upwards [h_state_cons] with a ha_state
        simp only [Kernel.comap_apply]
        have h_step_rew := oneStepKernel_reward_ae_eq env alg hr hEnv hAlg a.2
        filter_upwards [h_step_rew] with b hb_rew
        dsimp only [f, Set.mem_setOf_eq]
        have h_last : (⟨t, ht_succ⟩ : Fin (t + 1)) = Fin.last t := rfl
        rw [h_last, Fin.snoc_last]
        have h_state_t_prefix := state_t_snoc env hD a.1 (b.1, b.2.1, b.2.2.1) t (le_refl t)
        rw [h_state_t_prefix, ← ha_state]
        exact hb_rew
  simp only [trajMeasure]
  have h_set_traj : MeasurableSet {ω : Trajectory A O T | (ω ⟨t, ht⟩).2.2 = env.r (state_t env hD ω t, (ω ⟨t, ht⟩).1)} := by
    apply measurableSet_eq_fun
    · exact (measurable_snd.comp measurable_snd).comp (measurable_pi_apply (⟨t, ht⟩ : Fin T))
    · exact hr.comp (Measurable.prodMk (measurable_state_t env hD T t) (measurable_fst.comp (measurable_pi_apply (⟨t, ht⟩ : Fin T))))
  have h_set_not : MeasurableSet {a : ((Fin T → A × O × ℝ) × (Sig × S)) | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} := by
    exact (h_set_traj.preimage measurable_fst).compl
  rw [MeasureTheory.ae_map_iff measurable_fst.aemeasurable h_set_traj]
  rw [ae_iff]
  change ((trajMeasureAux env alg hr T).toFun ∘ₘ (Measure.dirac alg.σ₀).prod env.μ₀) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} = 0
  rw [Measure.bind_apply h_set_not (trajMeasureAux env alg hr T).measurable'.aemeasurable]
  have h_func_meas : Measurable (fun σs : Sig × S => (trajMeasureAux env alg hr T σs) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)}) := by
    exact Kernel.measurable_coe (trajMeasureAux env alg hr T) h_set_not
  calc ∫⁻ σs : Sig × S, (trajMeasureAux env alg hr T σs) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} ∂((Measure.dirac alg.σ₀).prod env.μ₀)
    _ = ∫⁻ σ, ∫⁻ s, (trajMeasureAux env alg hr T (σ, s)) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} ∂env.μ₀ ∂(Measure.dirac alg.σ₀) := by
      apply MeasureTheory.lintegral_prod
      exact h_func_meas.aemeasurable
    _ = ∫⁻ s, (trajMeasureAux env alg hr T (alg.σ₀, s)) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} ∂env.μ₀ := by
      simp only [MeasureTheory.lintegral_dirac]
    _ = ∫⁻ s, (trajMeasureAux env alg hr T (alg.σ₀, s)) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} ∂(Measure.dirac hD.s₀) := by
      rw [hD.μ₀_eq]
    _ = (trajMeasureAux env alg hr T (alg.σ₀, hD.s₀)) {a | ¬ (a.1 ⟨t, ht⟩).2.2 = env.r (state_t env hD a.1 t, (a.1 ⟨t, ht⟩).1)} := by
      simp only [MeasureTheory.lintegral_dirac]
    _ = 0 := by
      have h_ae := h_aux T ht
      rw [← ae_iff]
      exact h_ae

lemma trajMeasure_step_reward_eq_unit
    (env : SixPrimitives.Env Unit A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hD : TransIsDeterministic env)
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T t : ℕ) (ht : t < T) :
    ∀ᵐ ω ∂(trajMeasure env alg hr T),
      (ω ⟨t, ht⟩).2.2 = env.r ((), (ω ⟨t, ht⟩).1) := by
  filter_upwards [trajMeasure_step_reward_eq env alg hr hD hEnv hAlg T t ht] with ω hω
  rw [hω]

-- ALG VALUE

noncomputable def algValue'
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (T : ℕ) : ℝ :=
  ∫ traj : Trajectory A O T,
    ∑ t : Fin T, (traj t).2.2
  ∂ trajMeasure env alg hr T

lemma algValue'_eq_sum
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    {R_max : ℝ} (h_bound : ∀ s a, |env.r (s, a)| ≤ R_max) (T : ℕ) :
    algValue' env alg hr T = ∑ t : Fin T,
      ∫ traj : Trajectory A O T, (traj t).2.2 ∂ trajMeasure env alg hr T := by
  unfold algValue'
  rw [MeasureTheory.integral_finsetSum]
  intro t _
  haveI : IsProbabilityMeasure (trajMeasure env alg hr T) :=
    trajMeasure_isProbability env alg hr hEnv hAlg T
  have h_meas : Measurable (fun traj : Trajectory A O T => (traj t).2.2) :=
    measurable_traj_reward t.1 t.2
  apply Integrable.mono (integrable_const R_max) h_meas.aestronglyMeasurable
  filter_upwards [trajMeasure_reward_le env alg hr hEnv hAlg T t R_max h_bound] with traj htraj
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_trans htraj (le_abs_self R_max)

-- ACTION MARGINAL

noncomputable def actionMarginal
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (_hEnv : EnvIsMarkov env) (_hAlg : AlgIsMarkov alg)
    (T : ℕ) (t : Fin T) : Measure A :=
  (trajMeasure env alg hr T).map (fun traj => (traj t).1)

lemma actionMarginal_isProbability
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (t : Fin T) :
    IsProbabilityMeasure (actionMarginal env alg hr hEnv hAlg T t) := by
  simp only [actionMarginal]
  haveI := trajMeasure_isProbability env alg hr hEnv hAlg T
  exact Measure.isProbabilityMeasure_map
    (measurable_fst.comp (measurable_pi_apply t)).aemeasurable

-- KERNEL LINEARITY LEMMAS

section KernelLinearity

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

noncomputable def smulKernel (r : ℝ≥0) (κ : Kernel α β) : Kernel α β where
  toFun a := (r : ℝ≥0∞) • κ a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun a => (r : ℝ≥0∞) * κ a s)
    exact Measurable.const_mul (Kernel.measurable_coe κ hs) (r : ℝ≥0∞)

scoped infixl:73 " •ₖ " => smulKernel

@[simp]
lemma smulKernel_apply (r : ℝ≥0) (κ : Kernel α β) (a : α) :
    (r •ₖ κ) a = (r : ℝ≥0∞) • κ a := rfl

lemma smulKernel_add (r : ℝ≥0) (κ η : Kernel α β) :
    r •ₖ (κ + η) = r •ₖ κ + r •ₖ η := by
  ext a
  have h1 : (r •ₖ (κ + η)) a = (r : ℝ≥0∞) • (κ a + η a) := rfl
  have h2 : (r •ₖ κ + r •ₖ η) a = (r : ℝ≥0∞) • κ a + (r : ℝ≥0∞) • η a := rfl
  rw [h1, h2, smul_add]

lemma smulKernel_zero (κ : Kernel α β) :
    (0 : ℝ≥0) •ₖ κ = 0 := by
  ext a
  have h1 : ((0 : ℝ≥0) •ₖ κ) a = (0 : ℝ≥0∞) • κ a := rfl
  have h2 : (0 : Kernel α β) a = 0 := rfl
  rw [h1, h2, zero_smul]

lemma smulKernel_comap (r : ℝ≥0) (κ : Kernel α β) (f : γ → α) (hf : Measurable f) :
    (r •ₖ κ).comap f hf = r •ₖ (κ.comap f hf) := by
  ext a
  simp [smulKernel_apply, Kernel.comap_apply]

lemma add_comap (κ η : Kernel α β) (f : γ → α) (hf : Measurable f) :
    (κ + η).comap f hf = κ.comap f hf + η.comap f hf := by
  ext a
  simp [Kernel.comap_apply]

lemma smulKernel_compProd_left (r : ℝ≥0) (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel (r •ₖ κ)] [IsSFiniteKernel η] :
    (r •ₖ κ).compProd η = r •ₖ (κ.compProd η) := by
  ext a s hs
  change ((r •ₖ κ).compProd η a) s = (r : ℝ≥0∞) * (κ.compProd η a s)
  have hL := Kernel.compProd_apply hs (r •ₖ κ) η a
  have hR := Kernel.compProd_apply hs κ η a
  rw [hL, hR]
  have h_smul : (r •ₖ κ) a = (r : ℝ≥0∞) • κ a := rfl
  rw [h_smul, lintegral_smul_measure, smul_eq_mul]

lemma add_compProd_left (κ₁ κ₂ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel (κ₁ + κ₂)] [IsSFiniteKernel η] :
    (κ₁ + κ₂).compProd η = κ₁.compProd η + κ₂.compProd η := by
  ext a s hs
  change ((κ₁ + κ₂).compProd η a) s = κ₁.compProd η a s + κ₂.compProd η a s
  have hL := Kernel.compProd_apply hs (κ₁ + κ₂) η a
  have hR1 := Kernel.compProd_apply hs κ₁ η a
  have hR2 := Kernel.compProd_apply hs κ₂ η a
  rw [hL, hR1, hR2]
  have h_add : (κ₁ + κ₂) a = κ₁ a + κ₂ a := rfl
  rw [h_add, lintegral_add_measure]

lemma smulKernel_map (r : ℝ≥0) (κ : Kernel α β) (f : β → γ) (hf : Measurable f) :
    (r •ₖ κ).map f = r •ₖ (κ.map f) := by
  ext a s hs
  change ((r •ₖ κ).map f a) s = (r : ℝ≥0∞) * (κ.map f a s)
  rw [Kernel.map_apply _ hf a, Kernel.map_apply _ hf a]
  change Measure.map f ((r : ℝ≥0∞) • κ a) s = (r : ℝ≥0∞) * Measure.map f (κ a) s
  rw [Measure.map_smul]
  rfl

lemma bind_smulKernel (μ : Measure α) (r : ℝ≥0) (κ : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel (r •ₖ κ)] :
    μ.bind (r •ₖ κ) = (r : ℝ≥0∞) • μ.bind κ := by
  ext s hs
  change (μ.bind (r •ₖ κ)) s = (r : ℝ≥0∞) * (μ.bind κ s)
  have hL := @Measure.bind_apply α β _ _ μ (r •ₖ κ) s hs (Kernel.measurable (r •ₖ κ)).aemeasurable
  have hR := @Measure.bind_apply α β _ _ μ κ s hs (Kernel.measurable κ).aemeasurable
  rw [hL, hR]
  have h_integrand : (fun a => ((r •ₖ κ) a) s) = (fun a => (r : ℝ≥0∞) * (κ a) s) := by
    ext a
    rfl
  rw [h_integrand]
  exact lintegral_const_mul (r : ℝ≥0∞) (Kernel.measurable_coe κ hs)

end KernelLinearity

-- TRAJECTORY MEASURE TRUNCATION

lemma trajMeasure_truncation_one
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (E : Set (Trajectory A O T)) (hE : MeasurableSet E) :
    (trajMeasure env alg hr (T + 1))
      {traj : Trajectory A O (T + 1) | (fun i : Fin T => traj (Fin.castSucc i)) ∈ E} =
    (trajMeasure env alg hr T) E := by
  have h_cast_meas : Measurable (fun (traj : Trajectory A O (T + 1)) (i : Fin T) => traj (Fin.castSucc i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have h_set_T1 : MeasurableSet {traj : Trajectory A O (T + 1) | (fun i => traj (Fin.castSucc i)) ∈ E} :=
    h_cast_meas hE
  have hs_T1 : MeasurableSet (Prod.fst ⁻¹' {traj : Trajectory A O (T + 1) | (fun i => traj (Fin.castSucc i)) ∈ E} : Set (((Fin (T + 1) → A × O × ℝ) × (Sig × S)))) :=
    measurable_fst h_set_T1
  have hs_T : MeasurableSet (Prod.fst ⁻¹' E : Set (((Fin T → A × O × ℝ) × (Sig × S)))) :=
    measurable_fst hE
  simp only [trajMeasure]
  rw [Measure.map_apply measurable_fst h_set_T1]
  rw [Measure.map_apply measurable_fst hE]
  erw [Measure.bind_apply hs_T1 (trajMeasureAux env alg hr (T + 1)).measurable'.aemeasurable]
  erw [Measure.bind_apply hs_T (trajMeasureAux env alg hr T).measurable'.aemeasurable]
  apply lintegral_congr
  intro σs
  simp only [trajMeasureAux]
  let k_upd : Kernel ((Sig × S) × ((Fin T → A × O × ℝ) × (Sig × S))) (A × O × ℝ × Sig × S) :=
    (oneStepKernel env alg hr).comap
      (fun x => x.2.2)
      (measurable_snd.comp measurable_snd)
  haveI h_osk : IsMarkovKernel (oneStepKernel env alg hr) := oneStepKernel_isMarkov env alg hr hEnv hAlg
  haveI h_comap : IsMarkovKernel k_upd := Kernel.IsMarkovKernel.comap _ _
  let f : ((Fin T → A × O × ℝ) × (Sig × S)) × (A × O × ℝ × Sig × S) → (Fin (T + 1) → A × O × ℝ) × (Sig × S) :=
    fun x => (Fin.snoc x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), (x.2.2.2.2.1, x.2.2.2.2.2))
  have h_f_meas : Measurable f := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; fun_prop
      · intro j; simp only [Fin.snoc_castSucc]; fun_prop
    · apply Measurable.prodMk
      · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  change ⇑(Kernel.map _ f) σs _ = _
  rw [Kernel.map_apply (hf := h_f_meas)]
  rw [Measure.map_apply h_f_meas hs_T1]
  have h_f_pre : f ⁻¹' (Prod.fst ⁻¹' {p : Trajectory A O (T + 1) | (fun i => p (Fin.castSucc i)) ∈ E}) =
                 Prod.fst ⁻¹' (Prod.fst ⁻¹' E) := by
    ext x
    simp only [f, Set.mem_preimage, Set.mem_setOf_eq, Fin.snoc_castSucc]
  rw [h_f_pre]
  haveI : IsMarkovKernel (trajMeasureAux env alg hr T) :=
    trajMeasureAux_isMarkov env alg hr hEnv hAlg T
  have h_prod_meas : MeasurableSet (Prod.fst ⁻¹' (Prod.fst ⁻¹' E) : Set (((Fin T → A × O × ℝ) × Sig × S) × A × O × ℝ × Sig × S)) :=
    measurable_fst hs_T
  rw [Kernel.compProd_apply h_prod_meas]
  have h_integrate_one : (fun a : (Fin T → A × O × ℝ) × (Sig × S) =>
    k_upd (σs, a) (@Prod.mk ((Fin T → A × O × ℝ) × (Sig × S)) (A × O × ℝ × Sig × S) a ⁻¹' Prod.fst ⁻¹' Prod.fst ⁻¹' E)) =
    (Prod.fst ⁻¹' E : Set ((Fin T → A × O × ℝ) × (Sig × S))).indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext a
    by_cases ha : a.1 ∈ E
    · have ha_pre : a ∈ Prod.fst ⁻¹' E := ha
      have h_set_univ : @Prod.mk ((Fin T → A × O × ℝ) × (Sig × S)) (A × O × ℝ × Sig × S) a ⁻¹' Prod.fst ⁻¹' Prod.fst ⁻¹' E = (Set.univ : Set (A × O × ℝ × Sig × S)) := by
        ext x; simp only [Set.mem_preimage, Set.mem_univ, iff_true]; exact ha
      rw [h_set_univ]
      rw [Set.indicator_of_mem ha_pre]
      exact measure_univ
    · have ha_pre : a ∉ Prod.fst ⁻¹' E := ha
      have h_set_empty : @Prod.mk ((Fin T → A × O × ℝ) × (Sig × S)) (A × O × ℝ × Sig × S) a ⁻¹' Prod.fst ⁻¹' Prod.fst ⁻¹' E = (∅ : Set (A × O × ℝ × Sig × S)) := by
        ext x; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]; exact ha
      rw [h_set_empty]
      simp [ha_pre, measure_empty]
  rw [h_integrate_one]
  rw [lintegral_indicator_const hs_T]
  exact one_mul _

lemma trajMeasure_truncation
    (env : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T t : ℕ) (ht : t ≤ T) (E : Set (Trajectory A O t)) (hE : MeasurableSet E) :
    (trajMeasure env alg hr T)
      {traj : Trajectory A O T | (fun i : Fin t => traj (Fin.castLE ht i)) ∈ E} =
    (trajMeasure env alg hr t) E := by
  induction T, ht using Nat.le_induction with
  | base =>
    congr 1
  | succ T' h_le ih =>
    have h_cast_meas : Measurable (fun (traj' : Trajectory A O T') (i : Fin t) => traj' (Fin.castLE h_le i)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have h_meas_T' : MeasurableSet {traj' : Trajectory A O T' | (fun i : Fin t => traj' (Fin.castLE h_le i)) ∈ E} :=
      h_cast_meas hE
    have h_inner_eq : {traj : Trajectory A O (T' + 1) | (fun i : Fin t => traj (Fin.castLE (Nat.le_succ_of_le h_le) i)) ∈ E} =
      {traj : Trajectory A O (T' + 1) | (fun (i : Fin T') => traj (Fin.castSucc i)) ∈ {traj' : Trajectory A O T' | (fun i : Fin t => traj' (Fin.castLE h_le i)) ∈ E}} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have h_fun_eq : (fun i : Fin t => ω (Fin.castLE (Nat.le_succ_of_le h_le) i)) = (fun i : Fin t => ω (Fin.castSucc (Fin.castLE h_le i))) := by
        funext i
        rfl
      rw [h_fun_eq]
    rw [h_inner_eq]
    rw [trajMeasure_truncation_one env alg hr hEnv hAlg T' _ h_meas_T']
    exact ih

lemma trajMeasure_congr
    (env₁ env₂ : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hr₁ : Measurable env₁.r) (hr₂ : Measurable env₂.r)
    (h_trans : env₁.trans = env₂.trans) (h_obs : env₁.obs = env₂.obs)
    (h_r : ∀ s a, env₁.r (s, a) = env₂.r (s, a))
    (h_μ₀ : env₁.μ₀ = env₂.μ₀) (T : ℕ) :
    trajMeasure env₁ alg hr₁ T = trajMeasure env₂ alg hr₂ T := by
  have h_env_eq : env₁ = env₂ := by
    obtain ⟨t₁, o₁, r₁, hr₁, m₁, hm₁⟩ := env₁
    obtain ⟨t₂, o₂, r₂, hr₂, m₂, hm₂⟩ := env₂
    have h_r_eq : r₁ = r₂ := by
      ext ⟨s, a⟩
      exact h_r s a
    subst h_trans
    subst h_obs
    subst h_r_eq
    subst h_μ₀
    rfl
  subst h_env_eq
  rfl

-- HELPER LEMMAS

noncomputable def measureEntropy {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) : ℝ :=
  -∑ a : α, let p := (μ {a}).toReal; p * Real.log p

lemma entropy_mixture_ge {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε * measureEntropy ν ≤
      measureEntropy ((1 - ENNReal.ofReal ε) • μ + ENNReal.ofReal ε • ν) := by
  rcases eq_or_lt_of_le hε0 with rfl | hε0_strict
  · rw [ENNReal.ofReal_zero, tsub_zero, one_smul, zero_smul, add_zero, zero_mul]
    unfold measureEntropy
    rw [neg_nonneg]
    apply Finset.sum_nonpos
    intro x _
    have hp0 : 0 ≤ (μ {x}).toReal := ENNReal.toReal_nonneg
    have h_le : μ {x} ≤ 1 := prob_le_one
    have hp1 : (μ {x}).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top h_le
    exact mul_nonpos_of_nonneg_of_nonpos hp0 (Real.log_nonpos hp0 hp1)
  · rcases eq_or_lt_of_le hε1 with rfl | hε1_strict
    · rw [ENNReal.ofReal_one, tsub_self, zero_smul, one_smul, zero_add, one_mul]
    · unfold measureEntropy
      rw [mul_neg, Finset.mul_sum]
      apply neg_le_neg
      apply Finset.sum_le_sum
      intro a _ha
      let p_mu := (μ {a}).toReal
      let p_nu := (ν {a}).toReal
      let p_mix := (((1 - ENNReal.ofReal ε) • μ + ENNReal.ofReal ε • ν : Measure α) {a}).toReal
      have h_mix_eq : p_mix = (1 - ε) * p_mu + ε * p_nu := by
        dsimp only [p_mix, p_mu, p_nu]
        rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
        change ((1 - ENNReal.ofReal ε) * μ {a} + ENNReal.ofReal ε * ν {a}).toReal = _
        have h_fin1 : (1 - ENNReal.ofReal ε) * μ {a} ≠ ⊤ := by
          apply ENNReal.mul_ne_top
          · exact ENNReal.sub_ne_top ENNReal.one_ne_top
          · exact measure_ne_top μ {a}
        have h_fin2 : ENNReal.ofReal ε * ν {a} ≠ ⊤ := by
          apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · exact measure_ne_top ν {a}
        rw [ENNReal.toReal_add h_fin1 h_fin2, ENNReal.toReal_mul, ENNReal.toReal_mul]
        have h_eps_toReal : (ENNReal.ofReal ε).toReal = ε := ENNReal.toReal_ofReal hε0
        have h_sub_toReal : (1 - ENNReal.ofReal ε).toReal = 1 - ε := by
          have h_le : ENNReal.ofReal ε ≤ 1 := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hε1
          rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top, ENNReal.toReal_one, h_eps_toReal]
        rw [h_sub_toReal, h_eps_toReal]
      have hb1 : 0 < ε := hε0_strict
      have hb2 : 0 < 1 - ε := sub_pos.mpr hε1_strict
      have ha1 : 0 ≤ ε * p_nu := mul_nonneg hb1.le ENNReal.toReal_nonneg
      have ha2 : 0 ≤ (1 - ε) * p_mu := mul_nonneg hb2.le ENNReal.toReal_nonneg
      have hLSI := Phase1.log_sum_inequality (a₁ := ε * p_nu) (a₂ := (1 - ε) * p_mu) (b₁ := ε) (b₂ := 1 - ε) ha1 ha2 hb1 hb2
      have h_a1_div : ε * p_nu / ε = p_nu := mul_div_cancel_left₀ p_nu hb1.ne'
      have h_a2_div : (1 - ε) * p_mu / (1 - ε) = p_mu := mul_div_cancel_left₀ p_mu hb2.ne'
      have h_b_sum : ε + (1 - ε) = 1 := by ring
      have h_a_sum : ε * p_nu + (1 - ε) * p_mu = p_mix := by rw [h_mix_eq]; ring
      rw [h_a1_div, h_a2_div, h_b_sum, div_one, h_a_sum] at hLSI
      have hp_mu_le1 : p_mu ≤ 1 := by
        have h_le : μ {a} ≤ 1 := prob_le_one
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top h_le
      have h_log_mu : Real.log p_mu ≤ 0 := Real.log_nonpos ENNReal.toReal_nonneg hp_mu_le1
      have h_term_nonpos : (1 - ε) * p_mu * Real.log p_mu ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha2 h_log_mu
      have h_expand : ε * (p_nu * Real.log p_nu) = ε * p_nu * Real.log p_nu := by ring
      linarith

lemma uniform_entropy_eq_log {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : ℕ) (hn : n = Fintype.card α)
    (μ_unif : Measure α) [IsProbabilityMeasure μ_unif]
    (h_unif : ∀ a : α, μ_unif {a} = 1 / n) :
    measureEntropy μ_unif = Real.log n := by
  unfold measureEntropy
  have hp : ∀ a : α, (μ_unif {a}).toReal = 1 / (n : ℝ) := by
    intro a
    rw [h_unif a]
    simp
  have h_sum : (∑ a : α, (μ_unif {a}).toReal * Real.log (μ_unif {a}).toReal) =
    ∑ _a : α, (1 / (n : ℝ)) * Real.log (1 / (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hp a]
  rw [h_sum, Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
  have hn_ne_zero : (n : ℝ) ≠ 0 := by
    intro h_zero
    have h_n_zero : n = 0 := by exact_mod_cast h_zero
    have h_empty : IsEmpty α := Fintype.card_eq_zero_iff.mp (by rw [← hn, h_n_zero])
    have h_univ : (Set.univ : Set α) = ∅ := Set.univ_eq_empty_iff.mpr h_empty
    have h_prob := measure_univ (μ := μ_unif)
    rw [h_univ, measure_empty] at h_prob
    exact zero_ne_one h_prob
  rw [one_div, Real.log_inv]
  have h_cancel : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn_ne_zero
  rw [← mul_assoc, h_cancel, one_mul, neg_neg]

-- SEQUENCE DEFINITIONS

noncomputable def dangerProbSeq
    (env : Env S A O) (alg : Algorithm A O Sig) (hr : Measurable env.r)
    (aDanger : S → A) (k : ℕ) : ℝ :=
  ((trajMeasure env alg hr (k + 1))
    {traj : Fin (k + 1) → A × O × ℝ |
      (traj ⟨k, Nat.lt_succ_self k⟩).1 ∈ Set.range aDanger}).toReal

noncomputable def infeasProbSeq
    (env : Env S A O) (alg : Algorithm A O Sig) (hr : Measurable env.r)
    (F : Set A) (t : ℕ) : ℝ :=
  ((trajMeasure env alg hr (t + 1))
    {traj : Fin (t + 1) → A × O × ℝ |
      (traj ⟨t, Nat.lt_succ_self t⟩).1 ∈ F}).toReal

noncomputable def bridgeCumSeq
    (env : Env S A O) (alg : Algorithm A O Sig) (hr : Measurable env.r)
    (aBridge : A) (T : ℕ) : ℝ :=
  ∑ t : Fin T,
    ((trajMeasure env alg hr T)
      {traj : Fin T → A × O × ℝ | (traj t).1 = aBridge}).toReal

noncomputable def condEntSeq
    (env : Env S A O) (alg : Algorithm A O Sig) (hr : Measurable env.r)
    (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    [Fintype A] [MeasurableSingletonClass A] (t : ℕ) : ℝ :=
  measureEntropy (actionMarginal env alg hr hEnv hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩)

noncomputable def staleProbSeq
    (env : Env S A O) (alg : Algorithm A O Sig) (hr : Measurable env.r)
    (aStale : A) (t : ℕ) : ℝ :=
  ((trajMeasure env alg hr (t + 1))
    {traj : Fin (t + 1) → A × O × ℝ |
      (traj ⟨t, Nat.lt_succ_self t⟩).1 = aStale}).toReal

-- BERNOULLI OBSERVATION KERNEL

noncomputable def bernoulliMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli ⟨p, hp0⟩ (show (⟨p, hp0⟩ : ℝ≥0) ≤ 1 from by exact_mod_cast hp1)).toMeasure

lemma bernoulliMeasure_isProbability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p hp0 hp1) :=
  PMF.toMeasure.isProbabilityMeasure _

lemma bernoulliMeasure_mean (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ b : Bool, (if b then 1 else 0 : ℝ) ∂bernoulliMeasure p hp0 hp1 = p := by
  simp only [bernoulliMeasure]
  set pmf := PMF.bernoulli ⟨p, hp0⟩ (show (⟨p, hp0⟩ : ℝ≥0) ≤ 1 from by exact_mod_cast hp1)
  have hf : Integrable (fun b : Bool => if b then (1 : ℝ) else 0) pmf.toMeasure := by
    apply Integrable.mono (integrable_const (1 : ℝ))
    · exact (measurable_of_finite _).aestronglyMeasurable
    · filter_upwards with b
      fin_cases b <;> simp [norm_one, norm_zero]
  rw [PMF.integral_eq_tsum _ _ hf, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, smul_eq_mul, mul_zero, zero_add, mul_one]
  simp only [pmf, PMF.bernoulli_apply]
  norm_cast

end SixPrimitives.Phase2

-- VISIT FREQUENCY AT LEAST

namespace SixPrimitives

noncomputable def VisitFrequencyAtLeast_concrete {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass S]           -- ← reviewer fix
    (env : Env S A O) (s_star : S) (ν : ℝ) : Prop :=
  ∃ (Sig : Type) (_mSig : MeasurableSpace Sig) (_tSig : TopologicalSpace Sig) (_bSig : BorelSpace Sig)
    (alg : Algorithm A O Sig)
    (_hEnv : Phase2.EnvIsMarkov env)
    (_hAlg : Phase2.AlgIsMarkov alg),
    ∀ (T : ℕ), 0 < T →
      (T : ℝ) * ν ≤ Phase2.expectedVisits env alg env.hr_meas T s_star

noncomputable def VisitFrequencyAtLeast {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass S]
    (env : Env S A O) (s_star : S) (ν : ℝ) : Prop :=
  VisitFrequencyAtLeast_concrete env s_star ν

theorem VisitFrequencyAtLeast_eq {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass S]
    (env : Env S A O) (s_star : S) (ν : ℝ) :
    VisitFrequencyAtLeast env s_star ν ↔ VisitFrequencyAtLeast_concrete env s_star ν :=
  Iff.rfl

lemma visitFrequencyAtLeast_of_unique_state {A O : Type*}
    [MeasurableSpace A] [MeasurableSpace O] [Nonempty A]
    (env : Env Unit A O) (hD : Phase2.EnvIsDeterministic env) (ν : ℝ) (hν : ν ≤ 1) :
    VisitFrequencyAtLeast env () ν := by
  let a₀ : A := Classical.arbitrary A
  let algWit : Algorithm A O Unit := {
    σ₀     := ()
    act    := Kernel.const _ (Measure.dirac a₀)
    update := Kernel.const _ (Measure.dirac ()) }
  have hEnv : Phase2.EnvIsMarkov env  := Phase2.envIsDeterministic_isMarkov env hD
  have hAlg : Phase2.AlgIsMarkov algWit := {
    act_markov    := inferInstance
    update_markov := inferInstance }
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, algWit, hEnv, hAlg,
    fun T _hT => by
      have hEq : Phase2.expectedVisits env algWit env.hr_meas T () = T :=
        Phase2.expectedVisits_unit_state env algWit env.hr_meas hEnv hAlg T
      rw [hEq]
      calc (T : ℝ) * ν
          ≤ (T : ℝ) * 1 := mul_le_mul_of_nonneg_left hν (Nat.cast_nonneg T)
        _ = T             := mul_one _ ⟩

end SixPrimitives

-- REGRET DEFINITIONS  (SixPrimitives namespace)

namespace SixPrimitives

noncomputable def algValue {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : Env S A O) (alg : Algorithm A O Sig) (T : ℕ) : ℝ :=
  Phase2.algValue' env alg env.hr_meas T

noncomputable def optValue {S A O : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    (env : Env S A O) (T : ℕ) : ℝ :=
  sSup { v : ℝ | ∃ (Sig : Type)
                    (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig)
                    (alg : Algorithm A O Sig)
                    (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update),
                  v = Phase2.algValue' env alg env.hr_meas T }

noncomputable def regret {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : Env S A O) (alg : Algorithm A O Sig) (T : ℕ) : ℝ :=
  optValue env T - algValue env alg T

def SublinearRegret {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : Env S A O) (alg : Algorithm A O Sig) : Prop :=
  ∀ ε > 0, ∀ᶠ T : ℕ in Filter.atTop, regret env alg T ≤ ε * T

def LinearRegret {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : Env S A O) (alg : Algorithm A O Sig) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ,
    ∀ᶠ T : ℕ in Filter.atTop, c * (T - t₀) ≤ regret env alg T

end SixPrimitives

namespace SixPrimitives.Phase2

@[simp] lemma algValue_eq_algValue' {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig) (T : ℕ) :
    SixPrimitives.algValue env alg T = algValue' env alg env.hr_meas T := rfl

lemma algValue'_le_const {S A O Sig : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hr : Measurable env.r) (hEnv : EnvIsMarkov env) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (R_max : ℝ) (h_bound : ∀ s a, |env.r (s, a)| ≤ R_max) :
    algValue' env alg hr T ≤ T * R_max := by
  unfold algValue'
  haveI : IsProbabilityMeasure (trajMeasure env alg hr T) :=
    trajMeasure_isProbability env alg hr hEnv hAlg T
  have h_each : ∀ t : Fin T, ∀ᵐ traj ∂(trajMeasure env alg hr T), |(traj t).2.2| ≤ R_max :=
    fun t => trajMeasure_reward_le env alg hr hEnv hAlg T t R_max h_bound
  have hle_ae : ∀ᵐ traj ∂(trajMeasure env alg hr T),
      ∑ t : Fin T, (traj t).2.2 ≤ T * R_max := by
    filter_upwards [ae_all_iff.mpr h_each] with traj h_all
    calc ∑ t : Fin T, (traj t).2.2
        ≤ ∑ t : Fin T, |(traj t).2.2| := Finset.sum_le_sum (fun t _ => le_abs_self _)
      _ ≤ ∑ _t : Fin T, R_max := Finset.sum_le_sum (fun t _ => h_all t)
      _ = (T : ℝ) * R_max := by simp
  have hint : Integrable (fun traj : Trajectory A O T => ∑ t : Fin T, (traj t).2.2) (trajMeasure env alg hr T) := by
    have h_sum_meas : Measurable (fun traj : Trajectory A O T => ∑ t : Fin T, (traj t).2.2) :=
      Finset.measurable_sum _ (fun t _ => measurable_traj_reward t t.isLt)
    apply Integrable.mono (integrable_const (T * R_max)) h_sum_meas.aestronglyMeasurable
    filter_upwards [ae_all_iff.mpr h_each] with traj h_all
    calc ‖∑ t : Fin T, (traj t).2.2‖
      _ ≤ ∑ t : Fin T, ‖(traj t).2.2‖ := norm_sum_le _ _
      _ ≤ ∑ t : Fin T, R_max := Finset.sum_le_sum (fun t _ => by
          rw [Real.norm_eq_abs]
          exact h_all t)
      _ = (T : ℝ) * R_max := by simp
      _ ≤ ‖(T : ℝ) * R_max‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  calc ∫ traj, ∑ t : Fin T, (traj t).2.2 ∂trajMeasure env alg hr T
      ≤ ∫ _traj, (T : ℝ) * R_max ∂trajMeasure env alg hr T :=
        integral_mono_ae hint (integrable_const _) hle_ae
    _ = T * R_max := by simp

lemma regret_nonneg {S A O : Type*} {Sig : Type}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (env : SixPrimitives.Env S A O) (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv : EnvIsMarkov env)
    [IsMarkovKernel alg.act] [IsMarkovKernel alg.update] (T : ℕ)
    (h_r_le : ∀ s a, |env.r (s, a)| ≤ 1) :
    0 ≤ SixPrimitives.regret env alg T := by
  unfold SixPrimitives.regret SixPrimitives.optValue SixPrimitives.algValue
  apply sub_nonneg.mpr
  apply le_csSup
  · refine ⟨T * 1, fun v hv => ?_⟩
    obtain ⟨Sig', _, _, _, alg', h_act', h_upd', rfl⟩ := hv
    exact algValue'_le_const env alg' env.hr_meas hEnv
      { act_markov := h_act', update_markov := h_upd' } T 1 h_r_le
  · exact ⟨Sig, inferInstance, inferInstance, inferInstance,
           alg, inferInstance, inferInstance, rfl⟩

-- ENVIRONMENT E₁

section EnvX1

structure BanditParam where
  Δ   : ℝ
  hΔ0 : 0 < Δ
  hΔ1 : Δ < 1/2

noncomputable def env₁_0 (bp : BanditParam) : SixPrimitives.Env Unit (Fin 2) Bool where
  trans   := Kernel.const _ (Measure.dirac ())
  obs     := { toFun := fun (_, a) =>
                 if a = (0 : Fin 2)
                 then bernoulliMeasure (1/2 + bp.Δ) (by linarith [bp.hΔ0]) (by linarith [bp.hΔ1])
                 else bernoulliMeasure (1/2 - bp.Δ) (by linarith [bp.hΔ1]) (by linarith [bp.hΔ0])
               measurable' := measurable_of_finite _ }
  r       := fun (_, a) => if a = 0 then 1/2 + bp.Δ else 1/2 - bp.Δ
  hr_meas := measurable_of_finite _
  μ₀      := Measure.dirac ()
  hμ₀     := inferInstance

noncomputable def env₁_1 (bp : BanditParam) : SixPrimitives.Env Unit (Fin 2) Bool where
  trans   := Kernel.const _ (Measure.dirac ())
  obs     := { toFun := fun (_, a) =>
                 if a = (0 : Fin 2)
                 then bernoulliMeasure (1/2 - bp.Δ) (by linarith [bp.hΔ1]) (by linarith [bp.hΔ0])
                 else bernoulliMeasure (1/2 + bp.Δ) (by linarith [bp.hΔ0]) (by linarith [bp.hΔ1])
               measurable' := measurable_of_finite _ }
  r       := fun (_, a) => if a = 0 then 1/2 - bp.Δ else 1/2 + bp.Δ
  hr_meas := measurable_of_finite _
  μ₀      := Measure.dirac ()
  hμ₀     := inferInstance

theorem env₁_0_hasP₁ (bp : BanditParam) : SixPrimitives.HasP₁ (env₁_0 bp) (env₁_1 bp) := by
  refine ⟨(), 0, 1, by decide, ?_, ?_⟩
  · intro a
    fin_cases a <;> simp [env₁_0]
    linarith [bp.hΔ0]
  · intro a
    fin_cases a <;> simp [env₁_1]
    linarith [bp.hΔ0]

theorem env₁_0_inClassC (bp : BanditParam) : SixPrimitives.InClassC (env₁_0 bp) SixPrimitives.VisitFrequencyAtLeast :=
  Or.inl ⟨env₁_1 bp, env₁_0_hasP₁ bp⟩

instance env₁_0_isMarkov (bp : BanditParam) : EnvIsMarkov (env₁_0 bp) where
  trans_markov := ⟨fun _ => by dsimp [env₁_0]; infer_instance⟩
  obs_markov := ⟨fun ⟨_, a⟩ => by
    change IsProbabilityMeasure (if a = 0 then _ else _)
    split_ifs
    · exact bernoulliMeasure_isProbability _ _ _
    · exact bernoulliMeasure_isProbability _ _ _⟩

instance env₁_1_isMarkov (bp : BanditParam) : EnvIsMarkov (env₁_1 bp) where
  trans_markov := ⟨fun _ => by dsimp [env₁_1]; infer_instance⟩
  obs_markov := ⟨fun ⟨_, a⟩ => by
    change IsProbabilityMeasure (if a = 0 then _ else _)
    split_ifs
    · exact bernoulliMeasure_isProbability _ _ _
    · exact bernoulliMeasure_isProbability _ _ _⟩

noncomputable def env₁_optAlg (_bp : BanditParam) : SixPrimitives.Algorithm (Fin 2) Bool Unit where
  act := Kernel.const _ (Measure.dirac 0)
  update := Kernel.const _ (Measure.dirac ())
  σ₀ := ()

instance env₁_optAlg_isDet (_bp : BanditParam) : AlgIsDeterministic (env₁_optAlg _bp) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

noncomputable def env₁_0_transDet (bp : BanditParam) : TransIsDeterministic (env₁_0 bp) where
  s₀ := ()
  μ₀_eq := rfl
  transFn := fun _ => ()
  transFn_meas := measurable_const
  trans_eq := fun _ => rfl

lemma env₁_optValue (bp : BanditParam) (T : ℕ) :
    SixPrimitives.optValue (env₁_0 bp) T = (1/2 + bp.Δ) * T := by
  have hEnv := env₁_0_isMarkov bp
  have hAlg := algIsDeterministic_isMarkov (env₁_optAlg bp)
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' (env₁_0 bp) alg (env₁_0 bp).hr_meas T} → v ≤ (1 / 2 + bp.Δ) * (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Unit) (a : Fin 2), |(env₁_0 bp).r (s, a)| ≤ 1 / 2 + bp.Δ := by
      intro s a
      change |if a = 0 then 1/2 + bp.Δ else 1/2 - bp.Δ| ≤ 1/2 + bp.Δ
      split_ifs
      · rw [abs_of_pos (by linarith [bp.hΔ0])]
      · rw [abs_of_pos (by linarith [bp.hΔ1])]
        linarith [bp.hΔ0]
    have h_val := algValue'_le_const (env₁_0 bp) alg (env₁_0 bp).hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T (1 / 2 + bp.Δ) h_rew_bound
    rw [mul_comm] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T
      use Unit, inferInstance, inferInstance, inferInstance, env₁_optAlg bp, hAlg.act_markov, hAlg.update_markov
    · exact h_bound
  · apply le_csSup
    · use (1 / 2 + bp.Δ) * T; exact h_bound
    · use Unit, inferInstance, inferInstance, inferInstance, env₁_optAlg bp, hAlg.act_markov, hAlg.update_markov
      symm
      dsimp [Phase2.algValue']
      have hTransDet := env₁_0_transDet bp
      have h_eq_unit : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T),
          (ω t).2.2 = (env₁_0 bp).r ((), (ω t).1) :=
        fun t => trajMeasure_step_reward_eq_unit (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas hTransDet hEnv hAlg T t.1 t.2
      have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T),
          (ω t).1 = 0 := by
        intro t
        filter_upwards [traj_action_ae_eq_actFn (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas t.1 T t.2 hEnv] with ω hω
        exact hω
      have h_all : ∀ᵐ ω ∂(trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1/2 + bp.Δ := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_unit t, h_act t] with ω h_unit h_act_eq
        simp only [h_unit, h_act_eq, env₁_0, ite_true]
      have h_rew : ∀ᵐ traj ∂(trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) * (1/2 + bp.Δ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1/2 + bp.Δ : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) * (1/2 + bp.Δ) := by
            simp
            ring
      haveI : IsProbabilityMeasure (trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T) :=
        trajMeasure_isProbability (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas hEnv hAlg T
      have h_int_eq : ∫ (traj : Trajectory (Fin 2) Bool T), ∑ t : Fin T, (traj t).2.2 ∂trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T = ∫ (traj : Trajectory (Fin 2) Bool T), (T : ℝ) * (1/2 + bp.Δ) ∂trajMeasure (env₁_0 bp) (env₁_optAlg bp) (env₁_0 bp).hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp [mul_comm]

noncomputable def env₁_1_optAlg (_bp : BanditParam) : SixPrimitives.Algorithm (Fin 2) Bool Unit where
  act    := Kernel.const _ (Measure.dirac 1)
  update := Kernel.const _ (Measure.dirac ())
  σ₀     := ()

instance env₁_1_optAlg_isDet (_bp : BanditParam) : AlgIsDeterministic (env₁_1_optAlg _bp) where
  actFn         := fun _ => 1
  actFn_meas    := measurable_const
  act_eq        := fun _ => rfl
  updateFn      := fun _ => ()
  updateFn_meas := measurable_const
  update_eq     := fun _ => rfl

noncomputable def env₁_1_transDet (bp : BanditParam) : TransIsDeterministic (env₁_1 bp) where
  s₀           := ()
  μ₀_eq        := rfl
  transFn      := fun _ => ()
  transFn_meas := measurable_const
  trans_eq     := fun _ => rfl

lemma env₁_1_optValue (bp : BanditParam) (T : ℕ) :
    SixPrimitives.optValue (env₁_1 bp) T = (1/2 + bp.Δ) * T := by
  have hEnv := env₁_1_isMarkov bp
  have hAlg := algIsDeterministic_isMarkov (env₁_1_optAlg bp)
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig)
      (_ : TopologicalSpace Sig) (_ : BorelSpace Sig)
      (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
      (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update),
      x = Phase2.algValue' (env₁_1 bp) alg (env₁_1 bp).hr_meas T} →
      v ≤ (1 / 2 + bp.Δ) * (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Unit) (a : Fin 2), |(env₁_1 bp).r (s, a)| ≤ 1 / 2 + bp.Δ := by
      intro s a
      change |if a = 0 then 1/2 - bp.Δ else 1/2 + bp.Δ| ≤ 1/2 + bp.Δ
      split_ifs
      · rw [abs_of_pos (by linarith [bp.hΔ1])]
        linarith [bp.hΔ0]
      · rw [abs_of_pos (by linarith [bp.hΔ0])]
    have h_val := algValue'_le_const (env₁_1 bp) alg (env₁_1 bp).hr_meas hEnv
        { act_markov := hAct, update_markov := hUpd } T (1 / 2 + bp.Δ) h_rew_bound
    rw [mul_comm] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T
      exact ⟨Unit, inferInstance, inferInstance, inferInstance,
             env₁_1_optAlg bp, hAlg.act_markov, hAlg.update_markov, rfl⟩
    · exact h_bound
  · apply le_csSup
    · exact ⟨(1 / 2 + bp.Δ) * T, h_bound⟩
    · refine ⟨Unit, inferInstance, inferInstance, inferInstance,
              env₁_1_optAlg bp, hAlg.act_markov, hAlg.update_markov, ?_⟩
      symm
      dsimp [Phase2.algValue']
      have hTransDet := env₁_1_transDet bp
      have h_eq_unit : ∀ t : Fin T,
          ∀ᵐ ω ∂(trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T),
          (ω t).2.2 = (env₁_1 bp).r ((), (ω t).1) :=
        fun t => trajMeasure_step_reward_eq_unit (env₁_1 bp) (env₁_1_optAlg bp)
            (env₁_1 bp).hr_meas hTransDet hEnv hAlg T t.1 t.2
      have h_act : ∀ t : Fin T,
          ∀ᵐ ω ∂(trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T),
          (ω t).1 = 1 := by
        intro t
        filter_upwards [traj_action_ae_eq_actFn (env₁_1 bp) (env₁_1_optAlg bp)
            (env₁_1 bp).hr_meas t.1 T t.2 hEnv] with ω hω
        exact hω
      have h_all : ∀ᵐ ω ∂(trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1/2 + bp.Δ := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_unit t, h_act t] with ω h_unit h_act_eq
        simp only [h_unit, h_act_eq, env₁_1]
        rw [if_neg (by decide)]
      have h_rew : ∀ᵐ traj ∂(trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) * (1/2 + bp.Δ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
            _ = ∑ t : Fin T, (1/2 + bp.Δ : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
            _ = (T : ℝ) * (1/2 + bp.Δ)        := by simp; ring
      haveI : IsProbabilityMeasure
          (trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T) :=
        trajMeasure_isProbability (env₁_1 bp) (env₁_1_optAlg bp)
            (env₁_1 bp).hr_meas hEnv hAlg T
      have h_int_eq : ∫ traj : Trajectory (Fin 2) Bool T, ∑ t : Fin T, (traj t).2.2
            ∂trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T =
          ∫ _ : Trajectory (Fin 2) Bool T, (T : ℝ) * (1/2 + bp.Δ)
            ∂trajMeasure (env₁_1 bp) (env₁_1_optAlg bp) (env₁_1 bp).hr_meas T :=
        integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp [mul_comm]

end EnvX1

-- ENVIRONMENT E₂

section EnvX2

noncomputable def env₂ (K : ℕ) (hK : 0 < K) :
    SixPrimitives.Env (Fin (K + 2)) (Fin 2) (Fin (K + 2)) where
  trans := Kernel.deterministic
    (fun (p : Fin (K + 2) × Fin 2) =>
      if h : p.1.val < K then
        if p.2 = 0 then ⟨p.1.val + 1, by omega⟩ else ⟨K + 1, by omega⟩
      else p.1)
    (by measurability)
  obs := Kernel.deterministic
    (fun (p : Fin (K + 2) × Fin 2) =>
      if h : p.1.val < K then
        if p.2 = 0 then ⟨p.1.val + 1, by omega⟩ else ⟨K + 1, by omega⟩
      else p.1)
    (by measurability)
  r := fun (s, a) =>
    if s.val < K then (if a = 0 then 1 else 0) else if s.val = K then 1 else 0
  hr_meas  := measurable_of_finite _
  μ₀       := Measure.dirac ⟨0, by omega⟩
  hμ₀      := inferInstance

def env₂_trap (K : ℕ) : Set (Fin (K + 2)) := {⟨K + 1, by omega⟩}

theorem env₂_hasP₂ (K : ℕ) (hK : 0 < K) : SixPrimitives.HasP₂ (env₂ K hK) (env₂_trap K) := by
  refine ⟨⟨⟨K + 1, by omega⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have : (⟨0, by omega⟩ : Fin (K + 2)) ∈ Set.univ := Set.mem_univ _
    rw [← h] at this; simp [env₂_trap] at this
  · intro s hs a
    have hval : s = ⟨K + 1, by omega⟩ := hs
    subst hval
    simp only [env₂, Kernel.deterministic_apply,
               show ¬ (K + 1 < K) from Nat.not_lt.mpr (Nat.le_refl K |>.trans (Nat.le_succ K))]
    simp [env₂_trap]
  · intro s hs a
    have hval : s = ⟨K + 1, by omega⟩ := hs; subst hval
    simp [env₂, show ¬ (K + 1 < K) from by omega]
  · refine ⟨⟨0, by omega⟩, by simp [env₂_trap], 1, ?_⟩
    simp only [env₂, Kernel.deterministic_apply,
               show (⟨0, by omega⟩ : Fin (K + 2)).val < K from hK]
    simp only [show (1 : Fin 2) ≠ 0 from by decide]
    simp [env₂_trap]

theorem env₂_inClassC (K : ℕ) (hK : 0 < K) : SixPrimitives.InClassC (env₂ K hK) SixPrimitives.VisitFrequencyAtLeast :=
  Or.inr (Or.inl ⟨env₂_trap K, env₂_hasP₂ K hK⟩)

noncomputable def env₂_isDet (K : ℕ) (hK : 0 < K) : EnvIsDeterministic (env₂ K hK) where
  s₀ := ⟨0, by omega⟩
  μ₀_eq := rfl
  transFn := fun p =>
    if h : p.1.val < K then
      if p.2 = 0 then ⟨p.1.val + 1, by omega⟩ else ⟨K + 1, by omega⟩
    else p.1
  transFn_meas := measurable_of_finite _
  trans_eq := fun _ => rfl
  obsFn := fun p =>
    if h : p.1.val < K then
      if p.2 = 0 then ⟨p.1.val + 1, by omega⟩ else ⟨K + 1, by omega⟩
    else p.1
  obsFn_meas := measurable_of_finite _
  obs_eq := fun _ => rfl

noncomputable def env₂_optAlg (K : ℕ) (_hK : 0 < K) : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Unit where
  act := Kernel.const _ (Measure.dirac 0)
  update := Kernel.const _ (Measure.dirac ())
  σ₀ := ()

instance env₂_optAlg_isDet (K : ℕ) (hK : 0 < K) : AlgIsDeterministic (env₂_optAlg K hK) where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma env₂_optAlg_state_le_K (K : ℕ) (hK : 0 < K) {T : ℕ} (ω : Fin T → Fin 2 × Fin (K + 2) × ℝ)
    (h_act : ∀ t (ht : t < T), (ω ⟨t, ht⟩).1 = 0) (t : ℕ) :
    (state_t (env₂ K hK) (env₂_isDet K hK).toTrans ω t).val ≤ K := by
  induction t with
  | zero =>
    simp [state_t, env₂_isDet, EnvIsDeterministic.toTrans]
  | succ t ih =>
    by_cases ht : t < T
    · rw [state_t_succ _ _ _ _ ht]
      have h_act_t := h_act t ht
      generalize h_s : state_t (env₂ K hK) (env₂_isDet K hK).toTrans ω t = s
      rw [h_s] at ih
      dsimp [env₂_isDet, env₂, EnvIsDeterministic.toTrans]
      simp only [h_act_t]
      split_ifs with h_lt
      · change s.val + 1 ≤ K
        omega
      · exact ih
    · rw [state_t, dif_neg ht]
      exact ih

lemma env₂_optValue (K : ℕ) (hK : 0 < K) (T : ℕ) :
    SixPrimitives.optValue (env₂ K hK) T = T := by
  have hEnv := envIsDeterministic_isMarkov (env₂ K hK) (env₂_isDet K hK)
  have hAlg := algIsDeterministic_isMarkov (env₂_optAlg K hK)
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' (env₂ K hK) alg (env₂ K hK).hr_meas T} → v ≤ (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Fin (K + 2)) (a : Fin 2), |(env₂ K hK).r (s, a)| ≤ 1 := by
      intro s a
      dsimp [env₂]
      split_ifs <;> norm_num
    have h_val := algValue'_le_const (env₂ K hK) alg (env₂ K hK).hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T 1 h_rew_bound
    simp only [mul_one] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T
      use Unit, inferInstance, inferInstance, inferInstance, env₂_optAlg K hK, hAlg.act_markov, hAlg.update_markov
    · exact h_bound
  · apply le_csSup
    · use T; exact h_bound
    · use Unit, inferInstance, inferInstance, inferInstance, env₂_optAlg K hK, hAlg.act_markov, hAlg.update_markov
      symm
      dsimp [Phase2.algValue']
      have h_eq_step : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T),
          (ω t).2.2 = (env₂ K hK).r (state_t (env₂ K hK) (env₂_isDet K hK).toTrans ω t.1, (ω t).1) :=
        fun t => trajMeasure_step_reward_eq (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas (env₂_isDet K hK).toTrans hEnv hAlg T t.1 t.2
      have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T),
          (ω t).1 = 0 := by
        intro t
        filter_upwards [traj_action_ae_eq_actFn (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas t.1 T t.2 hEnv] with ω hω
        exact hω
      have h_all : ∀ᵐ ω ∂(trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1 := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_step t, ae_all_iff.mpr h_act] with ω h_unit h_act_all
        rw [h_unit]
        have h_a_t : (ω t).1 = 0 := h_act_all t
        have h_state_le := env₂_optAlg_state_le_K K hK ω (fun i hi => h_act_all ⟨i, hi⟩) t.1
        generalize h_state : state_t (env₂ K hK) (env₂_isDet K hK).toTrans ω ↑t = s
        rw [h_state] at h_state_le
        dsimp [env₂]
        simp only [h_a_t]
        split_ifs with h_lt h_eq
        · rfl
        · rfl
        · omega
      have h_rew : ∀ᵐ traj ∂(trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1 : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) := by simp
      haveI : IsProbabilityMeasure (trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T) :=
        trajMeasure_isProbability (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas hEnv hAlg T
      have h_int_eq : ∫ (traj : Trajectory (Fin 2) (Fin (K + 2)) T), ∑ t : Fin T, (traj t).2.2 ∂trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T = ∫ (traj : Trajectory (Fin 2) (Fin (K + 2)) T), (T : ℝ) ∂trajMeasure (env₂ K hK) (env₂_optAlg K hK) (env₂ K hK).hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp

end EnvX2

-- ENVIRONMENT E₃

section EnvX3

private noncomputable def env₃_trans (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Kernel (Fin 2 × Fin 2) (Fin 2) where
  toFun := fun sa =>
    if sa.1 = 1 then Measure.dirac 1
    else if sa.2 = 0 then Measure.dirac 0
    else (PMF.bernoulli ⟨p, hp0⟩
          (show (⟨p, hp0⟩ : ℝ≥0) ≤ 1 from by exact_mod_cast hp1)).toMeasure.map
          (fun b : Bool => if b then (1 : Fin 2) else 0)
  measurable' := measurable_of_countable _

noncomputable def env₃ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    SixPrimitives.Env (Fin 2) (Fin 2) Unit where
  trans    := env₃_trans p hp0 hp1
  obs      := Kernel.const _ (Measure.dirac ())
  r        := fun (s, a) => if s = (1 : Fin 2) then 1 else if a = (0 : Fin 2) then 1/2 else 0
  hr_meas  := measurable_of_finite _
  μ₀       := Measure.dirac 0
  hμ₀      := inferInstance

theorem env₃_hasP₃ (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    SixPrimitives.HasP₃ (env₃ p hp0.le hp1) ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_singleton.mpr (by decide)
  · exact Set.singleton_nonempty 0
  · exact Set.singleton_nonempty 1
  · intro s hs a h_greedy
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    have h_a_eq_0 : a = 0 := by
      revert h_greedy; fin_cases a
      · intro _; rfl
      · intro h_greedy
        have h_greedy_0 := h_greedy 0
        simp only [env₃] at h_greedy_0
        norm_num at h_greedy_0
    subst h_a_eq_0
    simp only [env₃, env₃_trans, Kernel.coe_mk]
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [h01, ite_false, ite_true]
    exact MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton 0)
  · refine ⟨0, Set.mem_singleton 0, 1, ?_⟩
    simp only [env₃, env₃_trans, Kernel.coe_mk]
    have h1 : (0 : Fin 2) = 1 ↔ False := by decide
    have h2 : (1 : Fin 2) = 0 ↔ False := by decide
    simp only [h1, h2, ite_false]
    have h_meas : Measurable (fun b : Bool => if b then (1 : Fin 2) else 0) :=
      measurable_of_finite _
    rw [MeasureTheory.Measure.map_apply h_meas (measurableSet_singleton 1)]
    have h_pre : (fun b : Bool => if b then (1 : Fin 2) else 0) ⁻¹' {1} = {true} := by
      ext b; cases b <;> simp
    rw [h_pre]
    rw [(PMF.bernoulli ⟨p, hp0.le⟩ hp1).toMeasure_apply (measurableSet_singleton true)]
    simp [tsum_fintype, Set.indicator_apply, PMF.bernoulli_apply]
    exact hp0
  · refine ⟨1/2, 1, ?_, ?_, by norm_num⟩
    · intro s hs a
      simp only [Set.mem_singleton_iff] at hs; subst hs
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      simp only [env₃, h01, ite_false]
      split_ifs
      · norm_num
      · linarith [hp1]
    · intro s hs; use 0
      simp only [Set.mem_singleton_iff] at hs; subst hs
      simp only [env₃, ite_true, le_refl]

theorem env₃_inClassC (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    SixPrimitives.InClassC (env₃ p hp0.le hp1) SixPrimitives.VisitFrequencyAtLeast :=
  Or.inr (Or.inr (Or.inl ⟨{0}, {1}, env₃_hasP₃ p hp0 hp1⟩))

instance env₃_isMarkov (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    EnvIsMarkov (env₃ p hp0 hp1) where
  trans_markov := ⟨fun ⟨s, a⟩ => by
    simp only [env₃, env₃_trans, Kernel.coe_mk]
    split_ifs with h1 h2
    · exact inferInstance
    · exact inferInstance
    · exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩
  obs_markov := ⟨fun _ => by dsimp [env₃]; infer_instance⟩

noncomputable def env₃_optAlg : SixPrimitives.Algorithm (Fin 2) Unit Unit where
  act    := Kernel.const _ (Measure.dirac 1)
  update := Kernel.const _ (Measure.dirac ())
  σ₀     := ()

instance env₃_optAlg_isDet : AlgIsDeterministic env₃_optAlg where
  actFn         := fun _ => 1
  actFn_meas    := measurable_const
  act_eq        := fun _ => rfl
  updateFn      := fun _ => ()
  updateFn_meas := measurable_const
  update_eq     := fun _ => rfl

-- NEW LEMMAS FOR PHASE 3

lemma env₃_reward_one_iff_state_one
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s a : Fin 2) :
    (env₃ p hp0 hp1).r (s, a) = 1 ↔ s = 1 := by
  fin_cases s <;> fin_cases a <;> simp [env₃]

private lemma env₃_r_le_half_or_eq_one
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s a : Fin 2) :
    (env₃ p hp0 hp1).r (s, a) ≤ 1/2 ∨ (env₃ p hp0 hp1).r (s, a) = 1 := by
  fin_cases s <;> fin_cases a <;> simp [env₃]

private lemma env₃_traj_reward_dichotomy
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (t : Fin T) :
    ∀ᵐ traj ∂(trajMeasure (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T),
      (traj t).2.2 ≤ 1/2 ∨ (traj t).2.2 = 1 := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0.le hp1) := env₃_isMarkov p hp0.le hp1
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  haveI hOSK : IsMarkovKernel (oneStepKernel (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas) :=
    oneStepKernel_isMarkov _ _ _ hEnv hAlg
  have hmf_step : Measurable (fun q : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) =>
      (q.1.1.1.1, q.1.1.1.2, q.1.1.2, q.2, q.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set_step : MeasurableSet {x : Fin 2 × Unit × ℝ × Sig × Fin 2 | x.2.2.1 ≤ 1/2 ∨ x.2.2.1 = 1} := by measurability
  have hstep : ∀ σs : Sig × Fin 2,
      ∀ᵐ step ∂(oneStepKernel (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas σs),
        step.2.2.1 ≤ 1/2 ∨ step.2.2.1 = 1 := by
    intro ⟨σ, s⟩
    simp only [oneStepKernel]
    rw [Kernel.map_apply (hf := hmf_step)]
    rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set_step]
    rw [Kernel.ae_compProd_iff (by measurability)]
    rw [Kernel.ae_compProd_iff (by measurability)]
    rw [Kernel.ae_compProd_iff (by measurability)]
    apply ae_of_all; intro ao
    simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
    exact ae_of_all _ fun _ => ae_of_all _ fun _ =>
      env₃_r_le_half_or_eq_one p hp0.le hp1 s ao.1
  have h_aux : ∀ (T' : ℕ) (σs : Sig × Fin 2) (k : Fin T'),
      ∀ᵐ q ∂(trajMeasureAux (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T' σs),
        (q.1 k).2.2 ≤ 1/2 ∨ (q.1 k).2.2 = 1 := by
    intro T'
    induction T' with
    | zero => intro _ k; exact k.elim0
    | succ T' ih =>
      haveI := trajMeasureAux_isMarkov (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas hEnv hAlg T'
      intro σs k
      have hmf : Measurable (fun x : ((Fin T' → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) ×
          (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
          ((Fin.snoc x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1) : Fin (T' + 1) → Fin 2 × Unit × ℝ),
           (x.2.2.2.2.1, x.2.2.2.2.2))) := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i
          refine Fin.lastCases ?_ ?_ i
          · simp; fun_prop
          · intro j; simp; fun_prop
        · fun_prop
      have h_set_fin (j : Fin (T' + 1)) :
          MeasurableSet {q : (Fin (T' + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
            (q.1 j).2.2 ≤ 1/2 ∨ (q.1 j).2.2 = 1} := by
        have h_meas_q : Measurable (fun q : (Fin (T' + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 => (q.1 j).2.2) :=
          (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply j).comp measurable_fst)
        exact MeasurableSet.union (measurableSet_le h_meas_q measurable_const) (measurableSet_eq_fun h_meas_q measurable_const)
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := hmf)]
      refine Fin.lastCases ?_ ?_ k
      · rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.last T'))]
        rw [Kernel.ae_compProd_iff (by measurability)]
        simp only [Fin.snoc_last]
        apply ae_of_all; intro q
        simp only [Kernel.comap_apply]
        exact hstep q.2
      · intro j
        rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.castSucc j))]
        rw [Kernel.ae_compProd_iff (by measurability)]
        simp only [Fin.snoc_castSucc]
        filter_upwards [ih σs j] with q hq
        exact ae_of_all _ fun _ => hq
  simp only [trajMeasure]
  have h_meas_t : Measurable (fun traj : Trajectory (Fin 2) Unit T => (traj t).2.2) :=
    (measurable_snd.comp measurable_snd).comp (measurable_pi_apply t)
  have h_set_traj : MeasurableSet {traj : Trajectory (Fin 2) Unit T | (traj t).2.2 ≤ 1/2 ∨ (traj t).2.2 = 1} :=
    MeasurableSet.union (measurableSet_le h_meas_t measurable_const) (measurableSet_eq_fun h_meas_t measurable_const)
  rw [MeasureTheory.ae_map_iff measurable_fst.aemeasurable h_set_traj]
  rw [ae_iff]
  change ((trajMeasureAux (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T).toFun ∘ₘ
      (Measure.dirac alg.σ₀).prod (env₃ p hp0.le hp1).μ₀)
    {a | ¬((a.1 t).2.2 ≤ 1/2 ∨ (a.1 t).2.2 = 1)} = 0
  have h_set_not : MeasurableSet {a : (Fin T → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
      ¬((a.1 t).2.2 ≤ 1/2 ∨ (a.1 t).2.2 = 1)} :=
    (measurable_fst h_set_traj).compl
  rw [Measure.bind_apply h_set_not (trajMeasureAux (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T).measurable'.aemeasurable]
  calc ∫⁻ σs : Sig × Fin 2,
        (trajMeasureAux (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T σs)
          {a | ¬((a.1 t).2.2 ≤ 1/2 ∨ (a.1 t).2.2 = 1)}
        ∂((Measure.dirac alg.σ₀).prod (env₃ p hp0.le hp1).μ₀)
      = ∫⁻ _ : Sig × Fin 2, 0 ∂((Measure.dirac alg.σ₀).prod (env₃ p hp0.le hp1).μ₀) :=
          lintegral_congr fun σs => by rw [← ae_iff]; exact h_aux T σs t
    _ = 0 := lintegral_zero

private lemma oneStepKernel_peel_state
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) :
    (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas σs {step | step.2.2.2.2 = 1}) =
    ∫⁻ a, (env₃ p hp0 hp1).trans (σs.2, a) {1} ∂(alg.act σs.1) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  simp only [oneStepKernel]
  have h_map : Measurable (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {step : Fin 2 × Unit × ℝ × Sig × Fin 2 | step.2.2.2.2 = 1} :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
      (measurableSet_singleton 1)
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) ⁻¹'
      {step | step.2.2.2.2 = 1} = {p | p.1.2 = 1} := by ext p; rfl
  rw [h_pre, Kernel.compProd_apply (by measurability)]
  have h_upd_int : ∀ b : (((Fin 2 × Unit) × ℝ) × Fin 2),
      alg.update.comap
          (fun x : (Sig × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) =>
            (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2))
          (by measurability) (σs, b)
          (Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.2 = 1}) =
      if b.2 = 1 then 1 else 0 := by
    intro b
    by_cases hb : b.2 = 1
    · simp only [hb, if_true]
      have h_univ : Prod.mk b ⁻¹'
          {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.2 = 1} = Set.univ := by
        ext c; simp [hb]
      rw [h_univ, measure_univ]
    · simp only [hb, if_false]
      have h_empty : Prod.mk b ⁻¹'
          {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.2 = 1} = ∅ := by
        ext c; simp [hb]
      rw [h_empty, measure_empty]
  rw [lintegral_congr h_upd_int]
  have h_revert : ∫⁻ b : (((Fin 2 × Unit) × ℝ) × Fin 2),
        (if b.2 = 1 then 1 else 0 : ℝ≥0∞)
        ∂((((alg.act.comap Prod.fst measurable_fst).compProd
              ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) (by measurability))).compProd
            (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1))
              ((env₃ p hp0 hp1).hr_meas.comp (by measurability)))).compProd
          ((env₃ p hp0 hp1).trans.comap (fun x => (x.1.2, x.2.1.1)) (by measurability))) σs =
      ((((alg.act.comap Prod.fst measurable_fst).compProd
              ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) (by measurability))).compProd
            (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1))
              ((env₃ p hp0 hp1).hr_meas.comp (by measurability)))).compProd
          ((env₃ p hp0 hp1).trans.comap (fun x => (x.1.2, x.2.1.1)) (by measurability))) σs
        {b | b.2 = 1} := by
    have h_ind_eq : (fun b : (((Fin 2 × Unit) × ℝ) × Fin 2) =>
          if b.2 = 1 then (1 : ℝ≥0∞) else 0) =
        {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.2 = 1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext b; by_cases hb : b.2 = 1 <;> simp [hb]
    rw [h_ind_eq, lintegral_indicator_const (by measurability), one_mul]
  rw [h_revert, Kernel.compProd_apply (by measurability)]
  have h_trans_int : ∀ b : ((Fin 2 × Unit) × ℝ),
      (env₃ p hp0 hp1).trans.comap
          (fun x : (Sig × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1))
          (by measurability) (σs, b)
          (Prod.mk b ⁻¹' {p : (((Fin 2 × Unit) × ℝ) × Fin 2) | p.2 = 1}) =
      (env₃ p hp0 hp1).trans (σs.2, b.1.1) {1} := by
    intro b
    simp only [Kernel.comap_apply]
    have h_set_eq : Prod.mk b ⁻¹'
        {p : (((Fin 2 × Unit) × ℝ) × Fin 2) | p.2 = 1} = {1} := by
      ext c; simp
    rw [h_set_eq]
  rw [lintegral_congr h_trans_int]
  have h_f_meas : Measurable (fun b : (Fin 2 × Unit) × ℝ =>
      (env₃ p hp0 hp1).trans (σs.2, b.1.1) {1}) := by
    have hm1 : Measurable (fun b : (Fin 2 × Unit) × ℝ => (σs.2, b.1.1)) :=
      measurable_const.prodMk (measurable_fst.comp measurable_fst)
    exact (Kernel.measurable_coe (env₃ p hp0 hp1).trans (measurableSet_singleton 1)).comp hm1
  rw [Kernel.lintegral_compProd _ _ _ h_f_meas]
  have h_rew_int : ∀ b : (Fin 2 × Unit),
      ∫⁻ r : ℝ, (env₃ p hp0 hp1).trans (σs.2, (b, r).1.1) {1}
        ∂(Kernel.deterministic
            (fun x : (Sig × Fin 2) × (Fin 2 × Unit) => (env₃ p hp0 hp1).r (x.1.2, x.2.1))
            ((env₃ p hp0 hp1).hr_meas.comp (by measurability)) (σs, b)) =
      (env₃ p hp0 hp1).trans (σs.2, b.1) {1} := by
    intro b
    simp only [Kernel.deterministic_apply]
    rw [lintegral_dirac]
  rw [lintegral_congr h_rew_int]
  have h_f_meas2 : Measurable (fun b : Fin 2 × Unit =>
      (env₃ p hp0 hp1).trans (σs.2, b.1) {1}) := by
    have hm1 : Measurable (fun b : Fin 2 × Unit => (σs.2, b.1)) :=
      measurable_const.prodMk measurable_fst
    exact (Kernel.measurable_coe (env₃ p hp0 hp1).trans (measurableSet_singleton 1)).comp hm1
  rw [Kernel.lintegral_compProd _ _ _ h_f_meas2]
  have h_obs_int : ∀ a : Fin 2,
      ∫⁻ o : Unit, (env₃ p hp0 hp1).trans (σs.2, (a, o).1) {1}
        ∂((env₃ p hp0 hp1).obs.comap (fun x : (Sig × Fin 2) × Fin 2 => (x.1.2, x.2))
            (by measurability) (σs, a)) =
      (env₃ p hp0 hp1).trans (σs.2, a) {1} := by
    intro a
    simp only [Kernel.comap_apply]
    have h_const : (fun o : Unit => (env₃ p hp0 hp1).trans (σs.2, (a, o).1) {1}) =
        fun _ => (env₃ p hp0 hp1).trans (σs.2, a) {1} := rfl
    rw [h_const, lintegral_const]
    have h_prob : IsProbabilityMeasure ((env₃ p hp0 hp1).obs (σs.2, a)) := inferInstance
    rw [measure_univ, mul_one]
  rw [lintegral_congr h_obs_int]
  simp only [Kernel.comap_apply]

private lemma oneStepKernel_peel_reward
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) :
    (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas σs {step |
step.2.2.1 = 1}) =
    ∫⁻ a, (if (env₃ p hp0 hp1).r (σs.2, a) = 1 then 1 else 0 : ℝ≥0∞) ∂(alg.act σs.1) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI := hEnv.obs_markov;
  haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have h_meas_upd : Measurable (fun x : (Sig × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) := by measurability
  have h_meas_trans : Measurable (fun x : (Sig × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1)) := by measurability
  have h_meas_rew : Measurable (fun x : (Sig × Fin 2) × (Fin 2 × Unit) => (x.1.2, x.2.1)) := by measurability
  have h_meas_obs : Measurable (fun x : (Sig × Fin 2) × Fin 2 => (x.1.2, x.2)) := by measurability
  simp only [oneStepKernel]
  have h_map : Measurable (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {step : Fin 2 × Unit × ℝ × Sig × Fin 2 |
step.2.2.1 = 1} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd)) measurable_const
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) => (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) ⁻¹' {step |
step.2.2.1 = 1} = {p | p.1.1.2 = 1} := rfl
  have hs1 : MeasurableSet {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) |
p.1.1.2 = 1} :=
    measurableSet_eq_fun (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_const
  rw [h_pre, Kernel.compProd_apply hs1]
  have h_upd_int : ∀ b : (((Fin 2 × Unit) × ℝ) × Fin 2),
      alg.update.comap (fun x : (Sig × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) h_meas_upd (σs, b) (Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.2 = 1}) =
      if b.1.2 = 1 then 1 else 0 := by
    intro b
    by_cases hb : b.1.2 = 1
    · simp only [hb, if_true]
      have h_univ : Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.2 = 1} = Set.univ := by ext c; simp [hb]
      rw [h_univ, measure_univ]
    · simp only [hb, if_false]
      have h_empty : Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.2 = 1} = ∅ := by ext c; simp [hb]
      rw [h_empty, measure_empty]
  rw [lintegral_congr h_upd_int]
  have hs2 : MeasurableSet {b : (((Fin 2 × Unit) × ℝ) × Fin 2) |
b.1.2 = 1} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have H2 : ∫⁻ b : (((Fin 2 × Unit) × ℝ) × Fin 2), (if b.1.2 = 1 then 1 else 0 : ℝ≥0∞) ∂((((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)).compProd (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew))).compProd ((env₃ p hp0 hp1).trans.comap (fun x => (x.1.2, x.2.1.1)) h_meas_trans)) σs =
            ∫⁻ b, ({b' : (((Fin 2 × Unit) × ℝ) × Fin 2) | b'.1.2 = 1}.indicator (fun _ => (1 : ℝ≥0∞))) b ∂((((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)).compProd (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew))).compProd ((env₃ p hp0 hp1).trans.comap (fun x => (x.1.2, x.2.1.1)) h_meas_trans)) σs := by
    apply lintegral_congr
    intro b
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [H2, lintegral_indicator_const hs2, one_mul]
  rw [Kernel.compProd_apply hs2]
  have h_trans_int : ∀ c : ((Fin 2 × Unit) × ℝ),
      (env₃ p hp0 hp1).trans.comap (fun x : (Sig × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1)) h_meas_trans (σs, c) (Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) |
b.1.2 = 1}) =
      if c.2 = 1 then 1 else 0 := by
    intro c
    by_cases hc : c.2 = 1
    · simp only [hc, if_true]
      have h_univ : Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.2 = 1} = Set.univ := by ext s'; simp [hc]
      rw [h_univ, measure_univ]
    · simp only [hc, if_false]
      have h_empty : Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.2 = 1} = ∅ := by ext s'; simp [hc]
      rw [h_empty, measure_empty]
  rw [lintegral_congr h_trans_int]
  have hs3 : MeasurableSet {c : ((Fin 2 × Unit) × ℝ) |
c.2 = 1} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have H3 : ∫⁻ c : ((Fin 2 × Unit) × ℝ), (if c.2 = 1 then 1 else 0 : ℝ≥0∞) ∂(((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)).compProd (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew))) σs =
            ∫⁻ c, ({c' : ((Fin 2 × Unit) × ℝ) | c'.2 = 1}.indicator (fun _ => (1 : ℝ≥0∞))) c ∂(((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)).compProd (Kernel.deterministic (fun x => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew))) σs := by
    apply lintegral_congr
    intro c
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [H3, lintegral_indicator_const hs3, one_mul]
  rw [Kernel.compProd_apply hs3]
  have h_rew_int : ∀ d : (Fin 2 × Unit),
      Kernel.deterministic (fun x : (Sig × Fin 2) × (Fin 2 × Unit) => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew) (σs, d) (Prod.mk d ⁻¹' {c : ((Fin 2 × Unit) × ℝ) | c.2 = 1}) =
      if (env₃ p hp0 hp1).r (σs.2, d.1) = 1 then 1 else 0 := by
    intro d
    simp only [Kernel.deterministic_apply]
    have h_set_eq : Prod.mk d ⁻¹' {c : ((Fin 2 × Unit) × ℝ) | c.2 = 1} = ({1} : Set ℝ) := by
      ext r
      simp
    rw [h_set_eq]
    by_cases hd : (env₃ p hp0 hp1).r (σs.2, d.1) = 1
    · simp only [hd, if_true]
      exact Measure.dirac_apply_of_mem (Set.mem_singleton 1)
    · simp only [hd, if_false]
      have h_meas_set : MeasurableSet ({1} : Set ℝ) := measurableSet_singleton 1
      calc Measure.dirac ((env₃ p hp0 hp1).r (σs.2, d.1)) {1}
        _ = ∫⁻ x, ({1} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) x ∂Measure.dirac ((env₃ p hp0 hp1).r (σs.2, d.1)) := by
          rw [lintegral_indicator_const h_meas_set, one_mul]
        _ = ({1} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) ((env₃ p hp0 hp1).r (σs.2, d.1)) := by
          rw [lintegral_dirac]
        _ = 0 := by
          rw [Set.indicator_apply]
          simp only [Set.mem_singleton_iff, hd, if_false]
  rw [lintegral_congr h_rew_int]
  have hm1 : Measurable (fun b : Fin 2 × Unit => (σs.2, b.1)) := measurable_const.prodMk measurable_fst
  have hs4 : MeasurableSet {d : Fin 2 × Unit |
(env₃ p hp0 hp1).r (σs.2, d.1) = 1} :=
    measurableSet_eq_fun ((env₃ p hp0 hp1).hr_meas.comp hm1) measurable_const
  have H4 : ∫⁻ d : Fin 2 × Unit, (if (env₃ p hp0 hp1).r (σs.2, d.1) = 1 then 1 else 0 : ℝ≥0∞) ∂((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)) σs =
            ∫⁻ d, ({d' : Fin 2 × Unit | (env₃ p hp0 hp1).r (σs.2, d'.1) = 1}.indicator (fun _ => (1 : ℝ≥0∞))) d ∂((alg.act.comap Prod.fst measurable_fst).compProd ((env₃ p hp0 hp1).obs.comap (fun x => (x.1.2, x.2)) h_meas_obs)) σs := by
    apply lintegral_congr
    intro d
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [H4, lintegral_indicator_const hs4, one_mul]
  rw [Kernel.compProd_apply hs4]
  have h_obs_int : ∀ a : Fin 2,
      ((env₃ p hp0 hp1).obs.comap (fun x : (Sig × Fin 2) × Fin 2 => (x.1.2, x.2)) h_meas_obs (σs, a)) (Prod.mk a ⁻¹' {d : Fin 2 × Unit | (env₃ p hp0 hp1).r (σs.2, d.1) = 1}) =
      if (env₃ p hp0 hp1).r (σs.2, a) = 1 then 1 else 0 := by
    intro a
    by_cases ha : (env₃ p hp0 hp1).r (σs.2, a) = 1
    · simp only [ha, if_true]
      have h_univ : Prod.mk a ⁻¹' {d : Fin 2 × Unit |
(env₃ p hp0 hp1).r (σs.2, d.1) = 1} = Set.univ := by ext o; simp [ha]
      rw [h_univ, measure_univ]
    · simp only [ha, if_false]
      have h_empty : Prod.mk a ⁻¹' {d : Fin 2 × Unit |
(env₃ p hp0 hp1).r (σs.2, d.1) = 1} = ∅ := by ext o; simp [ha]
      rw [h_empty, measure_empty]
  rw [lintegral_congr h_obs_int]
  simp only [Kernel.comap_apply]

private lemma oneStepKernel_peel_action
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) (a_target : Fin 2) :
    (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas σs {step | step.1 = a_target}) =
    alg.act σs.1 {a_target} := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have h_meas_upd : Measurable (fun x : (Sig × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) := by measurability
  have h_meas_trans : Measurable (fun x : (Sig × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1)) := by measurability
  have h_meas_rew : Measurable (fun x : (Sig × Fin 2) × (Fin 2 × Unit) => (x.1.2, x.2.1)) := by measurability
  have h_meas_obs : Measurable (fun x : (Sig × Fin 2) × Fin 2 => (x.1.2, x.2)) := by measurability
  simp only [oneStepKernel]
  have h_map : Measurable (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {step : Fin 2 × Unit × ℝ × Sig × Fin 2 | step.1 = a_target} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) => (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) ⁻¹' {step | step.1 = a_target} = {p | p.1.1.1.1 = a_target} := rfl
  have hs1 : MeasurableSet {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))) measurable_const
  rw [h_pre, Kernel.compProd_apply hs1]
  have h_upd_int : ∀ b : (((Fin 2 × Unit) × ℝ) × Fin 2),
      alg.update.comap (fun x : (Sig × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) h_meas_upd (σs, b) (Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.1.1 = a_target}) =
      if b.1.1.1 = a_target then 1 else 0 := by
    intro b
    by_cases hb : b.1.1.1 = a_target
    · have h_univ : Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.1.1 = a_target} = Set.univ := by
        ext c; simp [hb]
      rw [h_univ]
      simp only [hb, if_true]
      exact measure_univ
    · have h_empty : Prod.mk b ⁻¹' {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Sig) | p.1.1.1.1 = a_target} = ∅ := by
        ext c; simp [hb]
      rw [h_empty]
      simp only [hb, if_false]
      exact measure_empty
  rw [lintegral_congr h_upd_int]
  have hs2 : MeasurableSet {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_fst.comp measurable_fst)) measurable_const
  have h_ind_eq2 : (fun b : (((Fin 2 × Unit) × ℝ) × Fin 2) => if b.1.1.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {b' : (((Fin 2 × Unit) × ℝ) × Fin 2) | b'.1.1.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext b; by_cases hb : b.1.1.1 = a_target <;> simp [hb]
  rw [h_ind_eq2, lintegral_indicator_const hs2, one_mul]
  rw [Kernel.compProd_apply hs2]
  have h_trans_int : ∀ c : ((Fin 2 × Unit) × ℝ),
      (env₃ p hp0 hp1).trans.comap (fun x : (Sig × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1)) h_meas_trans (σs, c) (Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.1.1 = a_target}) =
      if c.1.1 = a_target then 1 else 0 := by
    intro c
    by_cases hc : c.1.1 = a_target
    · have h_univ : Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.1.1 = a_target} = Set.univ := by
        ext s'; simp [hc]
      rw [h_univ]
      simp only [hc, if_true]
      exact measure_univ
    · have h_empty : Prod.mk c ⁻¹' {b : (((Fin 2 × Unit) × ℝ) × Fin 2) | b.1.1.1 = a_target} = ∅ := by
        ext s'; simp [hc]
      rw [h_empty]
      simp only [hc, if_false]
      exact measure_empty
  rw [lintegral_congr h_trans_int]
  have hs3 : MeasurableSet {c : ((Fin 2 × Unit) × ℝ) | c.1.1 = a_target} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const
  have h_ind_eq3 : (fun c : ((Fin 2 × Unit) × ℝ) => if c.1.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {c' : ((Fin 2 × Unit) × ℝ) | c'.1.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext c; by_cases hc : c.1.1 = a_target <;> simp [hc]
  rw [h_ind_eq3, lintegral_indicator_const hs3, one_mul]
  rw [Kernel.compProd_apply hs3]
  have h_rew_int : ∀ d : (Fin 2 × Unit),
      Kernel.deterministic (fun x : (Sig × Fin 2) × (Fin 2 × Unit) => (env₃ p hp0 hp1).r (x.1.2, x.2.1)) ((env₃ p hp0 hp1).hr_meas.comp h_meas_rew) (σs, d) (Prod.mk d ⁻¹' {c : ((Fin 2 × Unit) × ℝ) | c.1.1 = a_target}) =
      if d.1 = a_target then 1 else 0 := by
    intro d
    by_cases hd : d.1 = a_target
    · have h_univ : Prod.mk d ⁻¹' {c : ((Fin 2 × Unit) × ℝ) | c.1.1 = a_target} = Set.univ := by
        ext r; simp [hd]
      rw [h_univ]
      simp only [hd, if_true, Kernel.deterministic_apply]
      exact measure_univ
    · have h_empty : Prod.mk d ⁻¹' {c : ((Fin 2 × Unit) × ℝ) | c.1.1 = a_target} = ∅ := by
        ext r; simp [hd]
      rw [h_empty]
      simp only [hd, if_false, Kernel.deterministic_apply]
      exact measure_empty
  rw [lintegral_congr h_rew_int]
  have hs4 : MeasurableSet {d : Fin 2 × Unit | d.1 = a_target} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have h_ind_eq4 : (fun d : Fin 2 × Unit => if d.1 = a_target then (1 : ℝ≥0∞) else 0) =
      {d' : Fin 2 × Unit | d'.1 = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext d; by_cases hd : d.1 = a_target <;> simp [hd]
  rw [h_ind_eq4, lintegral_indicator_const hs4, one_mul]
  rw [Kernel.compProd_apply hs4]
  have h_obs_int : ∀ a : Fin 2,
      ((env₃ p hp0 hp1).obs.comap (fun x : (Sig × Fin 2) × Fin 2 => (x.1.2, x.2)) h_meas_obs (σs, a)) (Prod.mk a ⁻¹' {d : Fin 2 × Unit | d.1 = a_target}) =
      if a = a_target then 1 else 0 := by
    intro a
    by_cases ha : a = a_target
    · have h_univ : Prod.mk a ⁻¹' {d : Fin 2 × Unit | d.1 = a_target} = Set.univ := by
        ext o; simp [ha]
      rw [h_univ]
      simp only [ha, if_true]
      exact measure_univ
    · have h_empty : Prod.mk a ⁻¹' {d : Fin 2 × Unit | d.1 = a_target} = ∅ := by
        ext o; simp [ha]
      rw [h_empty]
      simp only [ha, if_false]
      exact measure_empty
  rw [lintegral_congr h_obs_int]
  have hs5 : MeasurableSet {a : Fin 2 | a = a_target} :=
    measurableSet_eq_fun measurable_id measurable_const
  have h_ind_eq5 : (fun a : Fin 2 => if a = a_target then (1 : ℝ≥0∞) else 0) =
      {a' : Fin 2 | a' = a_target}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext a; by_cases ha : a = a_target <;> simp [ha]
  rw [h_ind_eq5, lintegral_indicator_const hs5, one_mul]
  simp only [Kernel.comap_apply]
  have h_eq_set : {a : Fin 2 | a = a_target} = {a_target} := by ext; simp
  rw [h_eq_set]

private lemma trajMeasureAux_next_state_prob
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) (t : ℕ) (s_target : Fin 2) :
    (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas (t + 1) σs {x | x.2.2 = s_target}) =
    ∫⁻ x, oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas x.2 {step |
      step.2.2.2.2 = s_target} ∂(trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t σs) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI hOsk : IsMarkovKernel (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas) := oneStepKernel_isMarkov _ _ _ hEnv hAlg
  haveI hTm : IsMarkovKernel (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t) := trajMeasureAux_isMarkov _ _ _ hEnv hAlg t
  simp only [trajMeasureAux]
  have h_map : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; fun_prop
      · intro j; simp only [Fin.snoc_castSucc]; fun_prop
    · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have h_set : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
    x.2.2 = s_target} :=
    measurable_snd.comp measurable_snd (measurableSet_singleton s_target)
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) ⁻¹' {x |
    x.2.2 = s_target} =
    {x | x.2.2.2.2.2 = s_target} := by ext x; rfl
  haveI : IsMarkovKernel ((oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap
    (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability)) :=
    Kernel.IsMarkovKernel.comap _ _
  rw [h_pre, Kernel.compProd_apply (by measurability)]
  have h_inner : ∀ a : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)),
      (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability) (σs, a) {c |
      c.2.2.2.2 = s_target} =
      oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas a.2 {step |
      step.2.2.2.2 = s_target} := by
    intro a; simp only [Kernel.comap_apply]
  simp

private lemma trajMeasureAux_action_prob
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) (t : ℕ) (a_target : Fin 2) :
    (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas (t + 1) σs {x | (x.1 (Fin.last t)).1 = a_target}) =
    ∫⁻ x, oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas x.2 {step | step.1 = a_target} ∂(trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t σs) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI hOsk : IsMarkovKernel (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas) := oneStepKernel_isMarkov _ _ _ hEnv hAlg
  haveI hTm : IsMarkovKernel (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t) := trajMeasureAux_isMarkov _ _ _ hEnv hAlg t
  simp only [trajMeasureAux]
  have h_map : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; fun_prop
      · intro j; simp only [Fin.snoc_castSucc]; fun_prop
    · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have h_set : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 | (x.1 (Fin.last t)).1 = a_target} :=
    measurable_fst.comp ((measurable_pi_apply (Fin.last t)).comp measurable_fst) (measurableSet_singleton a_target)
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) ⁻¹' {x |
    (x.1 (Fin.last t)).1 = a_target} =
    {x | x.2.1 = a_target} := by ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Fin.snoc_last]
  haveI : IsMarkovKernel ((oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap
    (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability)) :=
    Kernel.IsMarkovKernel.comap _ _
  rw [h_pre, Kernel.compProd_apply (by measurability)]
  have h_inner : ∀ a : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)),
      (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability) (σs, a) {c |
      c.1 = a_target} =
      oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas a.2 {step |
      step.1 = a_target} := by
    intro a; simp only [Kernel.comap_apply]
  simp

private lemma M_action_eq_trajMeasure
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (T : ℕ) (s : Fin T) :
    let env := env₃ p hp0 hp1
    let μ₀ := (Measure.dirac alg.σ₀).prod env.μ₀
    let M := fun n => μ₀.bind (trajMeasureAux env alg env.hr_meas n)
    (M (s.val + 1) {x | (x.1 (Fin.last s.val)).1 = 1}) =
    trajMeasure env alg env.hr_meas T {traj | (traj s).1 = 1} := by
  intro env μ₀ M
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0 hp1
  have h_meas_set : MeasurableSet {traj' : Trajectory (Fin 2) Unit (s.val + 1) | (traj' ⟨s.val, Nat.lt_succ_self s.val⟩).1 = 1} := by measurability
  have h_trunc := trajMeasure_truncation env alg env.hr_meas hEnv hAlg T (s.val + 1) s.isLt _ h_meas_set
  have h_set_eq : {traj : Trajectory (Fin 2) Unit T | (traj s).1 = 1} =
    {traj : Trajectory (Fin 2) Unit T | (fun i : Fin (s.val + 1) => traj (Fin.castLE s.isLt i)) ∈ {traj' : Trajectory (Fin 2) Unit (s.val + 1) | (traj' ⟨s.val, Nat.lt_succ_self s.val⟩).1 = 1}} := by
    ext traj; rfl
  rw [h_set_eq, h_trunc]
  simp only [trajMeasure]
  have h_map : Measurable (Prod.fst : ((Fin (s.val + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2) → (Fin (s.val + 1) → Fin 2 × Unit × ℝ)) := measurable_fst
  rw [Measure.map_apply h_map h_meas_set]
  rfl

private lemma env₃_state_recurrence_le
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (t : ℕ) :
    let env := env₃ p hp0 hp1
    let μ₀ := (Measure.dirac alg.σ₀).prod env.μ₀
    let M := fun n => μ₀.bind (trajMeasureAux env alg env.hr_meas n)
    (M (t + 1) {x | x.2.2 = 1}).toReal ≤
    (M t {x | x.2.2 = 1}).toReal + p * (M (t + 1) {x | (x.1 (Fin.last t)).1 = 1}).toReal := by
  intro env μ₀ M
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0 hp1
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  haveI hOsk : IsMarkovKernel (oneStepKernel env alg env.hr_meas) :=
    oneStepKernel_isMarkov _ _ _ hEnv hAlg
  haveI hTm_t : IsMarkovKernel (trajMeasureAux env alg env.hr_meas t) :=
    trajMeasureAux_isMarkov _ _ _ hEnv hAlg t
  haveI hTm_t1 : IsMarkovKernel (trajMeasureAux env alg env.hr_meas (t + 1)) :=
    trajMeasureAux_isMarkov _ _ _ hEnv hAlg (t + 1)
  haveI h_prob_dirac : IsProbabilityMeasure (Measure.dirac alg.σ₀) := inferInstance
  haveI h_prob_env : IsProbabilityMeasure env.μ₀ := env.hμ₀
  haveI h_prob_μ₀ : IsProbabilityMeasure μ₀ := inferInstance
  haveI h_prob_M_t : IsProbabilityMeasure (M t) := by
    dsimp [M]
    apply MeasureTheory.isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
    exact ae_of_all _ (fun _ => inferInstance)
  haveI h_prob_M_t1 : IsProbabilityMeasure (M (t + 1)) := by
    dsimp [M]
    apply MeasureTheory.isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
    exact ae_of_all _ (fun _ => inferInstance)
  have h_meas_1 : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) =>
      oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.2.2 = 1}) := by
    have h_set : MeasurableSet {step : Fin 2 × Unit × ℝ × Sig × Fin 2 | step.2.2.2.2 = 1} :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton 1)
    exact (Kernel.measurable_coe (oneStepKernel env alg env.hr_meas) h_set).comp measurable_snd
  have h_meas_2 : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) =>
      alg.act x.2.1 {1}) := by
    exact (Kernel.measurable_coe alg.act (measurableSet_singleton 1)).comp (measurable_fst.comp measurable_snd)
  have h_bind : M (t + 1) {x | x.2.2 = 1} =
      ∫⁻ σs, trajMeasureAux env alg env.hr_meas (t + 1) σs {x | x.2.2 = 1} ∂μ₀ := by
    dsimp [M]
    have h_set : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 | x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    exact Measure.bind_apply h_set (Kernel.measurable _).aemeasurable
  have h_step1 : ∫⁻ σs, trajMeasureAux env alg env.hr_meas (t + 1) σs {x | x.2.2 = 1} ∂μ₀ =
      ∫⁻ σs, ∫⁻ x, oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.2.2 = 1} ∂(trajMeasureAux env alg env.hr_meas t σs) ∂μ₀ := by
    apply lintegral_congr
    intro σs
    exact trajMeasureAux_next_state_prob p hp0 hp1 alg hAlg σs t 1
  have h_step2 : ∫⁻ σs, ∫⁻ x, oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.2.2 = 1} ∂(trajMeasureAux env alg env.hr_meas t σs) ∂μ₀ =
      ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.2.2 = 1} ∂(M t) := by
    dsimp [M]
    symm
    rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable h_meas_1.aemeasurable]
  have h_step3 : ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.2.2 = 1} ∂(M t) =
      ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, env.trans (x.2.2, a) {1} ∂(alg.act x.2.1) ∂(M t) := by
    apply lintegral_congr
    intro x
    exact oneStepKernel_peel_state p hp0 hp1 alg hAlg x.2
  have h_trans_bound : ∀ s a : Fin 2, env.trans (s, a) {1} ≤
      (if s = 1 then (1 : ℝ≥0∞) else 0) + (if a = 1 then ENNReal.ofReal p else 0) := by
    intro s a
    fin_cases s <;> fin_cases a
    · change env.trans (0, 0) {1} ≤ (if (0 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + if (0 : Fin 2) = 1 then ENNReal.ofReal p else 0
      have h_eq_LHS : env.trans (0, 0) {1} = 0 := by
        simp only [env, env₃, env₃_trans, Kernel.coe_mk]
        have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
        have h_00 : (0 : Fin 2) = 0 ↔ True := by decide
        simp only [h_01, ite_false, ite_true]
        have h_meas_set : MeasurableSet ({1} : Set (Fin 2)) := measurableSet_singleton 1
        rw [Measure.dirac_apply' _ h_meas_set]
        have h_mem : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) ↔ False := by decide
        simp
      have h_eq_RHS : (if (0 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + (if (0 : Fin 2) = 1 then ENNReal.ofReal p else 0) = 0 := by
        have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
        simp only [h_01, ite_false, add_zero]
      rw [h_eq_LHS, h_eq_RHS]
    · change env.trans (0, 1) {1} ≤ (if (0 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + if (1 : Fin 2) = 1 then ENNReal.ofReal p else 0
      have h_eq_LHS : env.trans (0, 1) {1} = ENNReal.ofReal p := by
        simp only [env, env₃, env₃_trans, Kernel.coe_mk]
        have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
        have h_10 : (1 : Fin 2) = 0 ↔ False := by decide
        simp only [h_01, h_10, ite_false]
        have h_meas : Measurable (fun b : Bool => if b then (1 : Fin 2) else 0) := measurable_of_finite _
        rw [Measure.map_apply h_meas (measurableSet_singleton 1)]
        have h_pre : (fun b : Bool => if b then (1 : Fin 2) else 0) ⁻¹' {1} = {true} := by
          ext b; cases b <;> simp
        rw [h_pre]
        rw [PMF.toMeasure_apply _ (measurableSet_singleton _)]  -- ← discharge case hs inline
        simp only [PMF.bernoulli_apply, tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_singleton_iff]
        have h_t : (true = true) ↔ True := by decide
        have h_f : (false = true) ↔ False := by decide
        simp
        rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hp0]
        rfl
      have h_eq_RHS : (if (0 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + (if (1 : Fin 2) = 1 then ENNReal.ofReal p else 0) = ENNReal.ofReal p := by
        have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
        have h_11 : (1 : Fin 2) = 1 ↔ True := by decide
        simp only [h_01, ite_false, ite_true, zero_add]
      rw [h_eq_LHS, h_eq_RHS]
    · change env.trans (1, 0) {1} ≤ (if (1 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + if (0 : Fin 2) = 1 then ENNReal.ofReal p else 0
      have h_eq_LHS : env.trans (1, 0) {1} = 1 := by
        simp only [env, env₃, env₃_trans, Kernel.coe_mk]
        have h_11 : (1 : Fin 2) = 1 ↔ True := by decide
        simp only [ite_true]
        exact Measure.dirac_apply_of_mem (Set.mem_singleton 1)
      have h_eq_RHS : (if (1 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + (if (0 : Fin 2) = 1 then ENNReal.ofReal p else 0) = 1 := by
        have h_11 : (1 : Fin 2) = 1 ↔ True := by decide
        have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
        simp only [h_01, ite_true, ite_false, add_zero]
      rw [h_eq_LHS, h_eq_RHS]
    · change env.trans (1, 1) {1} ≤ (if (1 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + if (1 : Fin 2) = 1 then ENNReal.ofReal p else 0
      have h_eq_LHS : env.trans (1, 1) {1} = 1 := by
        simp only [env, env₃, env₃_trans, Kernel.coe_mk]
        have h_11 : (1 : Fin 2) = 1 ↔ True := by decide
        simp only [ite_true]
        exact Measure.dirac_apply_of_mem (Set.mem_singleton 1)
      have h_eq_RHS : (if (1 : Fin 2) = 1 then (1 : ℝ≥0∞) else 0) + (if (1 : Fin 2) = 1 then ENNReal.ofReal p else 0) = 1 + ENNReal.ofReal p := by
        have h_11 : (1 : Fin 2) = 1 ↔ True := by decide
        simp only [ite_true]
      rw [h_eq_LHS, h_eq_RHS]
      exact le_add_right le_rfl
  have h_le_int : ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, env.trans (x.2.2, a) {1} ∂(alg.act x.2.1) ∂(M t) ≤
      ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, ((if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + (if a = 1 then ENNReal.ofReal p else 0)) ∂(alg.act x.2.1) ∂(M t) := by
    apply lintegral_mono
    intro x
    apply lintegral_mono
    intro a
    exact h_trans_bound x.2.2 a
  have h_split1 : ∀ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, ((if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + (if a = 1 then ENNReal.ofReal p else 0)) ∂(alg.act x.2.1) =
      (if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal p * alg.act x.2.1 {1} := by
    intro x
    have h1 : Measurable (fun a : Fin 2 => if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) := measurable_const
    rw [lintegral_add_left h1]
    have h_const : ∫⁻ a, (if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) ∂(alg.act x.2.1) = if x.2.2 = 1 then (1 : ℝ≥0∞) else 0 := by
      rw [lintegral_const]
      have h_prob : IsProbabilityMeasure (alg.act x.2.1) := inferInstance
      rw [h_prob.measure_univ, mul_one]
    rw [h_const]
    congr 1
    have h_ind_eq : (fun a : Fin 2 => if a = 1 then ENNReal.ofReal p else 0) =
        ({1} : Set (Fin 2)).indicator (fun _ => ENNReal.ofReal p) := by
      ext a; by_cases h : a = 1 <;> simp [h]
    rw [h_ind_eq, lintegral_indicator_const (measurableSet_singleton 1)]
  have h_split2 : ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ((if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal p * alg.act x.2.1 {1}) ∂(M t) =
      ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, (if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) ∂(M t) + ENNReal.ofReal p * ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, alg.act x.2.1 {1} ∂(M t) := by
    have h_set_x : MeasurableSet {x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) | x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    have hm1 : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) => if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite h_set_x measurable_const measurable_const
    rw [lintegral_add_left hm1]
    rw [lintegral_const_mul _ h_meas_2]
  have h_term1 : ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, (if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) ∂(M t) = M t {x | x.2.2 = 1} := by
    have h_ind_eq : (fun x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) => if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) =
        {x : ((Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2) | x.2.2 = 1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      ext x; simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [h_ind_eq]
    have h_set : MeasurableSet {x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2 | x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    rw [lintegral_indicator_const h_set, one_mul]
  have h_term2 : ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, alg.act x.2.1 {1} ∂(M t) = M (t + 1) {x | (x.1 (Fin.last t)).1 = 1} := by
    calc ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, alg.act x.2.1 {1} ∂(M t)
      _ = ∫⁻ σs, ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, alg.act x.2.1 {1} ∂(trajMeasureAux env alg env.hr_meas t σs) ∂μ₀ := by
        dsimp [M]
        symm
        rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable h_meas_2.aemeasurable]
      _ = ∫⁻ σs, trajMeasureAux env alg env.hr_meas (t + 1) σs {x | (x.1 (Fin.last t)).1 = 1} ∂μ₀ := by
        apply lintegral_congr
        intro σs
        rw [trajMeasureAux_action_prob p hp0 hp1 alg hAlg σs t 1]
        apply lintegral_congr
        intro x
        exact (oneStepKernel_peel_action p hp0 hp1 alg hAlg x.2 1).symm
      _ = M (t + 1) {x | (x.1 (Fin.last t)).1 = 1} := by
        dsimp [M]
        have h_set_meas : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 | (x.1 (Fin.last t)).1 = 1} :=
          measurable_fst.comp ((measurable_pi_apply (Fin.last t)).comp measurable_fst) (measurableSet_singleton 1)
        exact (Measure.bind_apply h_set_meas (Kernel.measurable _).aemeasurable).symm
  have h_ennreal_ineq : M (t + 1) {x | x.2.2 = 1} ≤ M t {x | x.2.2 = 1} + ENNReal.ofReal p * M (t + 1) {x | (x.1 (Fin.last t)).1 = 1} := by
    calc M (t + 1) {x | x.2.2 = 1}
      _ = ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, env.trans (x.2.2, a) {1} ∂(alg.act x.2.1) ∂(M t) := by rw [h_bind, h_step1, h_step2, h_step3]
      _ ≤ ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ∫⁻ a, ((if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + (if a = 1 then ENNReal.ofReal p else 0)) ∂(alg.act x.2.1) ∂(M t) := h_le_int
      _ = ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, ((if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal p * alg.act x.2.1 {1}) ∂(M t) := by apply lintegral_congr; exact h_split1
      _ = ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, (if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) ∂(M t) + ENNReal.ofReal p * ∫⁻ x : (Fin t → Fin 2 × Unit × ℝ) × Sig × Fin 2, alg.act x.2.1 {1} ∂(M t) := h_split2
      _ = M t {x | x.2.2 = 1} + ENNReal.ofReal p * M (t + 1) {x | (x.1 (Fin.last t)).1 = 1} := by rw [h_term1, h_term2]
  have h_toReal := ENNReal.toReal_mono ?_ h_ennreal_ineq
  swap
  · apply ENNReal.add_ne_top.mpr
    constructor
    · exact measure_ne_top _ _
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [ENNReal.toReal_add] at h_toReal
  · rw [ENNReal.toReal_mul] at h_toReal
    rw [ENNReal.toReal_ofReal hp0] at h_toReal
    exact h_toReal
  · exact measure_ne_top _ _
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

private lemma env₃_bridge_state_prob_le
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (C_tot : ℝ) (_hC : 0 ≤ C_tot)
    (h_bound : ∀ T', bridgeCumSeq (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas 1 T' ≤ C_tot)
    (T : ℕ) (t : Fin T) :
    ((trajMeasure (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T)
      {traj | (traj t).2.2 = 1}).toReal ≤ p * C_tot := by
  let env := env₃ p hp0.le hp1
  let μ₀ := (Measure.dirac alg.σ₀).prod env.μ₀
  let M := fun n => μ₀.bind (trajMeasureAux env alg env.hr_meas n)
  have h_M_eq : ((trajMeasure env alg env.hr_meas T) {traj | (traj t).2.2 = 1}).toReal =
                (M (t.val + 1) {x | (x.1 (Fin.last t.val)).2.2 = 1}).toReal := by
    haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0.le hp1
    have h_meas_set : MeasurableSet {traj' : Trajectory (Fin 2) Unit (t.val + 1) |
      (traj' (Fin.last t.val)).2.2 = 1} := by measurability
    have h_trunc := trajMeasure_truncation env alg env.hr_meas hEnv hAlg T (t.val + 1) t.isLt _ h_meas_set
    have h_set_eq : {traj : Trajectory (Fin 2) Unit T | (traj t).2.2 = 1} =
      {traj : Trajectory (Fin 2) Unit T |
        (fun i : Fin (t.val + 1) => traj (Fin.castLE t.isLt i)) ∈ {traj' : Trajectory (Fin 2) Unit (t.val + 1) |
          (traj' (Fin.last t.val)).2.2 = 1}} := by
      ext traj; simp only [Set.mem_setOf_eq];
      have h_cast : Fin.castLE t.isLt (Fin.last t.val) = t := Fin.ext (by simp)
      rw [h_cast]
    rw [h_set_eq, h_trunc]
    simp only [trajMeasure, M]
    have h_map : Measurable (Prod.fst : ((Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2) → (Fin (t.val + 1) → Fin 2 × Unit × ℝ)) := measurable_fst
    rw [Measure.map_apply h_map h_meas_set]
    rfl
  have h_reward_prob : M (t.val + 1) {x | (x.1 (Fin.last t.val)).2.2 = 1} = M t.val {x | x.2.2 = 1} := by
    dsimp [M]
    have h_set : MeasurableSet {x : (Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
      (x.1 (Fin.last t.val)).2.2 = 1} := by measurability
    rw [Measure.bind_apply h_set (Kernel.measurable _).aemeasurable]
    have h_inner : ∀ σs : Sig × Fin 2, trajMeasureAux env alg env.hr_meas (t.val + 1) σs {x |
      (x.1 (Fin.last t.val)).2.2 = 1} =
      ∫⁻ x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2, oneStepKernel env alg env.hr_meas x.2 {step |
        step.2.2.1 = 1} ∂(trajMeasureAux env alg env.hr_meas t.val σs) := by
      intro σs
      haveI hOsk : IsMarkovKernel (oneStepKernel env alg env.hr_meas) := oneStepKernel_isMarkov _ _ _ (env₃_isMarkov p hp0.le hp1) hAlg
      haveI hTm : IsMarkovKernel (trajMeasureAux env alg env.hr_meas t.val) := trajMeasureAux_isMarkov _ _ _ (env₃_isMarkov p hp0.le hp1) hAlg t.val
      simp only [trajMeasureAux]
      let f : ((Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2) × Fin 2 × Unit × ℝ × Sig × Fin 2 → (Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 :=
        fun x => (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)
      have h_f_meas : Measurable f := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.snoc_last]; fun_prop
          · intro j; simp only [Fin.snoc_castSucc]; fun_prop
        · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
                (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      have h_set_inner : MeasurableSet {x : (Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
        (x.1 (Fin.last t.val)).2.2 = 1} := h_set
      rw [Kernel.map_apply (hf := h_f_meas), Measure.map_apply h_f_meas h_set_inner]
      have h_pre : f ⁻¹' {x | (x.1 (Fin.last t.val)).2.2 = 1} = {x | x.2.2.2.1 = 1} := by
        ext x; simp only [f, Set.mem_preimage, Set.mem_setOf_eq, Fin.snoc_last]
      haveI : IsMarkovKernel ((oneStepKernel env alg env.hr_meas).comap (fun x : (Sig × Fin 2) × ((Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2) => x.2.2) (by measurability)) := Kernel.IsMarkovKernel.comap _ _
      rw [h_pre, Kernel.compProd_apply (by measurability)]
      apply lintegral_congr
      intro a
      simp
    rw [lintegral_congr h_inner]
    have h_set_step : MeasurableSet {step : Fin 2 × Unit × ℝ × Sig × Fin 2 | step.2.2.1 = 1} :=
      measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd)) measurable_const
    have h_meas_peel : Measurable (fun x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2 => oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.1 = 1}) :=
      (Kernel.measurable_coe (oneStepKernel env alg env.hr_meas) h_set_step).comp measurable_snd
    rw [← Measure.lintegral_bind (Kernel.measurable _).aemeasurable h_meas_peel.aemeasurable]
    have h_peel : ∀ x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2,
        oneStepKernel env alg env.hr_meas x.2 {step | step.2.2.1 = 1} = if x.2.2 = 1 then 1 else 0 := by
      intro x
      rw [oneStepKernel_peel_reward p hp0.le hp1 alg hAlg x.2]
      have h_r : ∀ a, (if env.r (x.2.2, a) = 1 then (1 : ℝ≥0∞) else 0) = if x.2.2 = 1 then (1 : ℝ≥0∞) else 0 := by
        intro a
        have h_iff : env.r (x.2.2, a) = 1 ↔ x.2.2 = 1 := env₃_reward_one_iff_state_one p hp0.le hp1 x.2.2 a
        by_cases h : x.2.2 = 1
        · have hr : env.r (x.2.2, a) = 1 := h_iff.mpr h
          rw [if_pos hr, if_pos h]
        · have hr : ¬ env.r (x.2.2, a) = 1 := mt h_iff.mp h
          rw [if_neg hr, if_neg h]
      haveI h_act_markov := hAlg.act_markov
      have h_prob : IsProbabilityMeasure (alg.act x.2.1) := inferInstance
      rw [lintegral_congr h_r, lintegral_const, h_prob.measure_univ, mul_one]
    rw [lintegral_congr h_peel]
    have h_ind_eq : (fun x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2 => if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) =
      {x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2 | x.2.2 = 1}.indicator (fun _ => 1) := by
      ext x; simp [Set.indicator_apply]
    have h_set_x : MeasurableSet {x : (Fin t.val → Fin 2 × Unit × ℝ) × Sig × Fin 2 | x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    rw [h_ind_eq, lintegral_indicator_const h_set_x, one_mul]
  rw [h_M_eq, h_reward_prob]
  have h_ind : ∀ k, (M k {x | x.2.2 = 1}).toReal ≤ p * ∑ i ∈ Finset.range k, (M (i + 1) {x | (x.1 (Fin.last i)).1 = 1}).toReal := by
    intro k
    induction k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
      dsimp [M]
      have h_set : MeasurableSet {x : (Fin 0 → Fin 2 × Unit × ℝ) × Sig × Fin 2 | x.2.2 = 1} :=
        measurable_snd.comp measurable_snd (measurableSet_singleton 1)
      rw [Measure.bind_apply h_set (Kernel.measurable _).aemeasurable]
      have h_map : ∀ σs : Sig × Fin 2, trajMeasureAux env alg env.hr_meas 0 σs {x | x.2.2 = 1} = if σs.2 = 1 then 1 else 0 := by
        intro σs
        have h_f : Measurable (fun σs : Sig × Fin 2 => ((Fin.elim0 : Fin 0 → Fin 2 × Unit × ℝ), σs)) := by measurability
        simp only [trajMeasureAux]
        rw [Kernel.map_apply (hf := h_f), Kernel.id_apply]
        rw [Measure.map_apply h_f h_set]
        have h_pre : (fun σs : Sig × Fin 2 => ((Fin.elim0 : Fin 0 → Fin 2 × Unit × ℝ), σs)) ⁻¹' {x | x.2.2 = 1} = {σs' : Sig × Fin 2 | σs'.2 = 1} := rfl
        rw [h_pre]
        have h_set_snd : MeasurableSet {σs' : Sig × Fin 2 | σs'.2 = 1} := measurable_snd (measurableSet_singleton 1)
        rw [Measure.dirac_apply' σs h_set_snd]
        simp [Set.indicator_apply]
      rw [lintegral_congr h_map]
      dsimp [μ₀, env, env₃]
      have h_prod : (Measure.dirac alg.σ₀).prod (Measure.dirac (0 : Fin 2)) = Measure.dirac (alg.σ₀, (0 : Fin 2)) := Measure.dirac_prod_dirac
      rw [h_prod, lintegral_dirac]
      have h01 : (0 : Fin 2) = 1 ↔ False := by decide
      simp [h01]
    | succ k ih =>
      have h_rec := env₃_state_recurrence_le p hp0.le hp1 alg hAlg k
      have h_sum_succ : ∑ i ∈ Finset.range (k + 1), (M (i + 1) {x | (x.1 (Fin.last i)).1 = 1}).toReal =
                        (∑ i ∈ Finset.range k, (M (i + 1) {x | (x.1 (Fin.last i)).1 = 1}).toReal) + (M (k + 1) {x | (x.1 (Fin.last k)).1 = 1}).toReal :=
        Finset.sum_range_succ _ k
      rw [h_sum_succ, mul_add]
      linarith [h_rec, ih]
  have h_bridge_def : ∑ i ∈ Finset.range t.val, (M (i + 1) {x | (x.1 (Fin.last i)).1 = 1}).toReal =
                      bridgeCumSeq env alg env.hr_meas 1 t.val := by
    dsimp [bridgeCumSeq]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have h_eq_enn := M_action_eq_trajMeasure p hp0.le hp1 alg hAlg t.val i
    exact congrArg ENNReal.toReal h_eq_enn

  have h_le := h_ind t.val
  have h_bound_val := h_bound t.val
  nlinarith [h_le, h_bridge_def, hp0, h_bound_val]

lemma env₃_algValue_ub
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig)
    (hAlg : AlgIsMarkov alg)
    (C_tot : ℝ) (hC : 0 ≤ C_tot)
    (h_bound : ∀ T', bridgeCumSeq (env₃ p hp0.le hp1) alg
                   (env₃ p hp0.le hp1).hr_meas 1 T' ≤ C_tot)
    (T : ℕ) :
    algValue' (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T ≤
    (T : ℝ) / 2 + (T : ℝ) * (p * C_tot) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0.le hp1) := env₃_isMarkov p hp0.le hp1
  set μ := trajMeasure (env₃ p hp0.le hp1) alg (env₃ p hp0.le hp1).hr_meas T
  haveI hPM : IsProbabilityMeasure μ := trajMeasure_isProbability _ _ _ hEnv hAlg T
  have h_abs : ∀ s a : Fin 2, |(env₃ p hp0.le hp1).r (s, a)| ≤ 1 := by
    intro s a; fin_cases s <;> fin_cases a <;> simp [env₃]; all_goals norm_num
  rw [algValue'_eq_sum _ _ _ hEnv hAlg h_abs]
  suffices h_step : ∀ t : Fin T, ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂μ ≤ (1 : ℝ) / 2 + p * C_tot by
    calc ∑ t : Fin T, ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂μ
        ≤ ∑ _t : Fin T, ((1 : ℝ) / 2 + p * C_tot) := Finset.sum_le_sum fun t _ => h_step t
      _ = (T : ℝ) / 2 + (T : ℝ) * (p * C_tot) := by
        simp [Finset.sum_const]
        ring
  intro t
  have h_dichot : ∀ᵐ traj ∂μ, (traj t).2.2 ≤ 1/2 ∨ (traj t).2.2 = 1 :=
    env₃_traj_reward_dichotomy p hp0 hp1 alg hAlg T t
  have h_prob : (μ {traj | (traj t).2.2 = 1}).toReal ≤ p * C_tot :=
    env₃_bridge_state_prob_le p hp0 hp1 alg hAlg C_tot hC h_bound T t
  have h_ms : MeasurableSet {traj : Trajectory (Fin 2) Unit T | (traj t).2.2 = 1} := by
    exact measurableSet_eq_fun ((measurable_snd.comp measurable_snd).comp (measurable_pi_apply t)) measurable_const
  have h_integ_t : Integrable (fun traj : Trajectory (Fin 2) Unit T => (traj t).2.2) μ := by
    apply Integrable.mono (integrable_const (1 : ℝ))
    · exact ((measurable_snd.comp measurable_snd).comp (measurable_pi_apply t)).aestronglyMeasurable
    · filter_upwards [trajMeasure_reward_le _ alg _ hEnv hAlg T t 1 h_abs] with traj h
      simp only [Real.norm_eq_abs, norm_one]
      exact h
  have h_ind_integ : Integrable (fun traj : Trajectory (Fin 2) Unit T => if (traj t).2.2 = (1 : ℝ) then (1 : ℝ) else 0) μ := by
    apply Integrable.mono (integrable_const (1 : ℝ))
    · exact (Measurable.ite h_ms measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards with traj; split_ifs <;> simp
  have h_ae_ineq : ∀ᵐ traj ∂μ, (traj t).2.2 ≤ (1 : ℝ)/2 + (if (traj t).2.2 = (1 : ℝ) then (1 : ℝ) else 0) := by
    filter_upwards [h_dichot] with traj ht
    rcases ht with h | h
    · have hne : (traj t).2.2 ≠ 1 := ne_of_lt (by linarith)
      simp only [if_neg hne, add_zero]; exact h
    · rw [h]; norm_num
  have h_ind_int : ∫ traj : Trajectory (Fin 2) Unit T, (if (traj t).2.2 = (1 : ℝ) then (1 : ℝ) else 0) ∂μ =
      (μ {traj | (traj t).2.2 = 1}).toReal := by
    have h_ind_eq : (fun traj : Trajectory (Fin 2) Unit T => if (traj t).2.2 = (1 : ℝ) then (1 : ℝ) else 0) =
        ({traj | (traj t).2.2 = (1 : ℝ)}).indicator (fun _ => (1 : ℝ)) := by
      ext traj; simp [Set.indicator_apply]
    rw [h_ind_eq]
    rw [integral_indicator h_ms]
    rw [integral_const]
    simp
    rfl
  have h_split : ∫ traj : Trajectory (Fin 2) Unit T, ((1:ℝ)/2 + if (traj t).2.2 = (1:ℝ) then (1:ℝ) else 0) ∂μ =
      ∫ _traj, (1:ℝ)/2 ∂μ + ∫ traj, (if (traj t).2.2 = (1:ℝ) then (1:ℝ) else 0) ∂μ :=
    integral_add (integrable_const _) h_ind_integ
  calc ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂μ
      ≤ ∫ traj : Trajectory (Fin 2) Unit T, ((1 : ℝ)/2 + if (traj t).2.2 = (1 : ℝ) then (1 : ℝ) else 0) ∂μ :=
          integral_mono_ae h_integ_t ((integrable_const _).add h_ind_integ) h_ae_ineq
    _ = (1 : ℝ)/2 + (μ {traj | (traj t).2.2 = 1}).toReal := by
          rw [h_split, integral_const, h_ind_int]
          simp
    _ ≤ (1 : ℝ)/2 + p * C_tot := by linarith [h_prob]

private lemma env₃_optAlg_stateMarginal
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (t : ℕ) :
    ((stateMarginal (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas t) {(1 : Fin 2)}).toReal =
    1 - (1 - p) ^ (t + 1) := by
  let env := env₃ p hp0.le hp1
  let alg := env₃_optAlg
  let hr := (env₃ p hp0.le hp1).hr_meas
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0.le hp1
  haveI hAlg : AlgIsMarkov alg := algIsDeterministic_isMarkov alg
  have h_meas_s : MeasurableSet {(1 : Fin 2)} := measurableSet_singleton 1
  have h_dirac_prod : (Measure.dirac alg.σ₀).prod env.μ₀ = Measure.dirac ((), (0 : Fin 2)) := by
    simp [env, env₃, alg, env₃_optAlg, Measure.dirac_prod_dirac]
  have h_state_marg : ∀ k, ((stateMarginal env alg hr k) {(1 : Fin 2)}) =
      trajMeasureAux env alg hr (k + 1) ((), (0 : Fin 2)) {x | x.2.2 = 1} := by
    intro k
    dsimp [stateMarginal]
    have h_meas_proj : Measurable (Prod.snd ∘ Prod.snd : ((Fin (k + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2) → Fin 2) :=
      measurable_snd.comp measurable_snd
    rw [Measure.map_apply h_meas_proj h_meas_s]
    have h_set_x : MeasurableSet {x : ((Fin (k + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2) | x.2.2 = 1} :=
      (measurable_snd.comp measurable_snd) h_meas_s
    have h_eq_set : (Prod.snd ∘ Prod.snd ⁻¹' {(1 : Fin 2)} : Set ((Fin (k + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2)) = {x | x.2.2 = 1} := rfl
    rw [h_eq_set]
    rw [Measure.bind_apply h_set_x (Kernel.measurable _).aemeasurable]
    rw [h_dirac_prod, lintegral_dirac]
  induction t with
  | zero =>
    simp only [zero_add, pow_one]
    rw [h_state_marg 0]
    rw [trajMeasureAux_next_state_prob p hp0.le hp1 alg hAlg ((), 0) 0 1]
    have h_tm_0 : trajMeasureAux env alg hr 0 ((), (0 : Fin 2)) = Measure.dirac ((Fin.elim0 : Fin 0 → Fin 2 × Unit × ℝ), ((), (0 : Fin 2))) := by
      have h_f : Measurable (fun σs : Unit × Fin 2 => ((Fin.elim0 : Fin 0 → Fin 2 × Unit × ℝ), σs)) :=
        Measurable.prodMk measurable_const measurable_id
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := h_f), Kernel.id_apply]
      rw [Measure.map_dirac]
    rw [h_tm_0, lintegral_dirac]
    rw [oneStepKernel_peel_state p hp0.le hp1 alg hAlg ((), 0)]
    dsimp [alg, env₃_optAlg]
    rw [lintegral_dirac]
    dsimp [env, env₃, env₃_trans]
    have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
    have h_10 : (1 : Fin 2) = 0 ↔ False := by decide
    simp
    have h_meas_b : Measurable (fun b : Bool => if b then (1 : Fin 2) else 0) := measurable_of_finite _
    rw [Measure.map_apply h_meas_b h_meas_s]
    have h_pre : (fun b : Bool => if b then (1 : Fin 2) else 0) ⁻¹' {1} = {true} := by
      ext b; cases b <;> simp
    rw [h_pre]
    rw [PMF.toMeasure_apply _ (measurableSet_singleton true)]
    simp only [PMF.bernoulli_apply, tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_singleton_iff]
    have h_t : (true = true) ↔ True := by decide
    have h_f : (false = true) ↔ False := by decide
    simp only [h_f, ite_true, ite_false, add_zero, cond_true]
    rfl
  | succ t ih =>
    rw [h_state_marg (t + 1)]
    rw [trajMeasureAux_next_state_prob p hp0.le hp1 alg hAlg ((), 0) (t + 1) 1]
    have h_inner : ∀ x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2,
        oneStepKernel env alg hr x.2 {step | step.2.2.2.2 = 1} =
        if x.2.2 = 1 then 1 else ENNReal.ofReal p := by
      intro x
      rw [oneStepKernel_peel_state p hp0.le hp1 alg hAlg x.2]
      dsimp [alg, env₃_optAlg]
      rw [lintegral_dirac]
      dsimp [env, env₃, env₃_trans]
      by_cases hx : x.2.2 = 1
      · simp [hx]
      · simp [hx]
        have h_meas_b : Measurable (fun b : Bool => if b then (1 : Fin 2) else 0) := measurable_of_finite _
        rw [Measure.map_apply h_meas_b h_meas_s]
        have h_pre : (fun b : Bool => if b then (1 : Fin 2) else 0) ⁻¹' {1} = {true} := by
          ext b; cases b <;> simp
        rw [h_pre]
        rw [PMF.toMeasure_apply _ (measurableSet_singleton true)]
        simp only [PMF.bernoulli_apply, tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_singleton_iff]
        have h_t : (true = true) ↔ True := by decide
        have h_f : (false = true) ↔ False := by decide
        simp only [h_f, ite_true, ite_false, add_zero, cond_true]
        symm
        rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hp0.le]
        rfl
    rw [lintegral_congr h_inner]
    have h_split : (fun x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 => if x.2.2 = 1 then (1 : ℝ≥0∞) else ENNReal.ofReal p) =
        fun x => ENNReal.ofReal p + (if x.2.2 = 1 then 1 - ENNReal.ofReal p else 0) := by
      ext x
      by_cases hx : x.2.2 = 1
      · simp only [hx, if_true]
        have h_le : ENNReal.ofReal p ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hp1
        exact (add_tsub_cancel_of_le h_le).symm
      · simp only [hx, if_false, add_zero]
    rw [h_split]
    have h_set_x : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 | x.2.2 = 1} :=
      (measurable_snd.comp measurable_snd) h_meas_s
    rw [lintegral_add_left measurable_const]
    rw [lintegral_const]
    haveI : IsMarkovKernel (trajMeasureAux env alg hr (t + 1)) := trajMeasureAux_isMarkov env alg hr hEnv hAlg (t + 1)
    have h_prob_tm : IsProbabilityMeasure (trajMeasureAux env alg hr (t + 1) ((), 0)) := inferInstance
    rw [h_prob_tm.measure_univ, mul_one]
    have h_ind_eq : (fun x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 => if x.2.2 = 1
       then 1 - ENNReal.ofReal p else 0) =
        {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 | x.2.2 = 1}.indicator (fun _ => 1 - ENNReal.ofReal p) := by
      ext x; simp [Set.indicator_apply]
    rw [h_ind_eq]
    rw [lintegral_indicator_const h_set_x]
    rw [← h_state_marg t]
    have h_sum_toReal : (ENNReal.ofReal p + (1 - ENNReal.ofReal p) * stateMarginal env alg hr t {(1 : Fin 2)}).toReal =
        p + (1 - p) * ((stateMarginal env alg hr t) {(1 : Fin 2)}).toReal := by
      rw [ENNReal.toReal_add]
      · rw [ENNReal.toReal_ofReal hp0.le]
        rw [ENNReal.toReal_mul]
        have h_sub : (1 - ENNReal.ofReal p).toReal = 1 - p := by
          have h_le : ENNReal.ofReal p ≤ 1 := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hp1
          rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
          rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le]
        rw [h_sub]
      · exact ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.sub_ne_top ENNReal.one_ne_top
        · haveI : IsProbabilityMeasure (stateMarginal env alg hr t) := stateMarginal_isProbability env alg hr hEnv hAlg t
          exact measure_ne_top _ _
    rw [h_sum_toReal, ih]
    calc p + (1 - p) * (1 - (1 - p) ^ (t + 1))
      _ = 1 - (1 - p) * (1 - p) ^ (t + 1) := by ring
      _ = 1 - (1 - p) ^ (t + 2) := by
        rw [pow_succ (1 - p) (t + 1)]
        ring

private lemma integral_eq_prob_of_zero_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (h_vals : ∀ᵐ x ∂μ, f x = 0 ∨ f x = 1) :
    ∫ x, f x ∂μ = (μ {x | f x = 1}).toReal := by
  have h_nn : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [h_vals] with x hx
    rcases hx with h0 | h1
    · rw [h0];
    · rw [h1]; exact zero_le_one
  rw [integral_eq_lintegral_of_nonneg_ae h_nn hf.aestronglyMeasurable]
  have h_lin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = μ {x | f x = 1} := by
    have h_lin_eq : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) = {x | f x = 1}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      filter_upwards [h_vals] with x hx
      rcases hx with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [lintegral_congr_ae h_lin_eq]
    have h_ms : MeasurableSet {x | f x = 1} := hf (measurableSet_singleton 1)
    rw [lintegral_indicator_const h_ms]
    simp
  rw [h_lin]

private lemma env₃_optAlg_traj_reward_zero_one
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (T : ℕ) (t : Fin T) :
    ∀ᵐ traj ∂(trajMeasure (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T),
      (traj t).2.2 = 0 ∨ (traj t).2.2 = 1 := by
  let env := env₃ p hp0.le hp1
  let alg := env₃_optAlg
  let hr := env.hr_meas
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0.le hp1
  haveI hAlg : AlgIsMarkov alg := algIsDeterministic_isMarkov alg
  haveI := hEnv.obs_markov
  haveI := hEnv.trans_markov
  haveI := hAlg.act_markov
  haveI := hAlg.update_markov
  haveI hOSK : IsMarkovKernel (oneStepKernel env alg hr) := oneStepKernel_isMarkov _ _ _ hEnv hAlg
  have hmf_step : Measurable (fun q : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Unit) =>
      (q.1.1.1.1, q.1.1.1.2, q.1.1.2, q.2, q.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set_step : MeasurableSet {x : Fin 2 × Unit × ℝ × Unit × Fin 2 |
x.2.2.1 = 0 ∨ x.2.2.1 = 1} := by
    have h_meas_r : Measurable (fun x : Fin 2 × Unit × ℝ × Unit × Fin 2 => x.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact MeasurableSet.union (measurableSet_eq_fun h_meas_r measurable_const) (measurableSet_eq_fun h_meas_r measurable_const)
  have hstep : ∀ σs : Unit × Fin 2,
      ∀ᵐ step ∂(oneStepKernel env alg hr σs),
        step.2.2.1 = 0 ∨ step.2.2.1 = 1 := by
    intro ⟨σ, s⟩
    simp only [oneStepKernel]
    rw [Kernel.map_apply (hf := hmf_step)]
    rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set_step]
    have hs4 : MeasurableSet {p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Unit) |
p.1.1.2 = 0 ∨ p.1.1.2 = 1} := by
      have hm : Measurable (fun p : ((((Fin 2 × Unit) × ℝ) × Fin 2) × Unit) => p.1.1.2) :=
        measurable_snd.comp (measurable_fst.comp measurable_fst)
      exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
    rw [Kernel.ae_compProd_iff hs4]
    have hs3_eq : (fun b : (((Fin 2 × Unit) × ℝ) × Fin 2) =>
        ∀ᵐ c ∂(alg.update.comap (fun x : (Unit × Fin 2) × (((Fin 2 × Unit) × ℝ) × Fin 2) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) ((σ, s), b)),
        (b, c).1.1.2 = 0 ∨ (b, c).1.1.2 = 1) =
      (fun b : (((Fin 2 × Unit) × ℝ) × Fin 2) => b.1.2 = 0 ∨ b.1.2 = 1) := by
      ext b
      simp only [Kernel.comap_apply]
      constructor
      · intro h
        have h_meas_univ := measure_univ (μ := alg.update (σ, b.1.1.1, b.1.1.2, b.1.2))
        by_cases hP : b.1.2 = 0 ∨ b.1.2 = 1
        · exact hP
        · have h_false : ∀ᵐ (_c : Unit) ∂alg.update (σ, b.1.1.1, b.1.1.2, b.1.2), False := h.mono (fun _ h_true => hP h_true)
          rw [ae_iff] at h_false
          have h_set_eq : {x : Unit |
¬False} = Set.univ := by ext; simp
          rw [h_set_eq] at h_false
          rw [h_meas_univ] at h_false
          exact False.elim (one_ne_zero h_false)
      · intro h
        exact ae_of_all _ (fun _ => h)
    rw [hs3_eq]
    have hs3 : MeasurableSet {p : (((Fin 2 × Unit) × ℝ) × Fin 2) |
p.1.2 = 0 ∨ p.1.2 = 1} := by
      have hm : Measurable (fun p : (((Fin 2 × Unit) × ℝ) × Fin 2) => p.1.2) :=
        measurable_snd.comp measurable_fst
      exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
    rw [Kernel.ae_compProd_iff hs3]
    have hs2_eq : (fun b : ((Fin 2 × Unit) × ℝ) =>
        ∀ᵐ c ∂(env.trans.comap (fun x : (Unit × Fin 2) × ((Fin 2 × Unit) × ℝ) => (x.1.2, x.2.1.1)) (by measurability) ((σ, s), b)),
        (b, c).1.2 = 0 ∨ (b, c).1.2 = 1) =
      (fun b : ((Fin 2 × Unit) × ℝ) => b.2 = 0 ∨ b.2 = 1) := by
      ext b
      simp only [Kernel.comap_apply]
      constructor
      · intro h
        have h_meas_univ := measure_univ (μ := env.trans (s, b.1.1))
        by_cases hP : b.2 = 0 ∨ b.2 = 1
        · exact hP
        · have h_false : ∀ᵐ (_c : Fin 2) ∂env.trans (s, b.1.1), False := h.mono (fun _ h_true => hP h_true)
          rw [ae_iff] at h_false
          have h_set_eq : {x : Fin 2 |
¬False} = Set.univ := by ext; simp
          rw [h_set_eq] at h_false
          rw [h_meas_univ] at h_false
          exact False.elim (one_ne_zero h_false)
      · intro h
        exact ae_of_all _ (fun _ => h)
    rw [hs2_eq]
    have hs2 : MeasurableSet {p : (Fin 2 × Unit) × ℝ |
p.2 = 0 ∨ p.2 = 1} := by
      have hm : Measurable (fun p : (Fin 2 × Unit) × ℝ => p.2) := measurable_snd
      exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
    rw [Kernel.ae_compProd_iff hs2]
    have h_rew_eq : (fun p : Fin 2 × Unit => ∀ᵐ c ∂(Kernel.deterministic (fun x : (Unit × Fin 2) × Fin 2 × Unit => env.r (x.1.2, x.2.1)) (hr.comp (by measurability)) ((σ, s), p)), c = 0 ∨ c = 1) =
      (fun p : Fin 2 × Unit => env.r (s, p.1) = 0 ∨ env.r (s, p.1) = 1) := by
      ext p
      simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
    rw [h_rew_eq]
    have hs1 : MeasurableSet {p : Fin 2 × Unit |
env.r (s, p.1) = 0 ∨ env.r (s, p.1) = 1} := by
      have hm : Measurable (fun p : Fin 2 × Unit => env.r (s, p.1)) := hr.comp (measurable_const.prodMk measurable_fst)
      exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
    rw [Kernel.ae_compProd_iff hs1]
    have h_obs_eq : (fun a : Fin 2 => ∀ᵐ o ∂(env.obs.comap (fun x : (Unit × Fin 2) × Fin 2 => (x.1.2, x.2)) (by measurability) ((σ, s), a)), env.r (s, a) = 0 ∨ env.r (s, a) = 1) =
      (fun a : Fin 2 => env.r (s, a) = 0 ∨ env.r (s, a) = 1) := by
      ext a
      simp only [Kernel.comap_apply]
      constructor
      · intro h
        haveI : IsProbabilityMeasure (env.obs (s, a)) := inferInstance
        have h_meas_univ := measure_univ (μ := env.obs (s, a))
        by_cases hP : env.r (s, a) = 0 ∨ env.r (s, a) = 1
        · exact hP
        · have h_false : ∀ᵐ (_o : Unit) ∂env.obs (s, a), False := h.mono (fun _ h_true => hP h_true)
          rw [ae_iff] at h_false
          have h_set_eq : {x : Unit |
¬False} = Set.univ := by ext; simp
          rw [h_set_eq] at h_false
          rw [h_meas_univ] at h_false
          exact False.elim (one_ne_zero h_false)
      · intro h
        exact ae_of_all _ (fun _ => h)
    rw [h_obs_eq]
    simp only [Kernel.comap_apply]
    have h_act : alg.act σ = Measure.dirac 1 := rfl
    rw [h_act]
    simp only [ae_dirac_eq, Filter.eventually_pure]
    dsimp [env, env₃]
    by_cases h : s = 1
    · right; simp [h]
    · left; simp [h]
  have h_aux : ∀ (T' : ℕ) (σs : Unit × Fin 2) (k : Fin T'),
      ∀ᵐ q ∂(trajMeasureAux env alg hr T' σs),
        (q.1 k).2.2 = 0 ∨ (q.1 k).2.2 = 1 := by
    intro T'
    induction T' with
    | zero => intro _ k; exact k.elim0
    | succ T' ih =>
      haveI := trajMeasureAux_isMarkov env alg hr hEnv hAlg T'
      intro σs k
      have hmf : Measurable (fun x : ((Fin T' → Fin 2 × Unit × ℝ) × (Unit × Fin 2)) ×
          (Fin 2 × Unit × ℝ × Unit × Fin 2) =>
          ((Fin.snoc x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1) : Fin (T' + 1) → Fin 2 × Unit × ℝ),
           (x.2.2.2.2.1, x.2.2.2.2.2))) := by
        apply Measurable.prodMk
        · apply measurable_pi_lambda; intro i
          refine Fin.lastCases ?_ ?_ i
          · simp; fun_prop
          · intro j; simp; fun_prop
        · fun_prop
      have h_set_fin (j : Fin (T' + 1)) :
          MeasurableSet {q : (Fin (T' + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
(q.1 j).2.2 = 0 ∨ (q.1 j).2.2 = 1} := by
        have h_meas_q : Measurable (fun q : (Fin (T' + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 => (q.1 j).2.2) :=
          (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply j).comp measurable_fst)
        exact MeasurableSet.union (measurableSet_eq_fun h_meas_q measurable_const) (measurableSet_eq_fun h_meas_q measurable_const)
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := hmf)]
      refine Fin.lastCases ?_ ?_ k
      · rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.last T'))]
        have h_set_inner : MeasurableSet {x : ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) × Fin 2 × Unit × ℝ × Unit × Fin 2 |
x.2.2.2.1 = 0 ∨ x.2.2.2.1 = 1} := by
          have hm : Measurable (fun x : ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) × Fin 2 × Unit × ℝ × Unit × Fin 2 => x.2.2.2.1) := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
          exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
        simp only [Fin.snoc_last]
        haveI : IsMarkovKernel ((oneStepKernel env alg hr).comap (fun x : (Unit × Fin 2) × ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) => x.2.2) (by measurability)) := Kernel.IsMarkovKernel.comap _ _
        refine (Kernel.ae_compProd_iff h_set_inner).mpr ?_
        apply ae_of_all; intro q
        simp only [Kernel.comap_apply]
        exact hstep q.2
      · intro j
        rw [MeasureTheory.ae_map_iff hmf.aemeasurable (h_set_fin (Fin.castSucc j))]
        have h_set_inner : MeasurableSet {x : ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) × Fin 2 × Unit × ℝ × Unit × Fin 2 |
(x.1.1 j).2.2 = 0 ∨ (x.1.1 j).2.2 = 1} := by
          have hm : Measurable (fun x : ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) × Fin 2 × Unit × ℝ × Unit × Fin 2 => (x.1.1 j).2.2) := (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
          exact MeasurableSet.union (measurableSet_eq_fun hm measurable_const) (measurableSet_eq_fun hm measurable_const)
        simp only [Fin.snoc_castSucc]
        haveI : IsMarkovKernel ((oneStepKernel env alg hr).comap (fun x : (Unit × Fin 2) × ((Fin T' → Fin 2 × Unit × ℝ) × Unit × Fin 2) => x.2.2) (by measurability)) := Kernel.IsMarkovKernel.comap _ _
        refine (Kernel.ae_compProd_iff h_set_inner).mpr ?_
        filter_upwards [ih σs j] with q hq
        exact ae_of_all _ fun _ => hq
  simp only [trajMeasure]
  have h_meas_t : Measurable (fun traj : Trajectory (Fin 2) Unit T => (traj t).2.2) :=
    (measurable_snd.comp measurable_snd).comp (measurable_pi_apply t)
  have h_set_traj : MeasurableSet {traj : Trajectory (Fin 2) Unit T |
(traj t).2.2 = 0 ∨ (traj t).2.2 = 1} :=
    MeasurableSet.union (measurableSet_eq_fun h_meas_t measurable_const) (measurableSet_eq_fun h_meas_t measurable_const)
  rw [MeasureTheory.ae_map_iff measurable_fst.aemeasurable h_set_traj]
  rw [ae_iff]
  change ((trajMeasureAux env alg hr T).toFun ∘ₘ
      (Measure.dirac alg.σ₀).prod env.μ₀)
    {a |
¬((a.1 t).2.2 = 0 ∨ (a.1 t).2.2 = 1)} = 0
  have h_set_not : MeasurableSet {a : (Fin T → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
¬((a.1 t).2.2 = 0 ∨ (a.1 t).2.2 = 1)} :=
    (measurable_fst h_set_traj).compl
  rw [Measure.bind_apply h_set_not (trajMeasureAux env alg hr T).measurable'.aemeasurable]
  calc ∫⁻ σs : Unit × Fin 2,
        (trajMeasureAux env alg hr T σs)
          {a |
¬((a.1 t).2.2 = 0 ∨ (a.1 t).2.2 = 1)}
        ∂((Measure.dirac alg.σ₀).prod env.μ₀)
      = ∫⁻ _ : Unit × Fin 2, 0 ∂((Measure.dirac alg.σ₀).prod env.μ₀) :=
          lintegral_congr fun σs => by rw [← ae_iff]; exact h_aux T σs t
    _ = 0 := lintegral_zero

private lemma trajMeasureAux_reward_prob
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (hAlg : AlgIsMarkov alg)
    (σs : Sig × Fin 2) (t : ℕ) :
    (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas (t + 1) σs {x | (x.1 (Fin.last t)).2.2 = 1}) =
    ∫⁻ x, oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas x.2 {step | step.2.2.1 = 1} ∂(trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t σs) := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0 hp1) := env₃_isMarkov p hp0 hp1
  haveI hOsk : IsMarkovKernel (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas) := oneStepKernel_isMarkov _ _ _ hEnv hAlg
  haveI hTm : IsMarkovKernel (trajMeasureAux (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas t) := trajMeasureAux_isMarkov _ _ _ hEnv hAlg t
  simp only [trajMeasureAux]
  have h_map : Measurable (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; fun_prop
      · intro j; simp only [Fin.snoc_castSucc]; fun_prop
    · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have h_set : MeasurableSet {x : (Fin (t + 1) → Fin 2 × Unit × ℝ) × Sig × Fin 2 |
    (x.1 (Fin.last t)).2.2 = 1} :=
    (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply (Fin.last t)).comp measurable_fst) (measurableSet_singleton 1)
  rw [Kernel.map_apply (hf := h_map), Measure.map_apply h_map h_set]
  have h_pre : (fun x : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) × (Fin 2 × Unit × ℝ × Sig × Fin 2) =>
    (Fin.snoc (α := fun _ => Fin 2 × Unit × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) ⁻¹' {x |
    (x.1 (Fin.last t)).2.2 = 1} =
    {x | x.2.2.2.1 = 1} := by ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Fin.snoc_last]
  haveI : IsMarkovKernel ((oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap
    (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability)) :=
    Kernel.IsMarkovKernel.comap _ _
  rw [h_pre, Kernel.compProd_apply (by measurability)]
  have h_inner : ∀ a : ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)),
      (oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas).comap (fun x : (Sig × Fin 2) × ((Fin t → Fin 2 × Unit × ℝ) × (Sig × Fin 2)) => x.2.2) (by measurability) (σs, a) {c |
      c.2.2.1 = 1} =
      oneStepKernel (env₃ p hp0 hp1) alg (env₃ p hp0 hp1).hr_meas a.2 {step |
      step.2.2.1 = 1} := by
    intro a; simp only [Kernel.comap_apply]
  simp

private lemma env₃_optAlg_traj_reward_prob (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (T : ℕ) (t : Fin T) :
    ((trajMeasure (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T) {traj | (traj t).2.2 = 1}).toReal =
    1 - (1 - p) ^ t.val := by
  let env := env₃ p hp0.le hp1
  let alg := env₃_optAlg
  let hr := env.hr_meas
  let μ₀ := (Measure.dirac alg.σ₀).prod env.μ₀
  let M := fun n => μ₀.bind (trajMeasureAux env alg hr n)
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0.le hp1
  haveI hAlg : AlgIsMarkov alg := algIsDeterministic_isMarkov alg
  have h_meas_set : MeasurableSet {traj' : Trajectory (Fin 2) Unit (t.val + 1) |
    (traj' (Fin.last t.val)).2.2 = 1} :=
    (measurable_snd.comp measurable_snd).comp (measurable_pi_apply (Fin.last t.val)) (measurableSet_singleton 1)
  have h_trunc := trajMeasure_truncation env alg hr hEnv hAlg T (t.val + 1) t.isLt _ h_meas_set
  have h_set_eq : {traj : Trajectory (Fin 2) Unit T |
    (traj t).2.2 = 1} =
    {traj : Trajectory (Fin 2) Unit T |
    (fun i : Fin (t.val + 1) => traj (Fin.castLE t.isLt i)) ∈ {traj' : Trajectory (Fin 2) Unit (t.val + 1) |
    (traj' (Fin.last t.val)).2.2 = 1}} := by
    ext traj;
    simp only [Set.mem_setOf_eq]
    have h_cast : Fin.castLE t.isLt (Fin.last t.val) = t := Fin.ext (by simp)
    rw [h_cast]
  have h_M_eq : ((trajMeasure env alg hr T) {traj | (traj t).2.2 = 1}) =
                (M (t.val + 1) {x | (x.1 (Fin.last t.val)).2.2 = 1}) := by
    rw [h_set_eq, h_trunc]
    simp only [trajMeasure, M]
    have h_map : Measurable (Prod.fst : ((Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2) → (Fin (t.val + 1) → Fin 2 × Unit × ℝ)) := measurable_fst
    rw [Measure.map_apply h_map h_meas_set]
    rfl
  have h_reward_prob : M (t.val + 1) {x |
    (x.1 (Fin.last t.val)).2.2 = 1} = M t.val {x |
    x.2.2 = 1} := by
    dsimp [M]
    have h_set : MeasurableSet {x : (Fin (t.val + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
      (x.1 (Fin.last t.val)).2.2 = 1} :=
      (measurable_snd.comp measurable_snd).comp ((measurable_pi_apply (Fin.last t.val)).comp measurable_fst) (measurableSet_singleton 1)
    rw [Measure.bind_apply h_set (Kernel.measurable _).aemeasurable]
    have h_inner : ∀ σs : Unit × Fin 2, trajMeasureAux env alg hr (t.val + 1) σs {x |
      (x.1 (Fin.last t.val)).2.2 = 1} =
      ∫⁻ x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2, oneStepKernel env alg hr x.2 {step |
      step.2.2.1 = 1} ∂(trajMeasureAux env alg hr t.val σs) := by
      intro σs
      exact trajMeasureAux_reward_prob p hp0.le hp1 alg hAlg σs t.val
    rw [lintegral_congr h_inner]
    have h_set_step : MeasurableSet {step : Fin 2 × Unit × ℝ × Unit × Fin 2 |
      step.2.2.1 = 1} :=
      measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd)) measurable_const
    have h_meas_peel : Measurable (fun x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2 => oneStepKernel env alg hr x.2 {step | step.2.2.1 = 1}) :=
      (Kernel.measurable_coe (oneStepKernel env alg hr) h_set_step).comp measurable_snd
    rw [← Measure.lintegral_bind (Kernel.measurable _).aemeasurable h_meas_peel.aemeasurable]
    have h_peel : ∀ x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2,
      oneStepKernel env alg hr x.2 {step | step.2.2.1 = 1} = if x.2.2 = 1 then 1 else 0 := by
      intro x
      rw [oneStepKernel_peel_reward p hp0.le hp1 alg hAlg x.2]
      have h_r : ∀ a, (if env.r (x.2.2, a) = 1 then (1 : ℝ≥0∞) else 0) = if x.2.2 = 1 then (1 : ℝ≥0∞) else 0 := by
        intro a
        have h_iff : env.r (x.2.2, a) = 1 ↔ x.2.2 = 1 := env₃_reward_one_iff_state_one p hp0.le hp1 x.2.2 a
        by_cases h : x.2.2 = 1
        · have hr : env.r (x.2.2, a) = 1 := h_iff.mpr h
          rw [if_pos hr, if_pos h]
        · have hr : ¬ env.r (x.2.2, a) = 1 := mt h_iff.mp h
          rw [if_neg hr, if_neg h]
      haveI h_act_markov := hAlg.act_markov
      have h_prob : IsProbabilityMeasure (alg.act x.2.1) := inferInstance
      rw [lintegral_congr h_r, lintegral_const, h_prob.measure_univ, mul_one]
    rw [lintegral_congr h_peel]
    have h_ind_eq : (fun x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2 => if x.2.2 = 1 then (1 : ℝ≥0∞) else 0) =
      {x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
      x.2.2 = 1}.indicator (fun _ => 1) := by
      ext x;
      simp [Set.indicator_apply]
    have h_set_x : MeasurableSet {x : (Fin t.val → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
      x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    rw [h_ind_eq, lintegral_indicator_const h_set_x, one_mul]
  rw [h_M_eq, h_reward_prob]
  cases t.val with
  | zero =>
    dsimp [M]
    have h_meas_0 : MeasurableSet {x : (Fin 0 → Fin 2 × Unit × ℝ) × Unit × Fin 2 |
      x.2.2 = 1} :=
      measurable_snd.comp measurable_snd (measurableSet_singleton 1)
    rw [Measure.bind_apply h_meas_0 (Kernel.measurable _).aemeasurable]
    have h_int_0 : ∀ σs : Unit × Fin 2, trajMeasureAux env alg hr 0 σs {x |
      x.2.2 = 1} = if σs.2 = 1 then 1 else 0 := by
      intro σs
      have h_f : Measurable (fun σs : Unit × Fin 2 => ((Fin.elim0 : Fin 0 → Fin 2 × Unit × ℝ), σs)) := by measurability
      simp only [trajMeasureAux]
      rw [Kernel.map_apply (hf := h_f), Kernel.id_apply]
      rw [Measure.map_dirac]
      rw [MeasureTheory.Measure.dirac_apply' _ h_meas_0]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rfl
    rw [lintegral_congr h_int_0]
    dsimp [μ₀, env, env₃, alg, env₃_optAlg]
    rw [Measure.dirac_prod_dirac]
    rw [lintegral_dirac]
    have h_01 : (0 : Fin 2) = 1 ↔ False := by decide
    simp [h_01]
  | succ k =>
    have h_sm : ((stateMarginal env alg hr k) {(1 : Fin 2)}).toReal = 1 - (1 - p) ^ (k + 1) :=
      env₃_optAlg_stateMarginal p hp0 hp1 k
    have h_M_eq_sm : M (k + 1) {x |
      x.2.2 = 1} = stateMarginal env alg hr k {(1 : Fin 2)} := by
      dsimp [stateMarginal, M]
      have h_meas_s : MeasurableSet {(1 : Fin 2)} := measurableSet_singleton 1
      have h_meas_proj : Measurable (Prod.snd ∘ Prod.snd : ((Fin (k + 1) → Fin 2 × Unit × ℝ) × Unit × Fin 2) → Fin 2) :=
        measurable_snd.comp measurable_snd
      rw [Measure.map_apply h_meas_proj h_meas_s]
      rfl
    rw [h_M_eq_sm]
    exact h_sm

lemma env₃_optAlg_expected_reward
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (T : ℕ) (t : Fin T) :
    ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂trajMeasure (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T =
    1 - (1 - p) ^ t.val := by
  let env := env₃ p hp0.le hp1
  let alg := env₃_optAlg
  let hr := env.hr_meas
  haveI hEnv : EnvIsMarkov env := env₃_isMarkov p hp0.le hp1
  haveI hAlg : AlgIsMarkov alg := algIsDeterministic_isMarkov alg
  haveI hProb : IsProbabilityMeasure (trajMeasure env alg hr T) :=
    trajMeasure_isProbability env alg hr hEnv hAlg T
  have h_zero_one : ∀ᵐ traj ∂(trajMeasure env alg hr T), (traj t).2.2 = 0 ∨ (traj t).2.2 = 1 :=
    env₃_optAlg_traj_reward_zero_one p hp0 hp1 T t
  have h_meas : Measurable (fun traj : Trajectory (Fin 2) Unit T => (traj t).2.2) :=
    (measurable_snd.comp measurable_snd).comp (measurable_pi_apply t)
  have h_integral := integral_eq_prob_of_zero_one (trajMeasure env alg hr T) (fun traj => (traj t).2.2) h_meas h_zero_one
  change ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂(trajMeasure env alg hr T) = 1 - (1 - p) ^ t.val
  rw [h_integral]
  exact env₃_optAlg_traj_reward_prob p hp0 hp1 T t

lemma env₃_optAlg_algValue_lb (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (T : ℕ) :
    (T : ℝ) - 1 / p ≤ algValue' (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T := by
  haveI hEnv : EnvIsMarkov (env₃ p hp0.le hp1) := env₃_isMarkov p hp0.le hp1
  haveI hAlg : AlgIsMarkov env₃_optAlg := algIsDeterministic_isMarkov env₃_optAlg
  have h_abs : ∀ s a : Fin 2, |(env₃ p hp0.le hp1).r (s, a)| ≤ 1 := by
    intro s a; fin_cases s <;> fin_cases a <;> simp [env₃]; all_goals norm_num
  rw [algValue'_eq_sum _ _ _ hEnv hAlg h_abs]
  have h_step_rew : ∀ t : Fin T, ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂(trajMeasure (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T) = 1 - (1 - p) ^ t.val := by
    intro t
    exact env₃_optAlg_expected_reward p hp0 hp1 T t
  have h_sum_eval : ∑ t : Fin T, (1 - (1 - p) ^ t.val) = (T : ℝ) - ∑ t : Fin T, (1 - p) ^ t.val := by
    rw [Finset.sum_sub_distrib]
    simp
  have hp_neq : 1 - p ≠ 1 := by linarith
  have h_geom : ∑ t : Fin T, (1 - p) ^ t.val = (1 - (1 - p) ^ T) / p := by
    rw [Finset.sum_fin_eq_sum_range]
    have h_congr : (∑ i ∈ Finset.range T, if h : i < T then (1 - p) ^ (⟨i, h⟩ : Fin T).val else 0) = ∑ i ∈ Finset.range T, (1 - p) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    rw [h_congr]
    have h_sum := geom_sum_eq hp_neq T
    calc ∑ i ∈ Finset.range T, (1 - p) ^ i
      _ = ((1 - p) ^ T - 1) / (1 - p - 1) := h_sum
      _ = (1 - (1 - p) ^ T) / p := by
        have h_num : (1 - p) ^ T - 1 = -(1 - (1 - p) ^ T) := by ring
        have h_den : 1 - p - 1 = -p := by ring
        rw [h_num, h_den, div_neg, neg_div, neg_neg]
  calc (T : ℝ) - 1 / p
    _ ≤ (T : ℝ) - (1 - (1 - p) ^ T) / p := by
      apply sub_le_sub_left
      have h_pow_nonneg : 0 ≤ (1 - p) ^ T := pow_nonneg (by linarith) T
      exact div_le_div_of_nonneg_right (by linarith) hp0.le
    _ = (T : ℝ) - ∑ t : Fin T, (1 - p) ^ t.val := by rw [h_geom]
    _ = ∑ t : Fin T, (1 - (1 - p) ^ t.val) := h_sum_eval.symm
    _ = ∑ t : Fin T, ∫ traj : Trajectory (Fin 2) Unit T, (traj t).2.2 ∂(trajMeasure (env₃ p hp0.le hp1) env₃_optAlg (env₃ p hp0.le hp1).hr_meas T) := by
      apply Finset.sum_congr rfl
      intro t _
      exact (h_step_rew t).symm

end EnvX3

-- ENVIRONMENT E₄

section EnvX4

noncomputable def env₄ : SixPrimitives.Env Unit (Fin 2) Unit where
  trans    := Kernel.const _ (Measure.dirac ())
  obs      := Kernel.const _ (Measure.dirac ())
  r        := fun (_, a) => if a = 0 then 1 else 0
  hr_meas  := measurable_of_finite _
  μ₀       := Measure.dirac ()
  hμ₀      := inferInstance

noncomputable def env₄_isDet : EnvIsDeterministic env₄ where
  s₀ := ()
  μ₀_eq := rfl
  transFn := fun _ => ()
  transFn_meas := measurable_const
  trans_eq := fun _ => rfl
  obsFn := fun _ => ()
  obsFn_meas := measurable_const
  obs_eq := fun _ => rfl

theorem env₄_hasP₄ : SixPrimitives.HasP₄ env₄ () (0 : Fin 2) SixPrimitives.VisitFrequencyAtLeast := by
  refine ⟨1, 1, one_pos, one_pos, ?_, ?_⟩
  · intro a ha
    fin_cases a
    · exact absurd rfl ha
    · simp [env₄]
  · exact SixPrimitives.visitFrequencyAtLeast_of_unique_state env₄ env₄_isDet 1 le_rfl

theorem env₄_inClassC : SixPrimitives.InClassC env₄ SixPrimitives.VisitFrequencyAtLeast :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨(), 0, env₄_hasP₄⟩)))

noncomputable def env₄_optAlg : SixPrimitives.Algorithm (Fin 2) Unit Unit where
  act := Kernel.const _ (Measure.dirac 0)
  update := Kernel.const _ (Measure.dirac ())
  σ₀ := ()

instance : AlgIsDeterministic env₄_optAlg where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma env₄_optValue (T : ℕ) : SixPrimitives.optValue env₄ T = T := by
  have hEnv := envIsDeterministic_isMarkov env₄ env₄_isDet
  have hAlg := algIsDeterministic_isMarkov env₄_optAlg
  have h_prob : IsProbabilityMeasure (trajMeasure env₄ env₄_optAlg env₄.hr_meas T) :=
    trajMeasure_isProbability env₄ env₄_optAlg env₄.hr_meas hEnv hAlg T
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' env₄ alg env₄.hr_meas T} → v ≤ (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Unit) (a : Fin 2), |env₄.r (s, a)| ≤ 1 := by
      intro s a; simp only [env₄]; split_ifs <;> norm_num
    have h_val := algValue'_le_const env₄ alg env₄.hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T 1 h_rew_bound
    simp only [mul_one] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' env₄ env₄_optAlg env₄.hr_meas T
      use Unit, inferInstance, inferInstance, inferInstance, env₄_optAlg, hAlg.act_markov, hAlg.update_markov
    · exact h_bound
  · apply le_csSup
    · use T; exact h_bound
    · use Unit, inferInstance, inferInstance, inferInstance, env₄_optAlg, hAlg.act_markov, hAlg.update_markov
      symm
      dsimp [Phase2.algValue']
      have h_rew : ∀ᵐ traj ∂(trajMeasure env₄ env₄_optAlg env₄.hr_meas T),
        ∑ t : Fin T, (traj t).2.2 = (T : ℝ) := by
        have h_eq_unit : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure env₄ env₄_optAlg env₄.hr_meas T),
            (ω t).2.2 = env₄.r ((), (ω t).1) :=
          fun t => trajMeasure_step_reward_eq_unit env₄ env₄_optAlg env₄.hr_meas env₄_isDet.toTrans hEnv hAlg T t.1 t.2
        have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure env₄ env₄_optAlg env₄.hr_meas T),
            (ω t).1 = 0 := by
          intro t
          filter_upwards [traj_action_ae_eq_actFn env₄ env₄_optAlg env₄.hr_meas t.1 T t.2 hEnv] with ω hω
          exact hω
        have h_all : ∀ᵐ ω ∂(trajMeasure env₄ env₄_optAlg env₄.hr_meas T),
            ∀ t : Fin T, (ω t).2.2 = 1 := by
          rw [ae_all_iff]
          intro t
          filter_upwards [h_eq_unit t, h_act t] with ω h_unit h_act_eq
          rw [h_unit, h_act_eq]
          rfl
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1 : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) := by simp
      have h_int_eq : ∫ (traj : Trajectory (Fin 2) Unit T), ∑ t : Fin T, (traj t).2.2 ∂trajMeasure env₄ env₄_optAlg env₄.hr_meas T = ∫ (traj : Trajectory (Fin 2) Unit T), (T : ℝ) ∂trajMeasure env₄ env₄_optAlg env₄.hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp

end EnvX4

--ENVIRONMENT E₅

section EnvX5

def feasSet₅ : Set ℝ := Set.Icc 0 (1/3) ∪ Set.Icc (2/3) 1
def penalty₅ : ℝ := 1

open Classical in
noncomputable def env₅ : SixPrimitives.Env Unit ℝ Unit where
  trans    := Kernel.const _ (Measure.dirac ())
  obs      := Kernel.const _ (Measure.dirac ())
  r        := fun (_, a) =>
    if a ∈ feasSet₅ then max 0 (1 - 3 * min (|a|) (|1 - a|)) else -penalty₅
  hr_meas  := by
    have hS : MeasurableSet (feasSet₅ : Set ℝ) := by
      simp only [feasSet₅]
      exact ((isClosed_Icc (a := (0 : ℝ)) (b := 1/3)).union
             (isClosed_Icc (a := (2/3 : ℝ)) (b := 1))).measurableSet
    apply Measurable.ite (hS.preimage measurable_snd)
    · exact measurable_const.max
        (measurable_const.sub
          (measurable_const.mul
            (measurable_snd.norm.min
              (measurable_const.sub measurable_snd).norm)))
    · exact measurable_const
  μ₀       := Measure.dirac ()
  hμ₀      := inferInstance

theorem env₅_hasP₅ : SixPrimitives.HasP₅ env₅ feasSet₅ penalty₅ := by
  refine ⟨by norm_num [penalty₅], ?_, ?_⟩
  · constructor
    · exact Set.subset_univ _
    · intro h
      have h12 : (1/2 : ℝ) ∈ feasSet₅ := h (Set.mem_univ _)
      norm_num [feasSet₅, Set.mem_union, Set.mem_Icc] at h12
  · intro _ a ha
    simp only [env₅, if_neg ha, le_refl]

theorem env₅_inClassC : SixPrimitives.InClassC env₅ SixPrimitives.VisitFrequencyAtLeast :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨feasSet₅, penalty₅, env₅_hasP₅⟩))))

noncomputable def env₅_isDet : EnvIsDeterministic env₅ where
  s₀ := ()
  μ₀_eq := rfl
  transFn := fun _ => ()
  transFn_meas := measurable_const
  trans_eq := fun _ => rfl
  obsFn := fun _ => ()
  obsFn_meas := measurable_const
  obs_eq := fun _ => rfl

noncomputable def env₅_optAlg : SixPrimitives.Algorithm ℝ Unit Unit where
  act := Kernel.const _ (Measure.dirac 0)
  update := Kernel.const _ (Measure.dirac ())
  σ₀ := ()

instance : AlgIsDeterministic env₅_optAlg where
  actFn := fun _ => 0
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

lemma env₅_optValue (T : ℕ) : SixPrimitives.optValue env₅ T = T := by
  have hEnv := envIsDeterministic_isMarkov env₅ env₅_isDet
  have hAlg := algIsDeterministic_isMarkov env₅_optAlg
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm ℝ Unit Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' env₅ alg env₅.hr_meas T} → v ≤ (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Unit) (a : ℝ), |env₅.r (s, a)| ≤ 1 := by
      intro s a
      dsimp [env₅, penalty₅]
      split_ifs
      · have h_min : 0 ≤ min |a| |1 - a| := le_min (abs_nonneg _) (abs_nonneg _)
        have h_max : max 0 (1 - 3 * min |a| |1 - a|) ≤ 1 := by
          apply max_le (by norm_num)
          linarith
        rw [abs_of_nonneg (le_max_left _ _)]
        exact h_max
      · norm_num
    have h_val := algValue'_le_const env₅ alg env₅.hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T 1 h_rew_bound
    simp only [mul_one] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' env₅ env₅_optAlg env₅.hr_meas T
      use Unit, inferInstance, inferInstance, inferInstance, env₅_optAlg, hAlg.act_markov, hAlg.update_markov
    · exact h_bound
  · apply le_csSup
    · use T; exact h_bound
    · use Unit, inferInstance, inferInstance, inferInstance, env₅_optAlg, hAlg.act_markov, hAlg.update_markov
      symm
      dsimp [Phase2.algValue']
      have h_eq_step : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure env₅ env₅_optAlg env₅.hr_meas T),
          (ω t).2.2 = env₅.r ((), (ω t).1) :=
        fun t => trajMeasure_step_reward_eq_unit env₅ env₅_optAlg env₅.hr_meas env₅_isDet.toTrans hEnv hAlg T t.1 t.2
      have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure env₅ env₅_optAlg env₅.hr_meas T),
          (ω t).1 = 0 := by
        intro t
        filter_upwards [traj_action_ae_eq_actFn env₅ env₅_optAlg env₅.hr_meas t.1 T t.2 hEnv] with ω hω
        exact hω
      have h_all : ∀ᵐ ω ∂(trajMeasure env₅ env₅_optAlg env₅.hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1 := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_step t, h_act t] with ω h_unit h_act_eq
        rw [h_unit, h_act_eq]
        dsimp [env₅]
        have h_feas : (0 : ℝ) ∈ feasSet₅ := by
          simp [feasSet₅]
        norm_num [h_feas]
      have h_rew : ∀ᵐ traj ∂(trajMeasure env₅ env₅_optAlg env₅.hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1 : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) := by simp
      haveI : IsProbabilityMeasure (trajMeasure env₅ env₅_optAlg env₅.hr_meas T) :=
        trajMeasure_isProbability env₅ env₅_optAlg env₅.hr_meas hEnv hAlg T
      have h_int_eq : ∫ (traj : Trajectory ℝ Unit T), ∑ t : Fin T, (traj t).2.2 ∂trajMeasure env₅ env₅_optAlg env₅.hr_meas T = ∫ (traj : Trajectory ℝ Unit T), (T : ℝ) ∂trajMeasure env₅ env₅_optAlg env₅.hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp

end EnvX5

-- ENVIRONMENT E₆

section EnvX6

open Classical in
noncomputable def env₆_family (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4)
    (n : ℕ) : SixPrimitives.Env Unit (Fin 2) Bool :=
  let postCP : Prop := T / 2 < n
  { trans   := Kernel.const _ (Measure.dirac ())
    obs     := { toFun := fun (_, a) =>
                   if (a = (0 : Fin 2)) = postCP
                   then bernoulliMeasure (1/2 + Δ) (by linarith) (by linarith)
                   else bernoulliMeasure (1/2 - Δ) (by linarith [hΔ4]) (by linarith [hΔ0])
                 measurable' := measurable_of_finite _ }
    r       := fun (_, a) =>
                 if (a = (0 : Fin 2)) = postCP then 1/2 + Δ else 1/2 - Δ
    hr_meas := measurable_of_finite _
    μ₀      := Measure.dirac ()
    hμ₀     := inferInstance }

theorem env₆_hasP₆ (T : ℕ) (_hT : 0 < T) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    SixPrimitives.HasP₆ (env₆_family T Δ hΔ0 hΔ4) (T / 2) := by
  refine ⟨(), 0, Or.inl ?_⟩
  simp only [env₆_family]
  simp only [show ¬ (T / 2 < T / 2) from Nat.lt_irrefl _,
             show T / 2 < T / 2 + 1 from Nat.lt_succ_self _]
  norm_num
  linarith

theorem env₆_inClassC (T : ℕ) (hT : 0 < T) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    SixPrimitives.InClassC (env₆_family T Δ hΔ0 hΔ4 0) SixPrimitives.VisitFrequencyAtLeast := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨env₆_family T Δ hΔ0 hΔ4, T / 2, rfl, env₆_hasP₆ T hT Δ hΔ0 hΔ4⟩))))

lemma env₆_post_changepoint_arm_swap (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4)
    (n : ℕ) (hn : T / 2 < n) :
    (env₆_family T Δ hΔ0 hΔ4 n).r ((), 0) = 1/2 + Δ ∧
    (env₆_family T Δ hΔ0 hΔ4 n).r ((), 1) = 1/2 - Δ := by
  dsimp [env₆_family]
  constructor
  · simp [hn]
  · have h1 : (1 : Fin 2) ≠ 0 := by decide
    simp [h1, hn]

instance env₆_isMarkov (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) (n : ℕ) : EnvIsMarkov (env₆_family T Δ hΔ0 hΔ4 n) where
  trans_markov := ⟨fun _ => by dsimp [env₆_family]; infer_instance⟩
  obs_markov := ⟨fun ⟨_, a⟩ => by
    change IsProbabilityMeasure (if (a = (0 : Fin 2)) = (T / 2 < n) then _ else _)
    split_ifs
    · exact bernoulliMeasure_isProbability _ _ _
    · exact bernoulliMeasure_isProbability _ _ _⟩

noncomputable def env₆_optAlg : SixPrimitives.Algorithm (Fin 2) Bool Unit where
  act := Kernel.const _ (Measure.dirac 1)
  update := Kernel.const _ (Measure.dirac ())
  σ₀ := ()

instance env₆_optAlg_isDet : AlgIsDeterministic env₆_optAlg where
  actFn := fun _ => 1
  actFn_meas := measurable_const
  act_eq := fun _ => rfl
  updateFn := fun _ => ()
  updateFn_meas := measurable_const
  update_eq := fun _ => rfl

noncomputable def env₆_transDet (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) (n : ℕ) : TransIsDeterministic (env₆_family T Δ hΔ0 hΔ4 n) where
  s₀ := ()
  μ₀_eq := rfl
  transFn := fun _ => ()
  transFn_meas := measurable_const
  trans_eq := fun _ => rfl

lemma env₆_optValue (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    SixPrimitives.optValue (env₆_family T Δ hΔ0 hΔ4 0) T = (1/2 + Δ) * T := by
  have hEnv := env₆_isMarkov T Δ hΔ0 hΔ4 0
  have hAlg := algIsDeterministic_isMarkov env₆_optAlg
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' (env₆_family T Δ hΔ0 hΔ4 0) alg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T} → v ≤ (1 / 2 + Δ) * (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : Unit) (a : Fin 2), |(env₆_family T Δ hΔ0 hΔ4 0).r (s, a)| ≤ 1 / 2 + Δ := by
      intro s a
      dsimp [env₆_family]
      split_ifs
      · rw [abs_of_pos (by linarith)]
      · rw [abs_of_pos (by linarith)]
        linarith
    have h_val := algValue'_le_const (env₆_family T Δ hΔ0 hΔ4 0) alg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T (1 / 2 + Δ) h_rew_bound
    rw [mul_comm] at h_val
    exact h_val
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T
      use Unit, inferInstance, inferInstance, inferInstance, env₆_optAlg, hAlg.act_markov, hAlg.update_markov
    · exact h_bound
  · apply le_csSup
    · use (1 / 2 + Δ) * T; exact h_bound
    · use Unit, inferInstance, inferInstance, inferInstance, env₆_optAlg, hAlg.act_markov, hAlg.update_markov
      symm
      dsimp [Phase2.algValue']
      have hTransDet := env₆_transDet T Δ hΔ0 hΔ4 0
      have h_eq_unit : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T),
          (ω t).2.2 = (env₆_family T Δ hΔ0 hΔ4 0).r ((), (ω t).1) :=
        fun t => trajMeasure_step_reward_eq_unit (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas hTransDet hEnv hAlg T t.1 t.2
      have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T),
          (ω t).1 = 1 := by
        intro t
        filter_upwards [traj_action_ae_eq_actFn (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas t.1 T t.2 hEnv] with ω hω
        exact hω
      have h_all : ∀ᵐ ω ∂(trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1/2 + Δ := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_unit t, h_act t] with ω h_unit h_act_eq
        rw [h_unit, h_act_eq]
        dsimp [env₆_family]
      have h_rew : ∀ᵐ traj ∂(trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) * (1/2 + Δ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1/2 + Δ : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) * (1/2 + Δ) := by
            simp
            ring
      haveI : IsProbabilityMeasure (trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T) :=
        trajMeasure_isProbability (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas hEnv hAlg T
      have h_int_eq : ∫ (traj : Trajectory (Fin 2) Bool T), ∑ t : Fin T, (traj t).2.2 ∂trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T = ∫ (traj : Trajectory (Fin 2) Bool T), (T : ℝ) * (1/2 + Δ) ∂trajMeasure (env₆_family T Δ hΔ0 hΔ4 0) env₆_optAlg (env₆_family T Δ hΔ0 hΔ4 0).hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp [mul_comm]

end EnvX6

-- COMPOUND ENVIRONMENT E*

section EnvStar

structure StarParam where
  Δ   : ℝ
  M   : ℝ
  T   : ℕ
  Θ   : Fin 2
  hΔ0 : 0 < Δ
  hΔ4 : Δ ≤ 1/4
  hM  : 0 < M
  hT  : 0 < T

noncomputable def pBridge (sp : StarParam) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.sqrt sp.T)

noncomputable def envStar_family (sp : StarParam) (n : ℕ) : SixPrimitives.Env (Fin 3) (Fin 7) (Fin 3) where
  trans := {
    toFun := fun (s, a) =>
      if s.val = 0 then
        if a.val = 2 then Measure.dirac ⟨2, by omega⟩
        else if a.val = 3 then
          (pBridge sp) • Measure.dirac ⟨1, by omega⟩ +
          (1 - pBridge sp) • Measure.dirac ⟨0, by omega⟩
        else Measure.dirac ⟨0, by omega⟩
      else if s.val = 1 then Measure.dirac ⟨1, by omega⟩
      else Measure.dirac ⟨2, by omega⟩,
    measurable' := measurable_of_finite _
  }
  obs := {
    toFun := fun (s, a) =>
      if s.val = 0 then
        let postCP := sp.T / 2 ≤ n
        let goodArm : Fin 2 := if postCP then ⟨1 - sp.Θ.val, by omega⟩ else sp.Θ
        if a.val = goodArm.val then
          (bernoulliMeasure (1/2 + sp.Δ) (by linarith [sp.hΔ0]) (by linarith [sp.hΔ4])).map (fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩)
        else if a.val < 2 then
          (bernoulliMeasure (1/2 - sp.Δ) (by linarith [sp.hΔ4]) (by linarith [sp.hΔ0])).map (fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩)
        else if a.val = 2 then Measure.dirac ⟨2, by omega⟩
        else Measure.dirac ⟨0, by omega⟩
      else if s.val = 1 then Measure.dirac ⟨1, by omega⟩
      else Measure.dirac ⟨2, by omega⟩,
    measurable' := measurable_of_finite _
  }
  r := fun (s, a) =>
    if a.val = 5 then -sp.M
    else if s.val = 0 then
      let postCP := sp.T / 2 ≤ n
      let goodArm : Fin 2 := if postCP then ⟨1 - sp.Θ.val, by omega⟩ else sp.Θ
      if a.val = goodArm.val then 1/2 + sp.Δ
      else if a.val < 2 then 1/2 - sp.Δ
      else 0
    else if s.val = 1 then
      if a.val = 4 then 1 else 0
    else 0
  hr_meas  := measurable_of_finite _
  μ₀       := Measure.dirac ⟨0, by omega⟩
  hμ₀      := inferInstance

private noncomputable def envStar_goodArm (sp : StarParam) (n : ℕ) : Fin 7 :=
  ⟨if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val, by
    have := sp.Θ.isLt
    split_ifs <;> omega⟩

end EnvStar

-- STAY-IN-S₀ ALGORITHM AND MARKOV INSTANCES

noncomputable def stayAlg : SixPrimitives.Algorithm (Fin 7) (Fin 3) Unit where
  σ₀     := ()
  act    := Kernel.deterministic (fun _ => ⟨0, by omega⟩) measurable_const
  update := Kernel.deterministic (fun _ => ()) measurable_const

instance stayAlg_isDet : AlgIsDeterministic stayAlg where
  actFn         := fun _ => ⟨0, by omega⟩
  actFn_meas    := measurable_const
  act_eq        := fun _ => by simp [stayAlg, Kernel.deterministic_apply]
  updateFn      := fun _ => ()
  updateFn_meas := measurable_const
  update_eq     := fun _ => by simp [stayAlg, Kernel.deterministic_apply]

instance stayAlg_isMarkov : AlgIsMarkov stayAlg :=
  algIsDeterministic_isMarkov stayAlg

private lemma pBridge_le_one (sp : StarParam) : pBridge sp ≤ 1 := by
  unfold pBridge
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hpos : (0 : ℝ) < sp.T := Nat.cast_pos.mpr sp.hT
  rw [div_le_one (Real.sqrt_pos.mpr hpos)]
  calc 1 = Real.sqrt 1        := by rw [Real.sqrt_one]
    _ ≤ Real.sqrt (sp.T : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr
                               (Nat.pos_iff_ne_zero.mp sp.hT))

private lemma pBridge_mixture_isProb (sp : StarParam) :
    IsProbabilityMeasure
      ((pBridge sp) • (Measure.dirac (⟨1, by omega⟩ : Fin 3)) +
       (1 - pBridge sp) • (Measure.dirac (⟨0, by omega⟩ : Fin 3))) := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
             Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  show (pBridge sp + (1 - pBridge sp) : ENNReal) = 1
  simp [pBridge_le_one sp]

lemma envStar_isMarkov (sp : StarParam) (n : ℕ) :
    EnvIsMarkov (envStar_family sp n) where
  trans_markov := ⟨fun ⟨s, a⟩ => by
    simp only [envStar_family, Kernel.coe_mk]
    fin_cases s <;> fin_cases a <;>
      simp only [Fin.zero_eta] <;>
      norm_num <;>
      first
      | exact inferInstance
      | exact pBridge_mixture_isProb sp⟩
  obs_markov := ⟨fun ⟨s, a⟩ => by
    simp only [envStar_family, Kernel.coe_mk]
    split_ifs with hs ha_eq ha_lt ha2
    all_goals
      first
      | exact inferInstance
      | {
        let μ : Measure Bool := bernoulliMeasure (1 / 2 + sp.Δ)
            (by linarith [sp.hΔ0]) (by linarith [sp.hΔ4])
        have hfAe : AEMeasurable (fun b : Bool => if b then (1 : Fin 3) else (0 : Fin 3)) μ :=
          (measurable_of_finite _).aemeasurable (μ := μ)
        have hprob : IsProbabilityMeasure μ :=
          bernoulliMeasure_isProbability (1 / 2 + sp.Δ)
            (by linarith [sp.hΔ0]) (by linarith [sp.hΔ4])
        haveI : IsProbabilityMeasure μ := hprob
        exact Measure.isProbabilityMeasure_map hfAe
      }
      | {
        let μ : Measure Bool := bernoulliMeasure (1 / 2 - sp.Δ)
            (by linarith [sp.hΔ4]) (by linarith [sp.hΔ0])
        have hfAe : AEMeasurable (fun b : Bool => if b then (1 : Fin 3) else (0 : Fin 3)) μ :=
          (measurable_of_finite _).aemeasurable (μ := μ)
        have hprob : IsProbabilityMeasure μ :=
          bernoulliMeasure_isProbability (1 / 2 - sp.Δ)
            (by linarith [sp.hΔ4]) (by linarith [sp.hΔ0])
        haveI : IsProbabilityMeasure μ := hprob
        exact Measure.isProbabilityMeasure_map hfAe
      }
    ⟩

-- HELPER LEMMAS FOR expectedVisits_stay

private lemma envStar_trans_zero_zero (sp : StarParam) (n : ℕ) :
    (envStar_family sp n).trans (⟨0, by omega⟩, ⟨0, by omega⟩) =
      Measure.dirac ⟨0, by omega⟩ := by
  simp [envStar_family, Kernel.coe_mk]

private lemma stayAlg_act_eq (σ : Unit) :
    stayAlg.act σ = Measure.dirac ⟨0, by omega⟩ := by
  simp [stayAlg, Kernel.deterministic_apply]

private lemma stayAlg_oneStep_newState (sp : StarParam) (n : ℕ) :
    ∀ᵐ step ∂(oneStepKernel (envStar_family sp n) stayAlg (measurable_of_finite _) ((), ⟨0, by omega⟩)),
      step.2.2.2.2 = ⟨0, by omega⟩ := by
  haveI hEnv : EnvIsMarkov (envStar_family sp n) := envStar_isMarkov sp n
  haveI hAlg : AlgIsMarkov stayAlg := stayAlg_isMarkov
  haveI := hEnv.obs_markov; haveI := hEnv.trans_markov
  haveI := hAlg.act_markov; haveI := hAlg.update_markov
  have hmf_step : Measurable (fun p : ((((Fin 7 × Fin 3) × ℝ) × Fin 3) × Unit) =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.2, p.1.2)) :=
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have h_set : MeasurableSet {x : Fin 7 × Fin 3 × ℝ × Unit × Fin 3 | x.2.2.2.2 = ⟨0, by omega⟩} := by
    apply measurableSet_eq_fun
    · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    · exact measurable_const
  simp only [oneStepKernel]
  rw [Kernel.map_apply (hf := hmf_step)]
  rw [MeasureTheory.ae_map_iff hmf_step.aemeasurable h_set]
  have hs5 : MeasurableSet {p : ((((Fin 7 × Fin 3) × ℝ) × Fin 3) × Unit) | p.1.2 = ⟨0, by omega⟩} := hmf_step h_set
  rw [Kernel.ae_compProd_iff hs5]
  have h_upd_eq : ∀ x, stayAlg.update x = Measure.dirac () := stayAlg_isDet.update_eq
  have hs4_eq : (fun a : (((Fin 7 × Fin 3) × ℝ) × Fin 3) => ∀ᵐ b ∂stayAlg.update.comap (fun x : (Unit × Fin 3) × (((Fin 7 × Fin 3) × ℝ) × Fin 3) => (x.1.1, x.2.1.1.1, x.2.1.1.2, x.2.1.2)) (by measurability) (((), ⟨0, by omega⟩), a), a.2 = ⟨0, by omega⟩) = (fun a => a.2 = ⟨0, by omega⟩) := by
    ext a
    simp only [Kernel.comap_apply, h_upd_eq, ae_dirac_eq, Filter.eventually_pure]
  rw [hs4_eq]
  have hs4 : MeasurableSet {a : (((Fin 7 × Fin 3) × ℝ) × Fin 3) | a.2 = ⟨0, by omega⟩} := by
    apply measurableSet_eq_fun measurable_snd measurable_const
  rw [Kernel.ae_compProd_iff hs4]
  have hs3_eq : (fun a : ((Fin 7 × Fin 3) × ℝ) => ∀ᵐ c ∂(envStar_family sp n).trans.comap (fun x : (Unit × Fin 3) × ((Fin 7 × Fin 3) × ℝ) => (x.1.2, x.2.1.1)) (by measurability) (((), ⟨0, by omega⟩), a), c = ⟨0, by omega⟩) = (fun a => ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1.1), c = ⟨0, by omega⟩) := by
    ext a
    simp only [Kernel.comap_apply]
  rw [hs3_eq]
  have hs3 : MeasurableSet {a : ((Fin 7 × Fin 3) × ℝ) | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1.1), c = ⟨0, by omega⟩} := by
    classical
    let f : Fin 7 → ℝ := fun a => if ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩ then 1 else 0
    have hf : Measurable f := measurable_of_finite f
    have h_eq : {a : ((Fin 7 × Fin 3) × ℝ) | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1.1), c = ⟨0, by omega⟩} = (f ∘ fun x => x.1.1) ⁻¹' {1} := by
      ext x
      simp only [f, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      split_ifs with h
      · exact iff_of_true h rfl
      · exact iff_of_false h (by norm_num)
    rw [h_eq]
    exact (hf.comp (measurable_fst.comp measurable_fst)) (measurableSet_singleton 1)
  rw [Kernel.ae_compProd_iff hs3]
  have hr_meas_comp : Measurable (fun x : (Unit × Fin 3) × (Fin 7 × Fin 3) => (envStar_family sp n).r (x.1.2, x.2.1)) :=
    (envStar_family sp n).hr_meas.comp (by measurability)
  have hs2_eq : (fun a : (Fin 7 × Fin 3) => ∀ᵐ b ∂Kernel.deterministic (fun x : (Unit × Fin 3) × (Fin 7 × Fin 3) => (envStar_family sp n).r (x.1.2, x.2.1)) hr_meas_comp (((), ⟨0, by omega⟩), a), ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1), c = ⟨0, by omega⟩) = (fun a => ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1), c = ⟨0, by omega⟩) := by
    ext a
    simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
  rw [hs2_eq]
  have hs2 : MeasurableSet {a : (Fin 7 × Fin 3) | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1), c = ⟨0, by omega⟩} := by
    classical
    let f : Fin 7 → ℝ := fun a => if ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩ then 1 else 0
    have hf : Measurable f := measurable_of_finite f
    have h_eq : {a : (Fin 7 × Fin 3) | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a.1), c = ⟨0, by omega⟩} = (f ∘ fun x => x.1) ⁻¹' {1} := by
      ext x
      simp only [f, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      split_ifs with h
      · exact iff_of_true h rfl
      · exact iff_of_false h (by norm_num)
    rw [h_eq]
    exact (hf.comp measurable_fst) (measurableSet_singleton 1)
  rw [Kernel.ae_compProd_iff hs2]
  have hs1_eq : (fun a : Fin 7 => ∀ᵐ b ∂(envStar_family sp n).obs.comap (fun x : (Unit × Fin 3) × Fin 7 => (x.1.2, x.2)) (by measurability) (((), ⟨0, by omega⟩), a), ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩) = (fun a => ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩) := by
    ext a
    simp only [Kernel.comap_apply]
    constructor
    · intro h
      by_cases ha : ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩
      · exact ha
      · have h_false : ∀ᵐ (_b : Fin 3) ∂(envStar_family sp n).obs (⟨0, by omega⟩, a), False := h.mono (fun _ hb => ha hb)
        rw [ae_iff] at h_false
        have h_set_eq : {x : Fin 3 | ¬False} = Set.univ := by ext; simp
        rw [h_set_eq] at h_false
        have h_meas : IsProbabilityMeasure ((envStar_family sp n).obs (⟨0, by omega⟩, a)) := inferInstance
        have h_univ_one := h_meas.measure_univ
        rw [h_univ_one] at h_false
        exact False.elim (one_ne_zero h_false)
    · intro h; exact ae_of_all _ (fun _ => h)
  rw [hs1_eq]
  have hs1 : MeasurableSet {a : Fin 7 | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩} := by
    classical
    let f : Fin 7 → ℝ := fun a => if ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩ then 1 else 0
    have hf : Measurable f := measurable_of_finite f
    have h_eq : {a : Fin 7 | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩} = f ⁻¹' {1} := by
      ext x
      simp only [f, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      split_ifs with h
      · exact iff_of_true h rfl
      · exact iff_of_false h (by norm_num)
    rw [h_eq]
    exact hf (measurableSet_singleton 1)
  have hproj : Measurable (fun x : (Unit × Fin 3) × Fin 7 => x.2) := measurable_snd
  have hs1_prod : MeasurableSet {x : (Unit × Fin 3) × Fin 7 | (x : (Unit × Fin 3) × Fin 7).2 ∈ {a : Fin 7 | ∀ᵐ c ∂(envStar_family sp n).trans (⟨0, by omega⟩, a), c = ⟨0, by omega⟩}} :=
    hproj hs1
  simp only [Kernel.comap_apply, stayAlg_act_eq, ae_dirac_eq, Filter.eventually_pure]
  have h_trans : (envStar_family sp n).trans (⟨0, by omega⟩, ⟨0, by omega⟩) = Measure.dirac ⟨0, by omega⟩ := envStar_trans_zero_zero sp n
  rw [h_trans]
  simp only [ae_dirac_eq, Filter.eventually_pure]

private lemma stayAlg_traj_ae_state (sp : StarParam) (n T : ℕ) :
    ∀ᵐ x ∂(trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) T ((), ⟨0, by omega⟩)),
      x.2.2 = ⟨0, by omega⟩ := by
  induction T with
  | zero =>
    have h_meas : Measurable (fun σs : Unit × Fin 3 => ((Fin.elim0 : Fin 0 → Fin 7 × Fin 3 × ℝ), σs)) :=
      Measurable.prodMk measurable_const measurable_id
    have h_set : MeasurableSet {x : (Fin 0 → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3 | x.2.2 = ⟨0, by omega⟩} := by
      measurability
    simp only [trajMeasureAux]
    rw [Kernel.map_apply (hf := h_meas), Kernel.id_apply]
    rw [MeasureTheory.ae_map_iff h_meas.aemeasurable h_set]
    simp only [ae_dirac_eq, Filter.eventually_pure]
  | succ T ih =>
    haveI hEnv : EnvIsMarkov (envStar_family sp n) := envStar_isMarkov sp n
    haveI hAlg : AlgIsMarkov stayAlg := stayAlg_isMarkov
    haveI h_osk : IsMarkovKernel (oneStepKernel (envStar_family sp n) stayAlg (measurable_of_finite _)) := oneStepKernel_isMarkov _ _ _ hEnv hAlg
    haveI h_tm : IsMarkovKernel (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) T) := trajMeasureAux_isMarkov _ _ _ hEnv hAlg T
    have h_map : Measurable (fun x : ((Fin T → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3) × Fin 7 × Fin 3 × ℝ × Unit × Fin 3 =>
      (Fin.snoc (α := fun _ => Fin 7 × Fin 3 × ℝ) x.1.1 (x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2.1, x.2.2.2.2.2)) := by
      apply Measurable.prodMk
      · apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; fun_prop
        · intro j; simp only [Fin.snoc_castSucc]; fun_prop
      · exact (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
              (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    have h_set : MeasurableSet {x : (Fin (T + 1) → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3 | x.2.2 = ⟨0, by omega⟩} := by
      apply measurableSet_eq_fun
      · exact measurable_snd.comp measurable_snd
      · exact measurable_const
    simp only [trajMeasureAux]
    rw [Kernel.map_apply (hf := h_map)]
    rw [MeasureTheory.ae_map_iff h_map.aemeasurable h_set]
    have hs2 : MeasurableSet {x : ((Fin T → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3) × Fin 7 × Fin 3 × ℝ × Unit × Fin 3 | x.2.2.2.2.2 = ⟨0, by omega⟩} := by
      apply measurableSet_eq_fun
      · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      · exact measurable_const
    rw [Kernel.ae_compProd_iff hs2]
    filter_upwards [ih] with a ha
    simp only [Kernel.comap_apply]
    have h_a2_eq : a.2 = ((), ⟨0, by omega⟩) := by
      apply Prod.ext
      · rfl
      · exact ha
    rw [h_a2_eq]
    exact stayAlg_oneStep_newState sp n

private lemma stayAlg_stateMarginal_isDirac (sp : StarParam) (n t : ℕ) :
    stateMarginal (envStar_family sp n) stayAlg (measurable_of_finite _) t =
    Measure.dirac ⟨0, by omega⟩ := by
  haveI hEnv : EnvIsMarkov (envStar_family sp n) := envStar_isMarkov sp n
  haveI hAlg : AlgIsMarkov stayAlg := stayAlg_isMarkov
  apply MeasureTheory.Measure.ext
  intro s hs
  have h_sm : stateMarginal (envStar_family sp n) stayAlg (measurable_of_finite _) t =
      (((Measure.dirac stayAlg.σ₀).prod (envStar_family sp n).μ₀).bind
        (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1))).map (Prod.snd ∘ Prod.snd) := rfl
  rw [h_sm]
  have h_mu : (Measure.dirac (α := Unit) stayAlg.σ₀).prod (envStar_family sp n).μ₀ = Measure.dirac ((), ⟨0, by omega⟩) := by
    simp only [stayAlg, envStar_family, Measure.dirac_prod_dirac]
  rw [h_mu, Measure.dirac_bind]
  swap
  · exact Kernel.measurable _
  rw [Measure.map_apply (measurable_snd.comp measurable_snd) hs]
  have h_ae := stayAlg_traj_ae_state sp n (t + 1)
  by_cases h0 : (⟨0, by omega⟩ : Fin 3) ∈ s
  · rw [Measure.dirac_apply_of_mem h0]
    haveI hMarkov : IsMarkovKernel (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1)) :=
      trajMeasureAux_isMarkov _ _ _ hEnv hAlg _
    have h_meas_s : MeasurableSet ((Prod.snd ∘ Prod.snd : ((Fin (t + 1) → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3) → Fin 3) ⁻¹' s) := (measurable_snd.comp measurable_snd) hs
    have h_univ : ∀ᵐ x ∂(trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1) ((), ⟨0, by omega⟩)), x ∈ (Prod.snd ∘ Prod.snd) ⁻¹' s := by
      filter_upwards [h_ae] with x hx
      simp only [Set.mem_preimage, Function.comp_apply]
      rw [hx]
      exact h0
    rw [ae_iff] at h_univ
    have h_univ_compl :
        (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1)
          ((), ⟨0, by omega⟩)) ((Prod.snd ∘ Prod.snd) ⁻¹' s)ᶜ = 0 := by
      simpa [Set.mem_compl_iff] using h_univ
    have h_compl : (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1)
        ((), ⟨0, by omega⟩)) ((Prod.snd ∘ Prod.snd) ⁻¹' s) = 1 := by
      have h_univ_meas := measure_add_measure_compl h_meas_s
        (μ := (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1) ((), ⟨0, by omega⟩)))
      rw [h_univ_compl] at h_univ_meas
      simpa using h_univ_meas
    exact h_compl
  · have h_empty : ∀ᵐ x ∂(trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1) ((), ⟨0, by omega⟩)), x ∉ (Prod.snd ∘ Prod.snd) ⁻¹' s := by
      filter_upwards [h_ae] with x hx
      simp only [Set.mem_preimage, Function.comp_apply]
      rw [hx]
      exact h0
    have h_meas_s : MeasurableSet ((Prod.snd ∘ Prod.snd : ((Fin (t + 1) → Fin 7 × Fin 3 × ℝ) × Unit × Fin 3) → Fin 3) ⁻¹' s) :=
      (measurable_snd.comp measurable_snd) hs
    rw [ae_iff] at h_empty
    have h_empty' :
        (trajMeasureAux (envStar_family sp n) stayAlg (measurable_of_finite _) (t + 1)
          ((), ⟨0, by omega⟩)) ((Prod.snd ∘ Prod.snd) ⁻¹' s) = 0 := by
      simpa using h_empty
    rw [h_empty']
    symm
    rw [Measure.dirac_apply' _ hs]
    exact if_neg h0

-- expectedVisits_stay

lemma expectedVisits_stay (sp : StarParam) (n T : ℕ) (_hT : 0 < T) :
    expectedVisits (envStar_family sp n) stayAlg (measurable_of_finite _) T
      ⟨0, by omega⟩ = T := by
  simp only [expectedVisits, stayAlg_stateMarginal_isDirac,
             Measure.dirac_apply]
  simp [Finset.sum_const]

-- visitFrequencyAtLeast_envStar

lemma visitFrequencyAtLeast_envStar (sp : StarParam) (n : ℕ) :
    SixPrimitives.VisitFrequencyAtLeast (envStar_family sp n) ⟨0, by omega⟩ 1 := by
  exact ⟨Unit, inferInstance, inferInstance, inferInstance,
    stayAlg,
    envStar_isMarkov sp n,
    stayAlg_isMarkov,
    fun T hT => by rw [expectedVisits_stay sp n T hT]; simp⟩

-- POST-OPTVALUE SUPPORT LEMMAS

lemma env₄_step_regret {Sig : Type*}
    [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig) (T : ℕ) :
    SixPrimitives.regret env₄ alg T = T - SixPrimitives.algValue env₄ alg T := by
  unfold SixPrimitives.regret
  rw [env₄_optValue T]

-- E* PROPERTY CERTIFICATES

-- P1 Certificate
theorem envStar_hasP₁ (sp : StarParam) (n : ℕ) :
    SixPrimitives.HasP₁
      (envStar_family { sp with Θ := ⟨0, by decide⟩ } n)
      (envStar_family { sp with Θ := ⟨1, by decide⟩ } n) := by
  let sp₀ : StarParam := { sp with Θ := ⟨0, by decide⟩ }
  let sp₁ : StarParam := { sp with Θ := ⟨1, by decide⟩ }
  let a₀ := envStar_goodArm sp₀ n
  let a₁ := envStar_goodArm sp₁ n
  refine ⟨⟨0, by omega⟩, a₀, a₁, ?_, ?_, ?_⟩
  · intro h_eq
    have h_val : a₀.val = a₁.val := by rw [h_eq]
    change (if sp₀.T / 2 ≤ n then 1 - sp₀.Θ.val else sp₀.Θ.val) =
           (if sp₁.T / 2 ≤ n then 1 - sp₁.Θ.val else sp₁.Θ.val) at h_val
    change (if sp.T / 2 ≤ n then 1 - 0 else 0) =
           (if sp.T / 2 ≤ n then 1 - 1 else 1) at h_val
    revert h_val
    split_ifs
    · intro h_val; omega
    · intro h_val; omega
  · intro a
    have hr0 : (envStar_family sp₀ n).r (⟨0, by omega⟩, a₀) = 1 / 2 + sp.Δ := by
      dsimp [envStar_family]
      have h_not_5 : a₀.val ≠ 5 := by
        change (if sp₀.T / 2 ≤ n then 1 - sp₀.Θ.val else sp₀.Θ.val) ≠ 5
        split_ifs <;> omega
      rw [if_neg h_not_5]
      have h_good_eq : a₀.val = (if sp₀.T / 2 ≤ n then (⟨1 - sp₀.Θ.val, by omega⟩ : Fin 2) else sp₀.Θ).val := by
        change (if sp₀.T / 2 ≤ n then 1 - sp₀.Θ.val else sp₀.Θ.val) = _
        split_ifs <;> rfl
      rw [if_pos h_good_eq]
    have h_r_a : (envStar_family sp₀ n).r (⟨0, by omega⟩, a) ≤ 1 / 2 + sp.Δ := by
      dsimp [envStar_family]
      by_cases h5 : a.val = 5
      · rw [if_pos h5]
        linarith [sp.hM, sp.hΔ0]
      · rw [if_neg h5]
        by_cases h_good : a.val = (if sp₀.T / 2 ≤ n then (⟨1 - sp₀.Θ.val, by omega⟩ : Fin 2) else sp₀.Θ).val
        · rw [if_pos h_good]
        · rw [if_neg h_good]
          by_cases hlt : a.val < 2
          · rw [if_pos hlt]
            linarith [sp.hΔ0]
          · rw [if_neg hlt]
            linarith [sp.hΔ0]
    rw [hr0]
    exact h_r_a
  · intro a
    have hr1 : (envStar_family sp₁ n).r (⟨0, by omega⟩, a₁) = 1 / 2 + sp.Δ := by
      dsimp [envStar_family]
      have h_not_5 : a₁.val ≠ 5 := by
        change (if sp₁.T / 2 ≤ n then 1 - sp₁.Θ.val else sp₁.Θ.val) ≠ 5
        split_ifs <;> omega
      rw [if_neg h_not_5]
      have h_good_eq : a₁.val = (if sp₁.T / 2 ≤ n then (⟨1 - sp₁.Θ.val, by omega⟩ : Fin 2) else sp₁.Θ).val := by
        change (if sp₁.T / 2 ≤ n then 1 - sp₁.Θ.val else sp₁.Θ.val) = _
        split_ifs <;> rfl
      rw [if_pos h_good_eq]
    have h_r_a : (envStar_family sp₁ n).r (⟨0, by omega⟩, a) ≤ 1 / 2 + sp.Δ := by
      dsimp [envStar_family]
      by_cases h5 : a.val = 5
      · rw [if_pos h5]
        linarith [sp.hM, sp.hΔ0]
      · rw [if_neg h5]
        by_cases h_good : a.val = (if sp₁.T / 2 ≤ n then (⟨1 - sp₁.Θ.val, by omega⟩ : Fin 2) else sp₁.Θ).val
        · rw [if_pos h_good]
        · rw [if_neg h_good]
          by_cases hlt : a.val < 2
          · rw [if_pos hlt]
            linarith [sp.hΔ0]
          · rw [if_neg hlt]
            linarith [sp.hΔ0]
    rw [hr1]
    exact h_r_a

-- P2 Certificate
def envStar_trap : Set (Fin 3) := {⟨2, by decide⟩}

theorem envStar_hasP₂ (sp : StarParam) (n : ℕ) :
    SixPrimitives.HasP₂ (envStar_family sp n) envStar_trap := by
  refine ⟨⟨⟨2, by decide⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : (⟨0, by decide⟩ : Fin 3) ∈ envStar_trap := by
      rw [h]
      exact Set.mem_univ _
    simp [envStar_trap] at h0
  · intro s hs a
    simp only [envStar_trap, Set.mem_singleton_iff] at hs
    subst hs
    simp [envStar_family, envStar_trap]
  · intro s hs a
    simp only [envStar_trap, Set.mem_singleton_iff] at hs
    subst hs
    simp [envStar_family]
    split_ifs
    · linarith [sp.hM]
    · rfl
  · refine ⟨⟨0, by decide⟩, ?_, ⟨2, by decide⟩, ?_⟩
    · simp [envStar_trap]
    · simp [envStar_family, envStar_trap]

-- P3 Certificate
def envStar_local : Set (Fin 3) := {⟨0, by decide⟩}
def envStar_global : Set (Fin 3) := {⟨1, by decide⟩}

lemma pBridge_pos (sp : StarParam) : 0 < pBridge sp := by
  unfold pBridge
  have hpos : 0 < (1 / Real.sqrt (↑sp.T : ℝ)) := by
    have hTpos : 0 < (↑sp.T : ℝ) := Nat.cast_pos.mpr sp.hT
    have hsqrt : 0 < Real.sqrt (↑sp.T : ℝ) := Real.sqrt_pos.mpr hTpos
    exact one_div_pos.mpr hsqrt
  exact ENNReal.ofReal_pos.mpr hpos

lemma envStar_r_goodArm (sp : StarParam) (n : ℕ) :
    (envStar_family sp n).r (⟨0, by omega⟩, envStar_goodArm sp n) = 1 / 2 + sp.Δ := by
  dsimp [envStar_family, envStar_goodArm]
  have h_eq : (if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val) =
      (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val := by
    split_ifs <;> rfl
  have h_not_5 : (envStar_goodArm sp n).val ≠ 5 := by
    dsimp [envStar_goodArm]
    split_ifs <;> omega
  simp [h_eq]
  omega

lemma envStar_greedy_not_2_3 (sp : StarParam) (n : ℕ) (a : Fin 7)
    (h_greedy : ∀ a', (envStar_family sp n).r (⟨0, by omega⟩, a) ≥ (envStar_family sp n).r (⟨0, by omega⟩, a')) :
    a.val ≠ 2 ∧ a.val ≠ 3 := by
  have h_ge := h_greedy (envStar_goodArm sp n)
  rw [envStar_r_goodArm sp n] at h_ge
  have h_r_a : (envStar_family sp n).r (⟨0, by omega⟩, a) =
      if a.val = 5 then -sp.M
      else if a.val = (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val then 1 / 2 + sp.Δ
      else if a.val < 2 then 1 / 2 - sp.Δ else 0 := rfl
  rw [h_r_a] at h_ge
  constructor
  · intro h2
    have h_not_5 : a.val ≠ 5 := by rw [h2]; omega
    have h_neq : a.val ≠ (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val := by
      rw [h2]; split_ifs <;> omega
    have h_nl : ¬ (a.val < 2) := by rw [h2]; omega
    rw [if_neg h_not_5, if_neg h_neq, if_neg h_nl] at h_ge
    linarith [sp.hΔ0]
  · intro h3
    have h_not_5 : a.val ≠ 5 := by rw [h3]; omega
    have h_neq : a.val ≠ (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val := by
      rw [h3]; split_ifs <;> omega
    have h_nl : ¬ (a.val < 2) := by rw [h3]; omega
    rw [if_neg h_not_5, if_neg h_neq, if_neg h_nl] at h_ge
    linarith [sp.hΔ0]

lemma envStar_trans_greedy (sp : StarParam) (n : ℕ) (a : Fin 7)
    (h_greedy : ∀ a', (envStar_family sp n).r (⟨0, by omega⟩, a) ≥ (envStar_family sp n).r (⟨0, by omega⟩, a')) :
    (envStar_family sp n).trans (⟨0, by omega⟩, a) = Measure.dirac ⟨0, by omega⟩ := by
  have ⟨ha2, ha3⟩ := envStar_greedy_not_2_3 sp n a h_greedy
  simp [envStar_family, ha2, ha3]

lemma envStar_trans_bridge (sp : StarParam) (n : ℕ) :
    (envStar_family sp n).trans (⟨0, by omega⟩, ⟨3, by omega⟩) =
    (pBridge sp) • Measure.dirac ⟨1, by omega⟩ + (1 - pBridge sp) • Measure.dirac ⟨0, by omega⟩ := by
  change (if (⟨0, by omega⟩ : Fin 3).val = 0 then
           if (⟨3, by omega⟩ : Fin 7).val = 2 then Measure.dirac (⟨2, by omega⟩ : Fin 3)
           else if (⟨3, by omega⟩ : Fin 7).val = 3 then
             (pBridge sp) • Measure.dirac (⟨1, by omega⟩ : Fin 3) + (1 - pBridge sp) • Measure.dirac (⟨0, by omega⟩ : Fin 3)
           else Measure.dirac (⟨0, by omega⟩ : Fin 3)
         else if (⟨0, by omega⟩ : Fin 3).val = 1 then Measure.dirac (⟨1, by omega⟩ : Fin 3)
         else Measure.dirac (⟨2, by omega⟩ : Fin 3)) = _
  have h0 : (⟨0, by omega⟩ : Fin 3).val = 0 := rfl
  have h32 : (⟨3, by omega⟩ : Fin 7).val ≠ 2 := by decide
  have h33 : (⟨3, by omega⟩ : Fin 7).val = 3 := rfl
  rw [if_pos h0, if_neg h32, if_pos h33]

theorem envStar_hasP₃ (sp : StarParam) (n : ℕ) :
    SixPrimitives.HasP₃ (envStar_family sp n) envStar_local envStar_global := by
  refine ⟨?_, ⟨⟨0, by omega⟩, rfl⟩, ⟨⟨1, by omega⟩, rfl⟩, ?_, ?_, ?_⟩
  · exact Set.disjoint_singleton.mpr (by decide)
  · intro s hs a h_greedy
    simp only [envStar_local, Set.mem_singleton_iff] at hs
    subst hs
    rw [envStar_trans_greedy sp n a h_greedy]
    exact Measure.dirac_apply_of_mem (by simp [envStar_local])
  · refine ⟨⟨0, by omega⟩, by simp [envStar_local], ⟨3, by omega⟩, ?_⟩
    rw [envStar_trans_bridge sp n]
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    have h_dirac1 : Measure.dirac (⟨1, by omega⟩ : Fin 3) envStar_global = 1 :=
      Measure.dirac_apply_of_mem (by simp [envStar_global])
    have h_dirac0 : Measure.dirac (⟨0, by omega⟩ : Fin 3) envStar_global = 0 := by
      have hn : (⟨0, by omega⟩ : Fin 3) ∉ envStar_global := by simp [envStar_global]
      simp [envStar_global]
    rw [h_dirac1, h_dirac0, mul_zero, add_zero, mul_one]
    exact pBridge_pos sp
  · refine ⟨1/2 + sp.Δ, 1, ?_, ?_, by linarith [sp.hΔ4]⟩
    · intro s hs a
      simp only [envStar_local, Set.mem_singleton_iff] at hs
      subst hs
      dsimp [envStar_family]
      by_cases h5 : a.val = 5
      · rw [if_pos h5]
        linarith [sp.hM, sp.hΔ0]
      · rw [if_neg h5]
        by_cases h_eq : a.val = (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val
        · rw [if_pos h_eq]
        · rw [if_neg h_eq]
          by_cases hlt : a.val < 2
          · rw [if_pos hlt]
            linarith [sp.hΔ0]
          · rw [if_neg hlt]
            linarith [sp.hΔ0]
    · intro s hs
      simp only [envStar_global, Set.mem_singleton_iff] at hs
      subst hs
      refine ⟨⟨4, by omega⟩, ?_⟩
      have h1 : ((⟨1, by omega⟩ : Fin 3).val = 1) := rfl
      have h4 : ((⟨4, by omega⟩ : Fin 7).val = 4) := rfl
      dsimp [envStar_family]
      simp

-- P4 Certificate
theorem envStar_hasP₄ (sp : StarParam) (n : ℕ) :
    SixPrimitives.HasP₄ (envStar_family sp n)
      ⟨0, by omega⟩ (envStar_goodArm sp n) SixPrimitives.VisitFrequencyAtLeast := by
  refine ⟨2 * sp.Δ, 1, by linarith [sp.hΔ0], zero_lt_one, ?_, visitFrequencyAtLeast_envStar sp n⟩
  intro a ha
  have h_a_neq : a.val ≠ (if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val) := by
    intro h
    apply ha
    apply Fin.ext
    exact h
  have h_r_star : (envStar_family sp n).r (⟨0, by omega⟩, envStar_goodArm sp n) = 1 / 2 + sp.Δ := by
    dsimp [envStar_family]
    have h_not_5 : (envStar_goodArm sp n).val ≠ 5 := by
      change (if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val) ≠ 5
      split_ifs <;> omega
    rw [if_neg h_not_5]
    have h_good_eq : (envStar_goodArm sp n).val = (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val := by
      change (if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val) = _
      split_ifs <;> rfl
    rw [if_pos h_good_eq]
  have h_r_a : (envStar_family sp n).r (⟨0, by omega⟩, a) ≤ 1 / 2 - sp.Δ := by
    dsimp [envStar_family]
    by_cases h5 : a.val = 5
    · rw [if_pos h5]
      linarith [sp.hM, sp.hΔ4]
    · rw [if_neg h5]
      by_cases h_good : a.val = (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val
      · exfalso
        apply h_a_neq
        have h_eq_good : (if sp.T / 2 ≤ n then (⟨1 - sp.Θ.val, by omega⟩ : Fin 2) else sp.Θ).val = (if sp.T / 2 ≤ n then 1 - sp.Θ.val else sp.Θ.val) := by
          split_ifs <;> rfl
        rw [← h_eq_good]
        exact h_good
      · rw [if_neg h_good]
        by_cases hlt : a.val < 2
        · rw [if_pos hlt]
        · rw [if_neg hlt]
          linarith [sp.hΔ4, sp.hΔ0]
  rw [h_r_star]
  linarith

-- P5 Certificate
def envStar_feas : Set (Fin 7) := {⟨5, by omega⟩}ᶜ

theorem envStar_hasP₅ (sp : StarParam) (n : ℕ) :
    SixPrimitives.HasP₅ (envStar_family sp n) envStar_feas sp.M := by
  refine ⟨sp.hM, ?_, ?_⟩
  · rw [Set.ssubset_def]
    constructor
    · exact Set.subset_univ _
    · intro h_univ
      have h_mem : (⟨5, by omega⟩ : Fin 7) ∈ envStar_feas := h_univ (Set.mem_univ _)
      simp only [envStar_feas, Set.mem_compl_iff, Set.mem_singleton_iff] at h_mem
      exact h_mem trivial
  · intro s a ha
    simp only [envStar_feas, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at ha
    subst ha
    dsimp [envStar_family]
    exact le_rfl

-- P6 Certificate
theorem envStar_hasP₆ (sp : StarParam) (hT2 : 1 < sp.T) :
    SixPrimitives.HasP₆ (envStar_family sp) (sp.T / 2 - 1) := by
  have h_theta_lt_7 : sp.Θ.val < 7 := by have := sp.Θ.isLt; omega
  let a_star : Fin 7 := ⟨sp.Θ.val, h_theta_lt_7⟩
  refine ⟨⟨0, by omega⟩, a_star, Or.inl ?_⟩
  dsimp [envStar_family]
  intro h_contra
  have h_not_5 : a_star.val = 5 ↔ False := by
    constructor
    · intro h; change sp.Θ.val = 5 at h; have := sp.Θ.isLt; omega
    · intro h; exact h.elim
  have h_pre : (sp.T / 2 ≤ sp.T / 2 - 1) ↔ False := by
    exact iff_false_intro (by omega)
  have h_post : (sp.T / 2 ≤ sp.T / 2 - 1 + 1) ↔ True := by
    exact iff_true_intro (by omega)
  have h_a_star_eq : a_star.val = sp.Θ.val ↔ True := by
    exact iff_true_intro rfl
  have h_a_star_neq : a_star.val = 1 - sp.Θ.val ↔ False := by
    constructor
    · intro h
      change sp.Θ.val = 1 - sp.Θ.val at h
      have := sp.Θ.isLt
      omega
    · intro h; exact h.elim
  have h_lt_2 : a_star.val < 2 ↔ True := by
    exact iff_true_intro sp.Θ.isLt
  simp only [h_not_5, h_pre, h_post, h_a_star_eq, h_a_star_neq, h_lt_2, ite_false, ite_true] at h_contra
  have h_delta_pos := sp.hΔ0
  linarith

theorem envStar_inClassC (sp : StarParam) (n : ℕ) :
    SixPrimitives.InClassC (envStar_family sp n) SixPrimitives.VisitFrequencyAtLeast := by
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨0, by omega⟩, envStar_goodArm sp n, envStar_hasP₄ sp n⟩)))

-- CONDITIONAL DANGER PROBABILITY SEQUENCE

section CondDangerProbForEnv₂

variable {A O Sig : Type*}
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableEq A]
  [MeasurableSpace O] [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
  [MeasurableSingletonClass Sig] [MeasurableEq Sig]

def survivedToStep (K : ℕ) (hK : 0 < K) (k : ℕ) :
    Set (Phase2.Trajectory (Fin 2) (Fin (K+2)) (k+1)) :=
  let trap := Fin.last (K+1)   -- trap state = K+1
  { ω | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k ≠ trap }

noncomputable def survivalProbSeq
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K+2)) Sig)
    (_hAlg : Phase2.AlgIsMarkov alg)
    (k : ℕ) : ℝ :=
  ((Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (k+1))
    (survivedToStep K hK k)).toReal

noncomputable def dangerAndSurvivalProbSeq
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K+2)) Sig)
    (_hAlg : Phase2.AlgIsMarkov alg)
    (aDanger : Fin (K+2) → Fin 2)
    (k : ℕ) : ℝ :=
  let _trap := Fin.last (K+1)
  let surv_set := survivedToStep K hK k
  let danger_set := { ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) }
  ((Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (k+1))
    (surv_set ∩ danger_set)).toReal

noncomputable def condDangerProbSeq
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K+2)) Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (aDanger : Fin (K+2) → Fin 2)
    (k : ℕ) : ℝ :=
  let surv := survivalProbSeq K hK alg hAlg k
  if surv = 0 then 0 else dangerAndSurvivalProbSeq K hK alg hAlg aDanger k / surv

end CondDangerProbForEnv₂

end SixPrimitives.Phase2
