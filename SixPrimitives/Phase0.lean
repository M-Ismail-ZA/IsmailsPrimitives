import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Order.Filter.Basic

/-! # Ismail's Primitives — Phase 0: Framework Types

**Source**: Ismail (2026 V6), §2–§3.
**Mathlib version**: v4.30.0
**Module path**: `SixPrimitives/Phase0.lean`

Phase 0 defines the fundamental types and predicates used throughout the formalization:
  - `Env` structure (POMDP environment)
  - `Algorithm` structure (canonical-summary algorithm)
  - `HasPᵢ` / `LacksXᵢ` / `PossessesXᵢ` / `RobustXᵢ` predicates
  - `InClassC` predicate -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace SixPrimitives

-- §1  ENVIRONMENT

/-- A POMDP environment.

    The field `hr_meas : Measurable r` is required for the
    trajectory-measure construction in Phase 2. -/
structure Env (S A O : Type*)
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] where
  /-- Stochastic state transition: (s, a) → distribution over s' -/
  trans    : Kernel (S × A) S
  /-- Stochastic observation emission: (s, a) → distribution over o -/
  obs      : Kernel (S × A) O
  /-- Deterministic reward: r(s, a) ∈ ℝ -/
  r        : S × A → ℝ
  /-- Measurability of r — required for `Kernel.deterministic` in Phase 2. -/
  hr_meas  : Measurable r
  /-- Initial state distribution -/
  μ₀       : Measure S
  /-- μ₀ is a probability measure -/
  hμ₀      : IsProbabilityMeasure μ₀

-- §2  ALGORITHM

/-- A sequential algorithm with canonical summary type `Sig`. -/
structure Algorithm (A O Sig : Type*)
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig]
    [BorelSpace Sig] where
  /-- Action selection: depends only on summary σ. -/
  act    : Kernel Sig A
  /-- Summary update: (σ, action, observation, reward) → new summary. -/
  update : Kernel (Sig × A × O × ℝ) Sig
  /-- Initial summary. -/
  σ₀     : Sig

-- §3  FAILURE CONDITIONS  (LacksXᵢ)

section FailureConditions

variable {S A O : Type*}

/-- **(F1)** Bounded mutual information: `limsup miSeq t ≤ B < ½`.
    The parameter `mi : ℕ → ℝ` is instantiated by Phase 2's `miSeq`. -/
def LacksX₁ (mi : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, B < 1/2 ∧ limsup (fun t : ℕ => mi t) atTop ≤ B

/-- **(F2)** Persistent danger probability: `dangerProb` is bounded away from zero.
    The parameter is instantiated by Phase 2's `dangerProbSeq`. -/
def LacksX₂ (dangerProb : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, dangerProb k ≥ δ

/-- **(F3)** Bounded total bridge plays: there exists a constant C such that
    the cumulative bridge-action count satisfies `cumBridge T ≤ C` for all T.
    The parameter is instantiated by Phase 2's `bridgeCumSeq`. -/
def LacksX₃ (cumBridge : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, cumBridge T ≤ C

/-- **(F4)** Persistent conditional entropy: `liminf condEnt t > 0`.
    The parameter is instantiated by Phase 2's `condEntSeq`. -/
def LacksX₄ (condEnt : ℕ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε ≤ liminf (fun t : ℕ => condEnt t) atTop

lemma LacksX₄_liminf_pos {f : ℕ → ℝ} (h : LacksX₄ f) :
    0 < liminf f atTop :=
  let ⟨_ε, hε, hle⟩ := h; lt_of_lt_of_le hε hle

/-- **(F5)** Persistent infeasible play: `liminf Cesàro avg ≥ δ > 0`.
    The parameter is instantiated by Phase 2's `infeasProbSeq`. -/
def LacksX₅ (infeasProb : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    δ ≤ liminf (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, infeasProb t) atTop

/-- **(F6)** Stale arm dominates post-changepoint window. -/
def LacksX₆ (staleProb : ℕ → ℝ) (tau : ℕ) : Prop :=
  ∃ (ε δ : ℝ), 0 < ε ∧ ε ≤ 1/2 ∧ 0 < δ ∧
    (Nat.floor ((1 + ε) * tau) > tau) ∧  -- ensure window is non-empty
    ∀ t : ℕ, tau < t → t ≤ Nat.floor ((1 + ε) * tau) → staleProb t ≥ 1/2 + δ

end FailureConditions

-- §4  POSSESSION CONDITIONS  (PossessesXᵢ / RobustXᵢ)

section Possession

/-- **Ordinary possession X₁**: the algorithm is NOT lacking X₁. -/
def PossessesX₁ (mi : ℕ → ℝ) : Prop := ¬ LacksX₁ mi

/-- **Robust possession X₁**: liminf mi > 1/2. -/
def RobustX₁ (mi : ℕ → ℝ) : Prop := 1/2 < liminf (fun t => mi t) atTop

/-- **Ordinary possession X₂**: ¬ LacksX₂. -/
def PossessesX₂ (dangerProb : ℕ → ℝ) : Prop := ¬ LacksX₂ dangerProb

/-- **Robust possession X₂**: dangerProb → 0. -/
def RobustX₂ (dangerProb : ℕ → ℝ) : Prop :=
  Tendsto dangerProb atTop (nhds 0)

/-- **Ordinary possession X₃**: ¬ LacksX₃. -/
def PossessesX₃ (cumBridge : ℕ → ℝ) : Prop := ¬ LacksX₃ cumBridge

/-- **Robust possession X₃**: cumBridge T = ω(√T). -/
def RobustX₃ (cumBridge : ℕ → ℝ) : Prop :=
  Tendsto (fun T : ℕ => cumBridge T / Real.sqrt T) atTop atTop

/-- **Ordinary possession X₄**: ¬ LacksX₄. -/
def PossessesX₄ (condEnt : ℕ → ℝ) : Prop := ¬ LacksX₄ condEnt

/-- **Robust possession X₄**: liminf condEnt = 0 AND ℙ(Aₜ=a*)→1. -/
def RobustX₄ (condEnt optProb : ℕ → ℝ) : Prop :=
  liminf (fun t : ℕ => condEnt t) atTop = 0 ∧
  Tendsto optProb atTop (nhds 1)

/-- **Ordinary possession X₅**: ¬ LacksX₅. -/
def PossessesX₅ (infeasProb : ℕ → ℝ) : Prop := ¬ LacksX₅ infeasProb

/-- **Robust possession X₅**: Cesàro average of infeasible-play probability → 0. -/
def RobustX₅ (infeasProb : ℕ → ℝ) : Prop :=
  Tendsto
    (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, infeasProb t)
    atTop (nhds 0)

/-- **Ordinary possession X₆**: ¬ LacksX₆. -/
def PossessesX₆ (staleProb : ℕ → ℝ) (tau : ℕ) : Prop := ¬ LacksX₆ staleProb tau

/-- **Robust possession X₆**: evidence-reset possession. -/
def RobustX₆ (staleProb      : ℕ → ℝ)
             (tau             : ℕ)
             (cleanSummary    : ℕ → ℝ)
             (actualSummary   : ℕ → ℝ) : Prop :=
  ¬ LacksX₆ staleProb tau ∧
  ∀ K : ℕ, cleanSummary K = actualSummary K

end Possession

-- §5  STRUCTURAL PROPERTIES AND CLASS C

section StructuralProperties

variable {S A O : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace O] [DecidableEq S] [DecidableEq A]

/-- **(P1)** Reward ambiguity: hidden Θ* ∈ {0,1}, different optimal actions. -/
def HasP₁ (env₀ env₁ : Env S A O) : Prop :=
  ∃ (s : S) (a₀ a₁ : A), a₀ ≠ a₁ ∧
    (∀ a : A, env₀.r (s, a₀) ≥ env₀.r (s, a)) ∧
    (∀ a : A, env₁.r (s, a₁) ≥ env₁.r (s, a))

/-- **(P2)** Absorbing traps. -/
def HasP₂ (env : Env S A O) (S_abs : Set S) : Prop :=
  S_abs.Nonempty ∧ S_abs ≠ Set.univ ∧
  (∀ s ∈ S_abs, ∀ a : A, env.trans (s, a) S_abs = 1) ∧
  (∀ s ∈ S_abs, ∀ a : A, env.r (s, a) ≤ 0) ∧
  (∃ s ∉ S_abs, ∃ a : A, 0 < env.trans (s, a) S_abs)

/-- **(P3)** Local optima. -/
def HasP₃ (env : Env S A O) (S_local S_global : Set S) : Prop :=
  Disjoint S_local S_global ∧
  S_local.Nonempty ∧ S_global.Nonempty ∧
  (∀ s ∈ S_local, ∀ a : A,
    (∀ a' : A, env.r (s, a) ≥ env.r (s, a')) →
      env.trans (s, a) S_local = 1) ∧
  (∃ s ∈ S_local, ∃ a : A, env.trans (s, a) S_global > 0) ∧
  (∃ r_local r_global : ℝ,
    (∀ s ∈ S_local, ∀ a : A, env.r (s, a) ≤ r_local) ∧
    (∀ s ∈ S_global, ∃ a : A, env.r (s, a) ≥ r_global) ∧
    r_local < r_global)

/-- **(P4)** Deterministic optimality.
    `visitFreq` is supplied by Phase 2 once the trajectory measure is available;
    the canonical instance is `SixPrimitives.VisitFrequencyAtLeast`. -/
def HasP₄ (env : Env S A O) (s_star : S) (a_star : A)
    (visitFreq : Env S A O → S → ℝ → Prop) : Prop :=
  ∃ (Δ_star : ℝ) (ν_star : ℝ),
    0 < Δ_star ∧ 0 < ν_star ∧
    (∀ a : A, a ≠ a_star →
      env.r (s_star, a_star) - env.r (s_star, a) ≥ Δ_star) ∧
    visitFreq env s_star ν_star

/-- **(P5)** Constrained feasibility. -/
def HasP₅ (env : Env S A O) (F : Set A) (M : ℝ) : Prop :=
  0 < M ∧ F ⊂ Set.univ ∧
  ∀ (s : S) (a : A), a ∉ F → env.r (s, a) ≤ -M

/-- **(P6)** Nonstationarity: reward or transition kernel changes at time tau. -/
def HasP₆ (envs : ℕ → Env S A O) (tau : ℕ) : Prop :=
  ∃ (s : S) (a : A),
    (envs tau).r (s, a) ≠ (envs (tau + 1)).r (s, a) ∨
    (envs tau).trans (s, a) ≠ (envs (tau + 1)).trans (s, a)

/-- **Class C**: satisfies at least one of (P1)–(P6).
    `visitFreq` is threaded to the P4 case; Phase 2 binds it to
    `SixPrimitives.VisitFrequencyAtLeast`. -/
def InClassC (env : Env S A O)
    (visitFreq : Env S A O → S → ℝ → Prop) : Prop :=
  (∃ env' : Env S A O, HasP₁ env env') ∨
  (∃ S_abs : Set S, HasP₂ env S_abs) ∨
  (∃ S_local S_global : Set S, HasP₃ env S_local S_global) ∨
  (∃ (s_star : S) (a_star : A), HasP₄ env s_star a_star visitFreq) ∨
  (∃ (F : Set A) (M : ℝ), HasP₅ env F M) ∨
  (∃ (envs : ℕ → Env S A O) (tau : ℕ), envs 0 = env ∧ HasP₆ envs tau)

end StructuralProperties

-- §6  SANITY CHECKS

section SanityChecks

example : (LacksX₁ (fun _ => 0)) = (LacksX₁ (fun _ => 0)) := rfl
example : (LacksX₂ (fun _ => 0)) = (LacksX₂ (fun _ => 0)) := rfl
example : (LacksX₃ (fun _ => 0)) = (LacksX₃ (fun _ => 0)) := rfl
example : (LacksX₄ (fun _ => 0)) = (LacksX₄ (fun _ => 0)) := rfl
example : (LacksX₅ (fun _ => 0)) = (LacksX₅ (fun _ => 0)) := rfl
example : (LacksX₆ (fun _ => 0) 0) = (LacksX₆ (fun _ => 0) 0) := rfl

-- The constant-zero MI sequence satisfies (F1) with B = 0 < ½.
example : LacksX₁ (fun _ => (0 : ℝ)) := by
  refine ⟨0, by norm_num, ?_⟩
  simp [Filter.limsup_const]

-- The constant-zero bridge-probability sequence satisfies (F3) with C = 1.
example : LacksX₃ (fun _ => (0 : ℝ)) :=
  ⟨1, one_pos, fun T => by norm_num⟩

-- An algorithm with zero infeasible probability possesses X₅ (¬ LacksX₅).
example : PossessesX₅ (fun _ => (0 : ℝ)) := by
  intro ⟨δ, hδ_pos, hδ_le⟩
  have h : liminf (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (0 : ℝ))
               atTop = 0 := by
    simp [Finset.sum_const_zero, Filter.liminf_const]
  linarith [h ▸ hδ_le]

end SanityChecks

end SixPrimitives
