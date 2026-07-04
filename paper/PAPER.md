# Ismail's Primitives

### A Unified Functional Theory of Necessity, Independence, and Sequential Dependence in Adaptive Decision Systems

**Muhammed Ismail**
Independent Researcher
Email: literacity@outlook.com
ORCID: [0009-0000-3713-7105](https://orcid.org/0009-0000-3713-7105)
July 3, 2026

> This is a trimmed, web-readable Markdown edition of the paper, covering the full narrative body (Sections 1–10) and references. The two appendices — a line-by-line Lean ↔ paper correspondence table (Appendix A) and the Lean proofs verifying every environment's class membership (Appendix B) — are omitted here for readability and are available in the [full PDF, archived on Zenodo](https://doi.org/10.5281/zenodo.21177368). The authoritative, machine-checked source is the Lean 4 / Mathlib formalization in [this repository](https://github.com/M-Ismail-ZA/IsmailsPrimitives).

## Abstract

This paper asks one question: what must any decision-maker — a person, an institution, or a machine — get right before sustained success under real uncertainty is even possible? Across investing, operations, public policy, and machine learning, the same six structural failures keep recurring: ambiguity nobody resolves, mistakes nobody can undo, comfortable plateaus nobody leaves, decisions nobody commits to, limits nobody respects, and beliefs nobody updates. The usual response is a patchwork — a regret bound here, a compliance checklist there, a risk framework somewhere else — each useful, none transferable, none provably complete. This paper instead asks what is unconditionally true of any sequential decision process, of any kind, anywhere. The answer is six capabilities, and only six (named X1 through X6 in the body): tracking the true objective, avoiding the mistake you cannot undo, exploring past the comfortable plateau, committing once the evidence is in, respecting the limits that cannot be traded away, and updating when the world changes. Lacking any one of them is not a stylistic weakness; it is a mathematical guarantee of failure that compounds the longer the decision-maker operates — and no other one of the six can substitute for it. None of this is asserted on faith. Every claim, including that no primitive can stand in for another, is verified line by line in the Lean 4 proof assistant, a computer that accepts nothing it cannot check itself; the same six results hold, unmodified, whether the decision-maker is a trading desk, a regulator, a hospital, or a reinforcement-learning agent. Each new domain tested is not merely another example: it returns evidence to the same six claims — evidence that has so far only confirmed them — and the theory invites the next test just as openly as the last.

**Author's note.** The framework, every definition, every theorem statement and proof, and the complete Lean 4/Mathlib formalization underlying this paper are the sole original work of the author — conceived, proved, and machine-verified without co-authors, institutional affiliation, or external funding. The complete formalization is available at [github.com/M-Ismail-ZA/IsmailsPrimitives](https://github.com/M-Ismail-ZA/IsmailsPrimitives).

**A note on structure.** The six movements of the abstract above — stating the question, naming the failures, rejecting the patchwork, committing to six capabilities, holding to a non-negotiable verification standard, and closing on a claim that strengthens with each new test — follow the six primitives in order. This is not ornamental: writing a clear, falsifiable claim about decision-making is itself a sequential decision under uncertainty, so doing it well takes the same six things.

**Keywords:** sequential decision-making; necessity and sufficiency; impossibility theorems; partially observable Markov decision processes; regret bounds; formal verification; Lean 4; cross-domain transfer

## Plain-Language Overview

Imagine equipping a rover for a mission without knowing which planet it will land on, or whether it faces extreme heat, corrosive radiation, or treacherous terrain. The only sound engineering choice is to prepare for every danger you can characterize in advance, even though any single mission will likely meet only a few. This paper does the same for decision-making systems — in investing, operations, public policy, or machine learning — by identifying six structural failures that recur across all of them, and asking exactly three questions about each.

**Is it necessary?** For each of the six structural failures, I build the smallest possible test environment that contains it — one hidden choice, one trap, one tempting-but-mediocre plateau — and prove that any decision process without the matching capability fails that test, permanently and increasingly, not just occasionally. The environments are deliberately toy-like: if a process cannot pass the simplest version of a failure, it has no chance against the messy version that shows up in the real world.

**Is it replaceable?** No. Being good at handling one of the six structural failures does not make a process any better at handling a different one: a model built to flag fraud is not, by virtue of that skill, also a model for regulatory-capital allocation. Each capability has to be separately earned; none can stand in for another.

**Do they work together?** This is the most delicate claim in the paper. The six capabilities assemble into a single forward chain, where having one creates exactly the conditions needed to benefit from the next, looping back at the end so that evidence compounds over repeated cycles rather than resetting. Two of the six links, and parts of several others, still need domain-specific work before the chain's promise is fully cashed out for any given real system: I built the verified scaffolding for that chain and show precisely where the remaining work lies.

Everything past this point is the rigorous version of these same three questions, stated in the language of probability and information theory so every claim can be, and has been, checked by a computer proof assistant rather than taken on faith. Section 1 restates the motivation formally and gives a table translating each capability into investing, operations, and policy language for readers who want to keep reading that way throughout.

---

## 1. Introduction

### 1.1 Why a Unified Functional Theory

Most accounts of what makes a sequential decision process trustworthy are either too narrow or too vague to be portable. A bandit-algorithm regret bound is precise but speaks only to bandits. A risk-management checklist is portable but unfalsifiable — nothing in it is stated sharply enough to be proved false. This paper takes a third path, and names it accordingly: a **Unified Functional Theory** — *unified* because the same small number of structural failures recur across investing, operations, public policy, and reinforcement learning alike, stated abstractly enough that one proof serves all of them at once; *functional* because what is characterized is what a decision process must *do* under uncertainty, never what field it belongs to, what institution runs it, or what it calls itself. For each structural failure, this paper proves an unconditional floor (Part I), a demonstration that none of the others can substitute for it (Part II), and a fully specified — if partly conditional — account of how the six combine into a single forward pipeline (Part III). The six properties that result are referred to throughout as X1 through X6, and the paper's central empirical claim is narrow and falsifiable by construction: each is necessary in a minimal instance of its matching structural failure, and no other one of the six can stand in for it there.

### 1.2 Roadblocks, Not Recipes

Each Part of this paper makes a different kind of claim; treating them as interchangeable is exactly the failure mode this paper exists to diagnose.

Part I places six roadblocks: a roadblock is a minimal condition whose absence guarantees failure regardless of what else a decision process does well — it marks the cliff edge, not a blueprint. Part II proves the six are non-substitutable for every pair, not merely assumed so.

Part III is the only part describing how to move from *not failing* to *actually succeeding*: it requires all six primitives combined in one specific order, not any subset and not an arbitrary sequence. Clearing every roadblock does not by itself describe a path forward; the sequential-dependence chain of Part III is the closest thing this paper offers to one, and states plainly, link by link (Section 8.1), which parts of that bridge are fully built and which are left for a concrete implementation to supply.

This structure also fixes what it means to port this theory into another field. Porting one primitive alone — noticing that decision-makers under uncertainty need good objective-tracking, say — is not the claim this paper makes; it is standard decision theory, studied under its own name for decades. Porting the full union, with the proof that none of the six substitutes for another and the proof of the one sequence that combines them into sufficiency, is a considerably stronger claim, taken up directly in Section 4.3.

### 1.3 Discovered, Not Designed

One claim in this paper is easy to state and impossible to dispute once its premise is granted: if a decision process genuinely faces one of the six structural failures of Section 3 — in the precise, checkable sense defined there, not a loose family resemblance — then the matching primitive is necessary for it, full stop, regardless of field or vocabulary. This is the ordinary behavior of every lower bound and impossibility theorem there has ever been: Arrow's theorem does not care what a voting system calls itself, and the Halting Problem does not care what language a program was written in. A real decision process either has the structure or it doesn't, and no redescription changes which.

That premise — that a given real situation actually has the structure — is a different kind of claim, kept separate here from the necessity result itself. Section 4 argues, with the same evidentiary standard economists have used since Akerlof to show that real markets violate frictionless-equilibrium idealizations, that realistic decision processes generically land in Class C — not by definitional fiat, but because the assumptions that would keep them out (complete information, no irreversible mistakes, no tempting local optima, total flexibility, stationarity) are exactly what economics, control theory, and decision theory have spent decades documenting real markets, institutions, and choices under uncertainty as failing to satisfy. Together, the two claims justify reading every cross-domain example in this paper as substantive rather than decorative.

### 1.4 The Minimality Principle

Every environment in Part I is deliberately the smallest instance of its structural failure that still forces failure — one ambiguous state for X1, one trap for X2, one local optimum for X3, and so on (Section 3.3 states this precisely). This is what licenses reading the results outside reinforcement learning: a necessity result proved on a stripped-down instance is a floor that persists into every messier, real environment containing that instance as a special case, whereas a result proved only on an elaborate instance might be an artifact of the elaboration. The paper's transferability claim rests on this one structural choice, not on an appeal to analogy.

### 1.5 Reading This Paper Outside Reinforcement Learning

The formal apparatus — POMDPs, regret, mutual information — is necessary for the proofs to be machine-checked, but the six properties it characterizes are not specific to reinforcement learning. Table 1 gives one fixed cross-domain reading for each; every subsequent section develops its own primitive's reading in more depth via boxed asides, but the table is what a reader returning to a single section out of order should consult first.

### 1.6 Related Work

The necessity arguments of Part I are in the classical two-point / Le Cam testing tradition used throughout the bandit and sequential decision-making lower-bound literature, and the Fano-type argument behind X4's necessity proof is likewise standard in that tradition; Lattimore and Szepesvári (2020) is a comprehensive modern reference for both techniques and for the regret framework used throughout this paper. The formalization itself is carried out in Lean 4 (de Moura and Ullrich, 2021) on top of Mathlib (The mathlib Community, 2020), the community-maintained library of formalized mathematics that supplies the measure theory, probability, and analysis this paper's proofs are built from.

This paper's contribution relative to that literature is not a new algorithm or a new regret bound, but a different question: not "how fast can regret be driven to zero," but "which structural properties are unconditionally necessary, mutually irreplaceable, and combinable into a single verified pipeline, stated abstractly enough to apply outside reinforcement learning altogether."

### 1.7 Organization

Section 2 fixes notation. Section 3 defines the environment class C and its six structural failures. Section 4 argues that realistic decision processes generically belong to C and gives checkable recognition tests for each structural failure. Section 5 states the (small) amount of general-purpose machinery the rest of the paper actually uses. Part I (Section 6) proves each primitive necessary. Part II (Section 7) proves the six mutually independent. Part III (Section 8) gives the verified logical scaffold for how the six combine, stating plainly which hypotheses are discharged within the paper and which are left for instantiation. Section 9 collects what has and has not been shown; Section 10 closes.

| Primitive | Plain meaning | Outside reinforcement learning |
|---|---|---|
| **X1** Objective Tracking | Tell two live hypotheses apart when they prescribe different actions | A fund that can't distinguish which of two strategies is actually working; a clinical trial that can't tell which arm is better |
| **X2** Cross-Context Safety Transfer | Stop touching the action that locks in permanent loss | A trading desk that won't stop revisiting a blow-up trade; an operation one safety violation away from losing its license |
| **X3** Global Attractor Exploration | Keep probing past a comfortable plateau toward a genuinely better region | A firm stuck at a mediocre-but-safe strategy with no scaling exploration budget; an agency that never pilots anything past a one-off budget |
| **X4** Policy Simplification | Commit decisively once the evidence supports one option | A committee still "deliberating" on a question the data settled quarters ago |
| **X5** Feasibility Projection | Respect a hard constraint rather than trade it off | A regulator-bound allocator that occasionally drifts into the forbidden range because it scored well elsewhere |
| **X6** Feedback Adaptation | Discard stale evidence once the world has changed | A strategy still sized for the regime that ended, or a policy still calibrated to a population that has moved on |

*Table 1: The six primitives outside reinforcement learning. Each row is developed further, with a worked example, in its own subsection of Part I.*

---

## 2. Setup, Notation, and the Canonical Summary

### 2.1 Environments

**Definition 2.1 (Environment).** An environment on a measurable state space *S*, action space *A*, and observation space *O* consists of:

- a stochastic transition kernel `trans : S × A → Δ(S)`;
- a stochastic observation kernel `obs : S × A → Δ(O)`;
- a deterministic, measurable reward function `r : S × A → ℝ`;
- an initial-state probability measure `μ₀` on *S*.

We write `Env(S, A, O)` for this type and *E* for a generic member of it.

```lean
-- Lean 4 / Mathlib — Phase0.lean, lines 32–45
structure Env (S A O : Type*)
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O] where
  /-- Stochastic state transition: (s, a) → distribution over s' -/
  trans : Kernel (S × A) S
  /-- Stochastic observation emission: (s, a) → distribution over o -/
  obs : Kernel (S × A) O
  /-- Deterministic reward: r(s, a) ∈ ℝ -/
  r : S × A → ℝ
  /-- Measurability of r — required for `Kernel.deterministic` in Phase 2. -/
  hr_meas : Measurable r
  /-- Initial state distribution -/
  μ0 : Measure S
  /-- μ0 is a probability measure -/
  hμ0 : IsProbabilityMeasure μ0
```

Two structural conditions recur throughout the paper and are worth fixing notation for now.

**Definition 2.2 (Markov and deterministic environments).** *E* is **Markov** if `trans` and `obs` are genuine probability kernels (every fibre is a probability measure, not merely a sub-probability measure). *E* is **deterministic** if, in addition, `μ0` is a point mass and `trans`, `obs` are point masses at measurable functions of (s, a) — i.e. the environment's own dynamics involve no randomness, only the algorithm's choices do.

### 2.2 Algorithms and the Canonical Summary

**Definition 2.3 (Algorithm).** An algorithm with summary type `Sig` consists of:

- an action kernel `act : Sig → Δ(A)`;
- a summary-update kernel `update : Sig × A × O × ℝ → Δ(Sig)`;
- an initial summary `σ0 ∈ Sig`.

```lean
-- Lean 4 / Mathlib — Phase0.lean, lines 50–59
structure Algorithm (A O Sig : Type*)
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Sig] [TopologicalSpace Sig]
    [BorelSpace Sig] where
  /-- Action selection: depends only on summary σ. -/
  act : Kernel Sig A
  /-- Summary update: (σ, action, observation, reward) → new summary. -/
  update : Kernel (Sig × A × O × ℝ) Sig
  /-- Initial summary. -/
  σ0 : Sig
```

The definition is deliberately restrictive in one respect: `act` takes only the current summary σt as input, never the raw history of past actions, observations, and rewards directly, and never the environment's hidden state. Whatever the algorithm has learned by time *t* must already be compressed into σt; there is no second channel by which the past can leak into the present decision. Every result in this paper is a statement about what shape that compression must take — it is never a statement about an algorithm with secret side-channel access to its own history.

> **Intuition — Operations.** Think of σt as a manager's dashboard, refreshed every period. The manager's next decision can only depend on what the dashboard currently shows — not on the raw transaction log sitting in a filing cabinet she never reopens. If the dashboard is well designed, this costs nothing: a good summary keeps everything decision-relevant. If it is poorly designed, the manager will keep making the same correctable mistake, because the dashboard never surfaced the pattern in the first place. The six primitives are, at bottom, six different ways a dashboard can quietly fail to surface something it needed to.

### 2.3 Trajectories and the Trajectory Measure

**Definition 2.4 (Trajectory).** For T ∈ ℕ, a length-T trajectory is a function ω : Fin(T) → A × O × ℝ, recording the action taken, observation received, and reward earned at each of the first T steps.

Running an algorithm in an environment for T steps induces a probability measure on length-T trajectories, built up one step at a time. Each step, from a current pair (σt, st), generates

```
at ~ act(σt),  ot ~ obs(st, at),  rt = r(st, at),  st+1 ~ trans(st, at),  σt+1 ~ update(σt, at, ot, rt),
```

with at, ot, st+1, and σt+1 conditionally independent given (σt, st, at) as appropriate, and the t-th coordinate of the trajectory set to (at, ot, rt). Notice that the observation, the reward, and the new state are all generated from the same pre-transition pair (st, at) — in particular the summary update sees ot and rt but never st+1 directly, exactly as it must if the algorithm is to have no access to the environment's hidden state except through what it observes.

**Definition 2.5 (Trajectory measure).** For an environment *E*, algorithm `alg`, and horizon T, the construction above defines a measure `trajMeasure(E, alg, T)` on `Trajectory(A, O, T)`. When *E* is Markov and `alg`'s kernels are genuine probability kernels, this measure is a probability measure.

### 2.4 Value, Regret, and the Oracle Baseline

**Definition 2.7 (Algorithm value and optimal value).** The value of `alg` in *E* at horizon T is its expected cumulative reward. The optimal value `optValue(E, T)` is the supremum of `algValue(E, alg, T)` over *every* summary type and *every* algorithm on it whose kernels are genuine probability kernels — not just over some fixed reference class.

> **Intuition — Investing.** `optValue` is not "the best fixed strategy" or "the best strategy from some pre-approved playbook." It is the best any conceivable strategy, of any complexity, could have achieved with full hindsight knowledge of the environment's dynamics — the same role a perfect-foresight benchmark plays when grading a fund manager. Defining the baseline this generously is what makes a regret bound meaningful: an algorithm cannot be let off the hook by comparing it only to a weak competitor.

**Definition 2.8 (Regret).** `regret(E, alg, T) := optValue(E, T) − algValue(E, alg, T)`. `alg` has **sublinear regret** in *E* if `regret(E, alg, T) ≤ εT` eventually, for every ε > 0; it has **linear regret** if there is a fixed c > 0 with `regret(E, alg, T) ≥ c(T − t₀)` eventually, for some t₀.

*Remark 2.9. Sublinear and linear regret are not exhaustive opposites stated this way — an algorithm could in principle have regret that oscillates between the two regimes forever. Necessity results (Part I) sidestep this by proving linear regret outright, which is always sufficient to rule out sublinearity.*

### 2.5 The Failure and Possession Hierarchy

Each primitive Xi is pinned down by a single real-valued sequence summarizing the algorithm's behaviour relevant to it (a mutual-information sequence for X1, a danger-action probability sequence for X2, and so on). Independently of that choice, three nested behaviours are defined once, abstractly, over any such sequence.

**Definition 2.10 (Failure conditions F1–F6).** An algorithm, summarized by the relevant sequence, *lacks* Xi if:

- **F1**: its mutual-information sequence `mi` satisfies `limsup mi(t) ≤ B` for some B < 1/2;
- **F2**: its danger-probability sequence `dangerProb` satisfies `dangerProb(k) ≥ δ` for all k, for some fixed δ > 0;
- **F3**: its cumulative bridge-count sequence `cumBridge` satisfies `cumBridge(T) ≤ C` for all T, for some fixed C > 0;
- **F4**: its conditional-entropy sequence `condEnt` satisfies `liminf condEnt(t) ≥ ε` for some fixed ε > 0;
- **F5**: its infeasible-play sequence `infeasProb` has Cesàro average satisfying `liminf T⁻¹ Σ infeasProb(t) ≥ δ` for some fixed δ > 0;
- **F6**: its stale-arm probability sequence `staleProb` satisfies `staleProb(t) ≥ 1/2 + δ` throughout a nonempty post-changepoint window (τ, (1+ε)τ], for some fixed ε ∈ (0, 1/2] and δ > 0.

**Definition 2.11 (Possession — ordinary and robust).** Ordinary possession of Xi is simply the negation of lacking it: `PossessesXi := ¬LacksXi`. Robust possession is a strictly stronger, quantitative guarantee with its own shape for each i — for instance, robust X1 asks for `liminf mi(t) > 1/2` outright (not merely that the limsup fails to stay at or below some B < 1/2), and robust X2 asks for the danger probability to converge to 0 (not merely to fail to stay bounded away from 0).

*Remark 2.12 (The hierarchy is non-vacuous). Robust possession implies ordinary possession for each i, immediately from the definitions and the elementary fact liminf ≤ limsup.*

> **Intuition — Investing.** Ordinary possession is a low bar: it just means the desk hasn't been caught failing in the specific, worst-case way Fi describes. Robust possession is the bar a regulator or an LP would actually want met: not merely "has not yet blown up," but "demonstrably trending toward the safe regime, with a quantitative rate." Part I (Necessity) only ever needs the weak bar — lacking Xi is already enough to force linear regret. Part III (Sequential Dependence) needs the strong bar, because a chain of merely-not-yet-failing primitives gives no guarantee about what happens next.

---

## 3. The Environment Class C

An environment belongs to C if it exhibits at least one of six structural failures. It need not exhibit all six, and it need not be adversarial in any other respect — C is defined by the presence of a single qualifying difficulty, not by general-purpose hardness. This is deliberate: the necessity results of Part I show that each structural failure, on its own, already forces failure on an algorithm lacking the matching primitive, so membership via any single property is enough to make that primitive indispensable.

### 3.1 The Six Structural Properties

**Definition 3.1 (Structural properties P1–P6).**

- **P1 — Reward ambiguity.** There is a hidden parameter Θ* ∈ {0, 1} and a state s at which the two possible environments disagree about which of two actions a₀ ≠ a₁ is optimal.
- **P2 — Absorbing traps.** There is a proper, nonempty set of states S_abs that, once entered, can never be left, every reward earned inside it is ≤ 0, and it is reachable with positive probability from outside.
- **P3 — Local optima.** There are disjoint nonempty sets of states S_local, S_global such that the myopically-best action at any state in S_local keeps you in S_local, some non-myopic action can reach S_global with positive probability, and the best reward obtainable in S_local is strictly below the best reward obtainable in S_global.
- **P4 — Deterministic optimality.** There is a single optimal state-action pair (s*, a*) with a fixed positive reward gap Δ* over every other action at s*, together with a promise that s* is visited with frequency at least ν* > 0.
- **P5 — Constrained feasibility.** There is a proper, nonempty set of feasible actions F such that any action outside F, at any state, earns reward at most −M for some fixed M > 0.
- **P6 — Nonstationarity.** The environment is really a sequence of environments that differs, in reward or in transition dynamics at some state-action pair, between time τ and time τ + 1.

### 3.2 Class Membership

**Definition 3.2 (Class C).** *E* ∈ C if *E* exhibits at least one of P1–P6.

### 3.3 Minimality

Each property above is stated with the fewest moving parts that still force the corresponding failure. P1 needs only one ambiguous state and two candidate actions, not an arbitrary reward landscape; P2 needs only that the trap be reachable and non-positive inside it, not that it be catastrophic; P5 needs only one infeasible region with a uniform penalty, not a complex constraint set. This is a design choice, not an incidental simplification, and it is what makes the necessity results of Part I load-bearing for environments far more complicated than the ones actually used in the proofs.

*Remark 3.3 (Why minimality matters for transfer). A necessity proof carried out on a stripped-down instance of a structural failure is stronger, not weaker, than one carried out on an elaborate instance: every harder environment exhibiting the same qualitative structural failure — more states, more actions, a richer trap, a messier constraint set — contains the minimal instance as a special case of the difficulty an algorithm must overcome. An algorithm that cannot clear the minimal bar has no prospect of clearing a higher one. Conversely, this paper makes no claim that clearing the minimal bar is sufficient for harder instances of the same structural failure; sufficiency is handled separately, and only for the forward pipeline of Part III, under its own stated conditions.*

> **Intuition — Public Policy.** A welfare program that cannot handle the simplest possible version of "some recipients will react to incentives in the intended way and some won't" has no chance with the real, messier population it will actually serve. Testing policy design against minimal, almost toy-like adversarial cases is not a weaker test than testing it against a fully realistic simulation — it is a more diagnostic one, because failure on the simple case cannot be blamed on incidental complexity.

---

## 4. From Formal Environments to Real Decision Structures

Section 1.3 previewed two claims and insisted they be kept apart. This section makes both precisely, in the order that matters: what kind of claim each one is, why the second is not debatable once its premise holds, and how to check the premise without fooling oneself in either direction.

### 4.1 Two Claims, Not One

**Claim A (representation).** A sequential decision process facing genuine uncertainty — an agent that acts, a world that responds stochastically, partial information about which state obtains, and a quantifiable consequence — can be formalized as an environment in the sense of Definition 2.1.

**Claim B (inescapability).** If an environment, however arrived at, instantiates one of the six structural properties of Definition 3.1, then the matching necessity result (Part I) applies to it with exactly the force it applies to the purpose-built environments of this paper.

Claim B is a theorem about a fixed formal object and needs no further argument beyond Part I itself. Claim A is a different kind of statement: it asserts a correspondence between an open-ended class of real situations and a formal structure, and no proof assistant can check it, for the same reason none can check the Church–Turing thesis. This paper does not pretend otherwise. What it offers instead is the same kind of case a thesis like that has always been argued on: convergent practice across independent fields, plus a theorem (von Neumann and Morgenstern) that closes the one gap in the representation that looks most like an arbitrary choice.

### 4.2 Why Realistic Decision Processes Generically Land in Class C

The state/action/observation/transition/reward structure of Definition 2.1 is the standard general-purpose formalism for sequential decision-making under uncertainty across robotics, operations research, control theory, and medicine (Kaelbling et al., 1998). Von Neumann and Morgenstern (1944) prove that any preference ordering over uncertain outcomes satisfying four mild axioms (completeness, transitivity, continuity, and independence) is representable as maximizing the expectation of some real-valued utility function — the independence axiom is the most contested (the Allais paradox is the classical objection), so this is a conditional foundation, not an unconditional one, though it is the one nearly every quantitative field already builds on.

Granting the representation, does a realistic process actually land in C? Here the case is empirical, and economics has been making it for half a century under a different name. Arrow and Debreu (1954) prove that competitive equilibrium is optimal under an idealized complement of C. Akerlof (1970) shows that ordinary markets violate the completeness of information — exactly P1 under a different name. The macroeconomic literature on structural breaks following the Lucas critique is P6 under a different name; technology lock-in and poverty-trap models are P3; systemic-risk and financial-contagion models are P2. None of this paper's six structural failures needed to be invented; each already has a name and a literature in at least one field that is not reinforcement learning, which is itself evidence for Claim A independent of anything proved in this paper.

### 4.3 The Literature Tests One Failure at a Time

The standard practice in regret-lower-bound work is to isolate a single source of hardness. Lattimore and Szepesvári (2020) builds essentially every lower bound in the bandit and reinforcement-learning literature around one hard instance engineered for one specific difficulty; combining several distinct hardness mechanisms into a single instance, with a separate necessity proof for each, is not how the technique is used there or, to this paper's knowledge, used anywhere else in that literature. Even where researchers have deliberately tried to test many capabilities at once — Osband et al. (2020)'s bsuite — the same one-at-a-time discipline holds: each environment isolates one or a small number of core capabilities. Where the literature has tried to combine even just two structural properties formally — safety and nonstationarity — the result is not a unified solution but an open problem: a 2026 survey describes their combination as remaining "one of the most challenging topics of research" (Tomashevskiy, 2026), and recent empirical work attempting exactly that combination finds that current methods cannot satisfy both simultaneously (Coursey et al., 2026).

Against that backdrop, the claim this paper makes is precise rather than sweeping: six structural properties, each shown individually necessary in its own minimal environment (Part I), with every one of the thirty ordered pairs shown irreplaceable by the other (Part II), unified under one machine-checked formal apparatus. To this paper's knowledge, no prior formalization combines this many independently-proven-necessary structural properties into a single class with proven mutual independence across all of them. This is not a claim that six is exhaustive or that no harder combination could be built — only that the union itself, and the discipline of proving every pair of its components irreplaceable rather than assuming it, is new.

This distinction matters beyond the count of properties combined. Porting a single primitive into a new field is neither new nor, alone, especially informative. What porting one fragment cannot supply is any guarantee that competence at that fragment says something about the other five — and Part II is precisely the proof that it does not. This is the mechanism behind a familiar practical failure: a consultancy, fund, or regulator that has rigorously verified a client's objective-tracking has tested one fractured property of Class C, not the environment the client is actually in.

### 4.4 The Disciplines This Required

Assembling Class C and the three results proved over it drew on several disciplines that do not, in ordinary practice, share a department, a conference, or a referee pool. Part I's necessity proofs are built from measure-theoretic probability and the two-point/Le Cam and Fano techniques standard to sequential-decision lower bounds. Part II's independence argument is a reduction, in the same spirit complexity theory uses the term: thirty pairwise hardness constructions collapse to one fixed-policy template checked against six characterizations Part I had already proved, rather than thirty separate direct arguments. Part III's closing link rests on genuine martingale theory — an actual Doob convergence argument over a cycle-indexed filtration, not a restatement of Part I's techniques. None of the above means anything without the discipline of formal verification itself: every definition and every theorem is machine-checked in Lean 4 over Mathlib, with zero `sorry`, zero custom axioms, zero `opaque` terms. And reading any of it outside reinforcement learning at all draws on the representation-theorem tradition of decision theory and economics — von Neumann and Morgenstern, Arrow and Debreu, Akerlof — not the bandit literature.

None of the formal definitions underneath any of this carry domain vocabulary. `Env`, HasP1–HasP6, and `InClassC` are stated over abstract measurable state, action, and observation types and never mention reinforcement learning, economics, or any other field, by inspection. The cross-domain readings throughout this paper are therefore not adaptations of a reinforcement-learning result to new territory: the result was never reinforcement-learning-specific to begin with, so recognizing that a fund, a regulator, or a consultancy engagement instantiates HasP2 is not porting a theorem across a boundary — the theorem was never stated on one side of a boundary in the first place.

That this particular combination had not been assembled before Section 4.3 checked for is not an accident of oversight: academic incentive structures reward depth within a single silo, not breadth across several. Promotion committees, conference referee pools, and one-to-three-year grant cycles all evaluate against a single subfield's norms, rewarding extension of an established paradigm over assembling one from parts with no shared home discipline — and none of this is a flaw; each is well suited to producing steady, reviewable progress within a field. None is suited to a project requiring simultaneous fluency in measure-theoretic probability, information theory, sequential-decision lower-bound construction, martingale convergence, and machine-checked formal verification, sustained across an arc with no publishable intermediate unit until independence and sequential dependence both close over all six primitives at once.

Freedom from institutional constraints is necessary for this kind of work and manifestly not sufficient for it — most work produced outside institutional settings stays within one silo too, by choice or convenience. What closes the gap is every discipline listed above present in one place, sustained long enough for all three parts to close together; that this combination is rare is a structural fact about how those disciplines are organized, not a claim this paper needs to make about the person who assembled it. This paper is offered as a case study in what crossing those silos deliberately can produce.

### 4.5 No Rhetoric Escapes a Genuine Instance

Granting Claim A's premise for a specific situation is a factual, falsifiable modeling question. But once that question is answered — once a real process is shown, under any faithful formalization, to instantiate Pi — disputing the conclusion by redescribing the situation in different words changes nothing, for the same reason recompiling a halting program under a different variable-naming convention does not make it run forever. A fund that calls its absorbing trap a "concentrated high-conviction position" is still describing P2. A committee that calls its failure to commit "maintaining strategic flexibility" is still describing P4. The mathematics was never reading the label.

This cuts in both directions. A process that is not actually facing one of the six structural failures is not bound by the matching necessity result merely because it superficially resembles one. The power of a precise structural failure definition is exactly that it can be correctly judged absent, not only correctly judged present.

### 4.6 Recognizing the Six Structural Failures in Practice

Each test below is stated to be passed *or failed* by a real situation — the failure case is included deliberately, because a test nothing can fail is not a test. But these are diagnostic questions about one primitive at a time, and Class C is a union, not six independent checkboxes to clear in sequence and forget. A real decision process is not held fixed while one test is checked against it: the "not this" boundary for every test below implicitly assumes the reader's read of the situation (X1) and the currency of that read (X6) are already reliable. When they are not, a scenario that appears to clear one primitive's test can be exactly the visible symptom of a different, already-active failure — and left unaddressed, that failure does not sit inertly; it can compound into what a later primitive's test would flag, or into a trap no single test was checking for at all. This mirrors, informally, the same directed structure Part III proves formally in the other direction (Section 8): if possessing Xi is what creates the conditions to benefit from Xi+1, persistently failing to exercise Xi does not leave Xi+1's test neutral either. This mirror claim is a practical corollary of taking Class C's union seriously across time, not itself one of Part III's machine-verified theorems — it is offered here as an instruction for how to use the six tests, not as a seventh one.

**P1 — Reward ambiguity.** At least two live courses of action; you cannot tell which is better today; only outcomes observed over time can. *Not this:* a choice between two options where one is already well-documented to dominate, provided that documentation is current — a dominance relationship that held once but has not been re-examined since is a live P6 question wearing P1's clean-pass language.

**P2 — Absorbing trap.** A specific action or pattern that, once taken, locks you into a state with no recovery path and no further upside. *Not this, cleanly:* a loss consistent with ordinary variance around a strategy that objective-tracking still supports — nothing about the read has changed, and next period's expected value is unchanged. *Not a clean pass, despite appearances:* taking the same loss and simply expecting the next cycle to recover it, without re-checking whether anything about the market or the strategy has actually changed. That expectation is not evidence against P2; it is what a live P6 failure — an unexamined belief carried forward unchanged — looks like from the inside, and repeating it is exactly how a run of ordinary-looking quarters can walk a desk into a state that functions as a trap, one small step at a time, with no single moment that looked like a door closing.

**P3 — Local optimum.** The best-looking option right now is not the option that leads to the best long-run outcome, and reaching the better outcome requires deliberately accepting worse results for a while. *Not this:* a free improvement available at no cost — if reaching the better region costs nothing, there is no trap to escape. Though an improvement that is genuinely free and stays untaken regardless is worth asking whether it has been recognized as better at all, which is P1's question, not P3's.

**P4 — Commitment failure.** The evidence already available decisively favors one option, and the choice is still being treated as open. *Not this:* an honest case where material new evidence is still arriving and could still overturn the leading option — premature commitment there would be the actual mistake.

**P5 — Hard constraint.** A specific region of actions is not merely worse but categorically off-limits, with no exchange rate against performance elsewhere. *Not this:* a soft preference, like favoring lower volatility, that trades off smoothly against other goals — P5 requires a wall, not a preference. A constraint that was a wall until it became inconvenient, and was then redescribed as a preference, was never actually reclassified; it was violated.

**P6 — Regime change.** The underlying relationship being relied on has actually changed. *Not this:* a single surprising outcome fully consistent with an unchanged underlying process — ordinary noise is not a regime change, provided the same explanation is not being reached for every time. A pattern of surprises, each individually dismissed as noise, is no longer describable as a single surprising outcome.

A process can fail every test and sit safely in Cᶜ, the idealized complement — Section 4.2's claim is that this is the exception in practice, not that it is impossible in principle. But a single, one-time pass through all six tests is weaker evidence for that exception than it looks: because the tests are not independent of each other, a real process's best defense is not a clean audit taken once, but the same six primitives, actually possessed, rechecked as the cycle turns.

---

## 5. Standard Tools

Exactly one chain of general-purpose machinery is actually load-bearing across the rest of the paper: Shannon entropy and conditional entropy in their measure-theoretic form, and a Fano-type bound connecting conditional entropy to error probability.

**Definition 5.1 (Entropy and conditional entropy).** For a finite-valued random variable X and a sub-σ-algebra F, the conditional entropy H(X | F), and the (unconditional) entropy H(X) := H(X | ⊥).

**Lemma 5.2.** H(X | F) ≤ H(X) for every F. If X = f∘Y for a measurable f and F is at least as fine as Y's generated σ-algebra, then H(X | F) = 0.

These two facts are exactly what makes every forward link in Part III collapse the conditional term to 0 via determinism, and what makes liminf / limsup bookkeeping throughout Part III well-posed.

**Definition 5.3 (Binary entropy and its inverse).** H(q) := −q log q − (1−q) log(1−q) for q ∈ [0,1]. On (0, 1/2), H is a strictly increasing bijection onto (0, log 2); its inverse H⁻¹ is used in Theorem 6.21.

**Lemma 5.4 (Fano, conditional-entropy form).** Let A be a two-valued random variable, a* a distinguished value, and X any random variable. If H(A | X) ≥ ε for some ε ∈ (0, log 2), then P(A ≠ a*) ≥ H⁻¹(ε).

*Remark (Left for the bridge, not left over). Fourteen declarations in Phase 1 are never invoked by any theorem in Parts I–III. They are not incidental — each sits adjacent to a specific obligation Part III leaves open, positioned for whoever instantiates the chain rather than walked by this paper.*

*Hypothesis testing: `klDiv`, `tvDist`, `pinsker_inequality` (bounding TV distance by √(KL/2)) — the bridge between Part III's native currency (entropy, mutual information) and Part I's (the TV-distance argument X1 carries out directly). `data_processing_tv` formalizes that passing two distributions through the same channel cannot manufacture distinguishability that was not already there — the tool that would let an implementer* prove *an `IsSufficientSummary` claim rather than assume it, which is what every theorem in Part III currently does. `sum_error_ge_one_sub_tv` is the general-PMF version of the Le Cam step X1's proof performs by hand for its one minimal witness — what generalizes X1 beyond that witness.*

*Bernoulli-KL calibration: `klBern`, `bernoulli_kl_lower_bound`, `bernoulli_kl_upper_bound`, calibrated to precisely the 1/2±Δ shape X1's and X6's environments already use — what concretizing the fully abstract RobustX4/RobustX5 propositions in IET 4 and IET 5 for an actual bandit-shaped algorithm would run through.*

*Mixture and divergence: `mixPMF`, `JSD`, `jsd_le_quarter_kl_sym`. JSD's range is [0, log 2] — exactly the ceiling every forward theorem in Part III converges toward — making it a candidate for what `MI_Summary_Seq`'s convergence claims would be derived from, rather than assumed.*

*Martingale convergence: `azuma_hoeffding` upgrades IET 6's qualitative almost-sure martingale convergence to a quantitative rate. `kronecker_lemma` is the classical bridge from a summable-series condition to Cesàro-average convergence — RobustX5 is defined as exactly such an average — connecting IET 6's martingale apparatus to an X5-shaped averaged guarantee elsewhere in the chain.*

*Every necessity, independence, and sequential-dependence result in this paper is proved using only the entropy/Fano chain above, plus elementary analysis local to each proof. The fourteen tools above were not needed to prove what this paper proves. They were needed, and left in place, for what this paper does not.*

> **Intuition — Operations.** Fano's inequality, in this form, says something almost mundane: if a predictor's residual uncertainty about a binary outcome — after seeing everything it's going to see — is still substantial, then it must sometimes guess wrong, at a rate the residual uncertainty pins down quantitatively. "Still genuinely unsure" and "sometimes wrong" are, quantitatively, the same fact viewed from two sides.

---

## 6. Part I — Ismail's Proof of Primitive Necessity

Each primitive is shown necessary by the same recipe. A minimal environment exhibiting one structural failure from Section 3 is exhibited; an algorithm is shown to suffer linear regret in that environment whenever it lacks the matching primitive (in the ordinary, weak sense — the floor is proved against the weakest plausible failure). Linear regret is always enough to rule out sublinear regret. Six such results are proved; each is self-contained and uses only its own environment, never the other five.

### 6.1 Objective Tracking (X1)

**Definition 6.1.** Fix a gap parameter Δ ∈ (0, 1/2). Two stateless, two-armed bandit environments are defined: in E₁⁽⁰⁾, arm 0 pays 1/2+Δ and arm 1 pays 1/2−Δ; in E₁⁽¹⁾ the two arms are swapped. The two environments agree on everything except which arm is better.

**Theorem 6.5 (Necessity of X1).** For any algorithm `alg` (with Markov kernels) lacking X1 relative to (E₁⁽⁰⁾, E₁⁽¹⁾), there is a constant c > 0 such that, eventually, c·T ≤ regret(E₁⁽⁰⁾, alg, T) + regret(E₁⁽¹⁾, alg, T).

*Proof sketch.* Fix B < 1/2 witnessing the failure and η > 0 with B+η < 1/2; since mi(t) ∈ [0,1] always, limsup mi ≤ B gives mi(t) < B+η eventually. A direct computation shows the per-step reward gap in E₁⁽⁰⁾ at step t is 2Δ·P₀(At=1), and symmetrically for E₁⁽¹⁾. Since actions are binary, the total variation distance between the two action laws equals |P₀(At=0) − P₁(At=0)|, giving the classical Le Cam two-point bound P₀(At=1) + P₁(At=0) ≥ 1 − mi(t) > 1/2 for t large enough. Summing the per-step gaps gives the stated linear bound.

The complete machine-checked proof (`necessity_x1`, Phase3.lean, ~440 lines) is available in the [repository](https://github.com/M-Ismail-ZA/IsmailsPrimitives). The proposition itself is standard: this exact two-point construction is presented as a worked example in Lattimore and Szepesvári (2020).

> **Intuition — Investing.** Picture two possible worlds that agree on everything except which of two strategies is the winning one, and no other signal in the data distinguishes them faster than the algorithm's own trades do. If the algorithm's trading pattern looks statistically similar across both worlds, then in at least one of the two worlds it is persistently overweighting the losing strategy. The size of that persistent error, multiplied by the gap between the two strategies' returns, is a drag that accumulates linearly, forever, no matter how much capital or time the desk has.

### 6.2 Cross-Context Safety Transfer (X2)

**Definition 6.7.** Fix K ∈ ℕ>0. The environment E2(K) has states {0, ..., K−1, K, K+1}. From any corridor state s < K: action 0 ("safe") earns reward 1 and advances to s+1; action 1 ("danger") earns reward 0 and jumps straight to state K+1. State K is a safe harbor — every action keeps you there, earning reward 1 forever. State K+1 is the trap — every action keeps you there, earning reward 0 forever.

**Theorem 6.11 (Necessity of X2).** Fix δ ∈ (0,1]. If, for every k, the algorithm's conditional danger probability at step k is at least δ, then `alg` has linear regret in E2(K), with regret eventually at least (1 − (1−δ)^K)(T − K).

*Proof sketch.* Surviving K corridor steps requires avoiding the δ-probability danger event at each one, conditional on having survived so far; this forces the survival probability ≤ (1−δ)^K by induction. Splitting the expectation over the trapped and surviving events gives the stated linear regret bound.

> **Intuition — Operations.** A single irreversible mistake — the regulatory violation that triggers a license revocation, the safety bypass that causes a fatal accident, the leverage call that wipes the account — caps everything that follows, no matter how well things had been going up to that point. The relevant question is never "how often does this go wrong on average," which can look small even as the firm slides toward the trap; it is "how often does this go wrong, given that it hasn't gone wrong yet." An operation that gambles at a steady conditional rate, survival after survival, is on a clock — the probability of eventually hitting the trap converges to certainty, and the regret of having built on top of that gamble grows without bound.

### 6.3 Global Attractor Exploration (X3)

**Definition 6.13.** Fix a bridge-success probability p ∈ [0,1]. The environment E3(p) has two states: 0 ("local") and 1 ("global"). State 1 is absorbing and pays reward 1 forever. From state 0: action 0 ("stay") deterministically stays at 0 and pays 1/2; action 1 ("bridge") pays 0 this step and moves to state 1 with probability p, otherwise stays at 0.

**Theorem 6.15 (Necessity of X3).** Fix Ctot > 0. For every horizon T ≥ 4·Ctot², if an algorithm's cumulative bridge-action count never exceeds Ctot at any horizon (in the instance E3(1/√T)), then regret(E3(1/√T), alg, T) ≥ T/2 − (1+Ctot)√T.

*Proof sketch.* Reaching the global state at all requires at least one of at most Ctot bridge attempts to succeed, each independently with probability 1/√T; a union bound caps the probability of ever reaching it, capping algorithm value near T/2. The reference algorithm that always attempts the bridge reaches the global state, in expectation, within √T attempts and then collects near-full reward for the rest of the horizon.

The environment is the minimal case of a long-standing benchmark family — introduced as RiverSwim by Strehl and Littman (2008) and used since as the Chain MDP by Osband et al. (2016), among many others.

> **Intuition — Investing.** A fund sitting on a comfortable, reliably mediocre strategy earning "half of what's possible" will never discover the better regime if it only ever allocates a small, fixed, one-off research budget to exploring it — the discovery either happens early, by luck, within that fixed budget, or it never happens. Larger fixed budgets help, but only up to a fixed cap; the cap has to keep growing with the time horizon faster than √T for genuine discovery to become likely as the fund operates longer. A one-time pilot program is not the same commitment as an exploration budget that scales with how long the firm has been running.

### 6.4 Policy Simplification (X4)

**Definition 6.18.** E4 has one state, two actions, no transitions to track: action 0 always pays reward 1, action 1 always pays reward 0.

**Theorem 6.22 (Necessity of X4).** Any algorithm lacking X4 in E4 has linear regret in E4.

*Proof sketch.* Fano's inequality (Section 5) converts a conditional-entropy floor on the action taken into a floor on the probability of taking the wrong action at every relevant step, and since action 1 costs exactly one unit of reward relative to action 0 in E4, summing this per-step error probability gives a linear regret floor directly.

The general link between residual entropy over an optimal action and regret is Russo and Van Roy (2016)'s information-theoretic framework; the specific zero-uncertainty construction used here does not appear to be pre-stated in that or related work.

> **Intuition — Consulting.** This is the only one of the six environments with no real dynamics at all — one state, one obviously correct call, forever. Failing here isn't about facing a hard problem; it is about a decision process that keeps re-litigating an already-settled question. A committee that, after years of the same evidence arriving every quarter, still spends real deliberation time genuinely torn on a question with one clearly correct answer is not being careful — the carefulness was appropriate once, before the evidence came in. Continued indecision after the evidence is no longer prudence; each quarter spent still "deciding" is a quarter paying the cost of the wrong answer half the time.

### 6.5 Feasibility Projection (X5)

**Definition 6.24.** E5 has a continuous action space A = ℝ and a single state. The feasible set is F = [0, 1/3] ∪ [2/3, 1]. A feasible action earns a reward peaking at 1 at a=0 or a=1 and falling linearly toward the forbidden middle band. Any infeasible action earns a flat penalty of −1.

**Theorem 6.26 (Necessity of X5).** Any algorithm lacking X5 in E5 has linear regret in E5.

*Proof sketch.* Every feasible reward is at most 1 and every infeasible reward is exactly −1, so each step's expected reward is capped below optimal by a term proportional to the probability of infeasible play at that step; averaging over a horizon and comparing against `optValue = T` gives a linear regret floor.

Hard-constraint bandit settings are an established area, e.g. Badanidiyuru et al. (2018); the specific minimal construction used here, with a fixed penalty and no budget mechanism, does not appear to be pre-stated there.

> **Intuition — Public Policy.** A regulatory or budget constraint is not a soft preference to be traded off against performance — it is a wall. An allocator who occasionally drifts into the forbidden range, even while doing well everywhere else, is not running a slightly-suboptimal version of a compliant strategy; it is running a strategy that periodically pays a fixed, large penalty for crossing a line that should never be crossed at all. A persistent habit of occasionally stepping over the line, rather than a one-off lapse, guarantees a bill that grows without bound the longer the allocator operates.

### 6.6 Feedback Adaptation (X6)

**Definition 6.28.** Fix a horizon T and gap Δ ∈ (0, 1/4]. Let τ = ⌊T/2⌋. Before τ, arm 1 pays 1/2+Δ and arm 0 pays 1/2−Δ; after τ the two arms swap. A single, fixed changepoint flips which arm is better exactly once, halfway through the horizon.

**Theorem 6.31 (Necessity of X6).** Fix Δ ∈ (0,1/4], ε ∈ (0,1/2], δ > 0, and τ = ⌊T/2⌋. If the stale-arm probability stays at least 1/2+δ throughout the post-change window (τ, ⌊(1+ε)τ⌋], then there is c > 0 and d ∈ ℝ such that c·T − d ≤ regret(E6(T,Δ), alg, T).

*Proof sketch.* Throughout the post-change window, favoring the stale arm with excess probability δ above even odds costs at least 2δΔ in expected reward per step relative to the now-correct arm; the window has length on the order of εT/2, so the accumulated cost over the window alone is already linear in T.

This is the single-changepoint specialization of the switching-bandit analysis of Garivier and Moulines (2011), an entire established subfield since 2011.

> **Intuition — Investing.** A regime change in markets — a rate environment shift, a structural break in a relationship the strategy depended on — doesn't announce itself with a label. A strategy that keeps allocating to what worked in the old regime, with real conviction, well into the new one isn't being patient; it is paying the gap between the old winner and the new winner, every period, for as long as the stale belief persists. The fix isn't forecasting the regime change in advance — it's not clinging to old evidence past the point where it stopped describing the world, and that is a property of the decision process, not of how good its predictions were going in.

This completes Part I. All six primitives are necessary, each witnessed by its own minimal environment, each using only the weak (ordinary) sense of lacking the primitive — the strongest form of the claim available.

---

## 7. Part II — Ismail's Proof of Primitive Independence

For each ordered pair (i, j) with i ≠ j, the algorithm built to handle Xj's own structural failure is shown to lack Xi when redeployed in Xi's home environment — the same six environments from Part I, with no new construction needed. Thirty such pairs cover every off-diagonal cell of a 6×6 grid.

### 7.1 The Challengers

Every challenger is built from one template: a fixed (possibly randomized) policy that never updates its summary at all. Six such challengers are instantiated — one per primitive, each carrying the fixed policy that happens to survive its own home structural failure (never gamble, never touch the danger action, never bridge, never commit, never play the forbidden midpoint, never adapt).

*Remark 7.1 (Why independence falls out almost for free). Each primitive's own structural failure is survivable by some fixed, non-adaptive policy. A policy that is fixed in this sense carries no information about which environment it is actually in, so it is exactly the kind of object Part I's necessity proofs already rule out for every other structural failure. Independence here is a direct consequence of necessity, not a separate phenomenon.*

### 7.2 Two Worked Examples

**Example 7.2.** A deterministic challenger, redeployed on X1's home turf, always plays arm 0 regardless of which of E₁⁽⁰⁾, E₁⁽¹⁾ it is actually in. The two action marginals at every horizon are therefore identical point masses; the total variation distance between them is identically 0, and the algorithm lacks X1.

**Example 7.3.** Any challenger built from a fixed 50/50 randomizer plays the dangerous action with conditional probability exactly 1/2 at every step, regardless of survival history, since the policy never looks at its own summary. This is proved once, generically, and reused for all five algorithms tested against X2's home turf.

| Home turf | Lacked by | Witnessing policy |
|---|---|---|
| E1 (vs. X1) | algs 2,3,4,5,6 | constant arm 0 |
| E2 (vs. X2) | algs 1,3,4,5,6 | constant 50/50 |
| E3 (vs. X3) | algs 1,2,4,5,6 | never bridges |
| E4 (vs. X4) | algs 1,2,3,5,6 | never commits |
| E5 (vs. X5) | algs 1,2,3,4,6 | constant action 1/2 (always forbidden) |
| E6 (vs. X6) | algs 1,2,3,4,5 | never adapts |

*Table 3: The thirty home-turf failures.*

**Theorem 7.4 (Mutual independence).** All thirty pairs hold simultaneously — proved as one master theorem (`mutual_independence`, Phase4.lean) combining all thirty component lemmas.

> **Intuition — Operations.** A fraud-detection model is not, by virtue of being good at fraud detection, also a model for regulatory-capital allocation, even though both get filed under "risk management." Competence at one specific structural failure is not a general-purpose property that happens to transfer; it is the result of a specific adaptation to a specific problem, and the simplest version of that adaptation — the fixed rule that handles this one thing and nothing else — is definitionally blind to every other problem in the building. None of the six primitives is a proxy for any of the others; each has to be separately earned.

---

## 8. Part III — Ismail's Formally-Verified Bridge Towards Sufficiency

### 8.1 What This Part Proves, and What It Defers

This structure follows from an asymmetry between what Necessity and Sequential Dependence each claim. Failure has one shape: an algorithm either has the structural property survival requires, or it does not — and if not, the outcome is linear regret, full stop, independent of what else the algorithm does well or how success is defined. This is why Part I is unconditional throughout: necessity closes the moment the structural failure is granted, requiring nothing about the algorithm's aims beyond surviving it. Success has no comparable single shape; what sufficiency looks like depends on the environment, the goal variable, and choices no necessity argument can make on an implementer's behalf. Part III is honestly conditional for the same reason a general theory of success could never be otherwise: it proves the chain's logical architecture is sound and states exactly which further choices — a concrete algorithm, environment, and goal variable — would close each remaining link, rather than asserting one universal closing move exists.

The methodological preface below is stated once and applies to all six links. Each link Xi → Xi+1 is established by three results:

- a **forward theorem**: under stated structural hypotheses, the mutual information between the canonical summary and a goal variable advances toward its maximum;
- a **reverse theorem**: under a stated, explicitly named bridging hypothesis connecting failure of the primitive to information erosion, the information ceiling is strictly below the maximum;
- a **non-reversibility result**: a fully concrete, no-hypotheses-deferred construction showing that satisfying the next primitive's metric without the current one is achievable but informationally hollow.

Every named hypothesis that is not discharged within this paper is flagged in an **Implementation Obligation** at the point it is used, stating exactly what would need to be shown, of a concrete algorithm and environment, to invoke the result. This paper proves the chain's logical architecture is sound; it does not assert that any particular algorithm satisfies every link's obligations in general — that is the constructive question left open for instantiation.

### 8.2 IET 1: X1 → X2

**Theorem 8.1 (forward).** If `alg` robustly possesses X1 and its summary is sufficient for the goal variable, then the mutual information sequence has liminf strictly above 1/2. This link needs no separate bridging step: robust X1 is defined as exactly the conclusion, so the theorem is a restatement, not a derivation.

**Theorem 8.2 (reverse).** If `alg` lacks X1, the mutual information sequence's limsup is bounded strictly below 1/2.

**Theorem 8.3 (non-reversibility).** There is a concrete environment, a constant goal variable, and an algorithm with mutual information identically 0.

> **Intuition — Investing.** This link is the cleanest of the six precisely because robust X1 is the information target, not a precondition for reaching it: a desk that robustly tracks which of two strategies is true is, by definition, carrying more than half a bit of information about the answer. The non-reversibility result is the same caution as elsewhere: a "signal" that's actually a constant tells you nothing, no matter how it's measured.

### 8.3 IET 2: X2 → X3

This link is worked through in full as the template the remaining links follow.

**Definition 8.4 (Robust possession of X2).** Fix a checkpoint sequence τ and a designated dangerous action. An algorithm robustly possesses X2 if the sequence of probabilities it assigns to the dangerous action, evaluated at the checkpoints, is summable.

> **Intuition — Operations.** Summability is a stronger demand than "the danger probability goes to zero." It says the algorithm's flirtation with the catastrophic action is not just shrinking but shrinking fast enough that, by Borel–Cantelli, it touches that action only finitely many times with probability one. A trading desk that merely reduces its exposure to a blow-up trade over time is not the same as a desk that, with certainty in the long run, stops taking that trade altogether.

**Definition 8.5 (Robust possession of X3).** Fix a designated bridge action. An algorithm robustly possesses X3 if, for every threshold M > 0, the probability that its cumulative count of bridge-action plays up to horizon T exceeds M√T tends to one as T → ∞.

**Theorem 8.6 (forward).** Let Gt be a binary goal variable, and suppose the algorithm's canonical summary is a sufficient statistic for Gt at every horizon, and that Gt retains its full log 2 nats of entropy at every horizon. Then the mutual information between the summary and Gt is identically log 2 from the start.

> **Implementation Obligation.** The theorem is stated for algorithms that robustly possess X2 and X3, but the two hypotheses actually doing the logical work are sufficiency of the summary and entropy retention of Gt. Nothing in this paper shows that robust X2 and robust X3 imply those two conditions in a general Class C environment. Exhibiting that implication for a concrete algorithm and environment is left to the implementer.

**Theorem 8.7 (reverse).** Suppose the algorithm does not robustly possess X2, that Gt retains full entropy, and that failing to robustly avoid the dangerous action eventually forces the conditional entropy of Gt given the summary to remain at least δ log 2, for some δ > 0. Then the mutual information's limsup is at most (1−δ) log 2, strictly below the maximum.

> **Implementation Obligation.** The genuinely deferred content is the bridging hypothesis itself — that failing to robustly avoid the dangerous action forces conditional entropy to stay above a fixed fraction of log 2. Constructing a concrete environment and algorithm pair in which this implication holds is left to the implementer.

**Theorem 8.8 (non-reversibility).** There exists a concrete environment, a constant goal variable, and an algorithm satisfying X3's defining metric by construction, yet with mutual information identically 0 — no deferred hypothesis.

> **Intuition — Consulting.** A turnaround consultant who has not yet gotten a client to stop touching the move that keeps causing write-downs (no robust X2) cannot be credited with having found the client's path to a better market segment, even while running pilots in that segment (the X3 behaviour). Until the dangerous move stops, any signal from the pilots is contaminated by the ongoing damage and tells you little about which segment is actually better. Once it stops, the pilots' results really do start to mean something — that is the forward link. And if the client is using a "pilot" that was never designed to teach anyone anything, running it proves nothing about either primitive, no matter how it's dressed up in a report.

### 8.4 IET 3: X3 → X4

**Theorem 8.9 (forward).** If `alg` robustly possesses X3, its summary is sufficient for Gt, and robust X3 entails entropy convergence, then the mutual information converges to log 2.

> **Implementation Obligation.** Note the shift from IET 2's forward link: there, the deferred condition was a pointwise equality; here it is an asymptotic statement. The proof still reduces mutual information to the entropy term exactly via sufficiency, so convergence of one is exactly as strong as convergence of the other — which is what a concrete instantiation must establish.

The reverse link follows the same shape as IET 2's, and the non-reversibility result is again fully concrete — a one-state, zero-reward environment with a constant goal variable.

### 8.5 IET 4: X4 → X5, and IET 5: X5 → X6

These two links are stated at a deliberately higher level of abstraction than the other four. Where IET 1–3 and IET 6 name a concrete possession predicate, IET 4 and IET 5 leave both the possession predicate and, in their non-reversibility results, the witnessing construction fully abstract — logical relays over an arbitrary proposition rather than a named, concrete definition.

> **A larger obligation than elsewhere.** For these two links, instantiating the chain concretely requires strictly more work than for the others: an implementer must supply not only the bridging implication (as everywhere else) but also the concrete definition of what robust possession even means at this link, since none is fixed in the theorem itself. This paper states this as a genuine difference in how much these two links commit to, not a stylistic accident.

> **Intuition — Public Policy.** Some links in a causal chain are well-characterized enough to name precisely — "stops touching the dangerous lever" is a concrete, checkable behavior. Others are real but resist a single canonical formalization across every possible setting — what "robustly respecting a constraint" or "robustly committing to a decision" means can reasonably differ by domain. Rather than force a one-size formal definition onto X4 → X5 and X5 → X6, the chain is kept honest by leaving the shape of the requirement explicit and the content open, to be filled in by whoever is closest to the concrete setting.

### 8.6 IET 6: X6 → X1 — The Accumulative Closure

The sixth link closes the cycle back to X1 and is the only one that makes the "compounds across cycles" promise precise, via an actual Doob martingale construction over a filtration indexed by cycles of length L_min.

**Theorem 8.10 (Accumulation and convergence across cycles).** Under robust X6, for any integrable quantity Θ measurable with respect to the full horizon: (i) if the posterior sequence is a martingale with respect to the cycle filtration, it remains one (the property is preserved, not manufactured); (ii) if in addition Θ is measurable with respect to the filtration's limit, then — given the martingale convergence implication — the posterior converges almost surely to Θ itself.

> **Implementation Obligation.** The filtration and the posterior process are concrete, fully-specified mathematical objects — this is real infrastructure, not a placeholder. What remains deferred is exactly the two facts a real instantiation must supply: that the posterior process actually is a martingale under the cycle filtration, and that martingale convergence applies to it. Given both, the conclusion — almost-sure convergence of the cycle-by-cycle posterior to the truth — is the precise sense in which evidence compounds across cycles rather than resetting.

> **Intuition — Investing.** A fund that resets its analysis from scratch every quarter never accumulates an edge, no matter how good each quarter's analysis is in isolation. A fund whose quarterly posterior genuinely updates on what came before — a real martingale, not a fresh coin flip dressed up as one — has a process that, by Doob's theorem, must eventually settle down to the truth, provided the underlying quantity is integrable and the process really does have the martingale property. That proviso is not a technicality to wave away: it is the entire content of what "building on accumulated evidence" has to mean for the promise to be more than a slogan.

This completes Part III. The six links, together, give a fully machine-checked logical scaffold for a chain from X1 through X6 and back; what is not claimed is that any particular algorithm discharges every link's obligations in a general Class C environment — that construction is environment-specific and is left open, deliberately, for instantiation.

---

## 9. Summary of Results

**What is proved.** Six structural failures (Section 3) each force linear regret on any algorithm lacking the matching primitive, in a minimal environment exhibiting only that one structural failure (Part I, six independent theorems). The six primitives are mutually irreplaceable: for every ordered pair, the algorithm built for one primitive's structural failure is shown to lack a different one when redeployed on that other structural failure's home turf, all thirty pairs following from the same underlying fact — a fixed, non-adaptive policy survives its own structural failure but carries no information about any other (Part II, one master theorem). Six information-theoretic links connect the primitives into a cycle X1 → X2 → ⋯ → X6 → X1; each link is established by a forward result, a reverse result, and a non-reversibility result, and the closing link is grounded in an actual Doob martingale construction (Part III). Every theorem above traces to a specific, named identifier in a machine-checked Lean 4/Mathlib formalization, with every environment's claimed class membership independently verified.

**What is not claimed.**

- Necessity is proved on minimal instances, not sufficiency on general ones. Part I shows that lacking a primitive is fatal in a stripped-down environment exhibiting one structural failure; it does not show that possessing all six primitives is enough to succeed in an arbitrary, more complex member of Class C.
- The literature-comparison claim of Section 4.3 is bounded, not a claim of absolute priority. It asserts only that no formalization known to this paper combines six independently-proven-necessary structural properties into one machine-checked class with proven mutual independence across all of them — not that six properties are exhaustive.
- The sequential-dependence chain is a verified scaffold, not a closed theorem about any concrete algorithm. IET 1, 2, 3, and 6 name a concrete possession predicate; IET 4 and IET 5 leave the possession predicate itself abstract. Every forward and reverse link carries at least one hypothesis — named explicitly in an Implementation Obligation at the point it is used — that this paper does not discharge for any specific environment.
- Two genuinely different notions share the name "conditional entropy" — independently defined and used in different parts of the paper; neither is derived from the other.
- X1's necessity proof uses a total-variation surrogate, not Shannon mutual information, despite the naming convention inherited from Phase 0.
- X2's necessity hypothesis is a deliberate strengthening of F2, not a literal instance of it, because the unconditional version is vacuous in an absorbing-trap environment.
- The fourteen unused Phase 1 tools are positioned, not proven to work. The relevant remark in Section 5 identifies which Part III obligation each is plausibly suited to discharging; none of them has actually been used to discharge it. Confirming that fit is exactly the constructive work this paper leaves open, not a claim made here.

---

## 10. Conclusion

The six primitives were chosen to be stated abstractly enough to survive outside the reinforcement-learning setting that motivated them — a hidden objective worth identifying, a mistake worth never repeating, a plateau worth pushing past, a decision worth eventually making, a constraint worth never trading away, and evidence worth retiring once it goes stale recur in fund management, operations, consulting, and public policy under different names but the same shape. The minimality principle (Section 3.3) is what makes that portability more than a rhetorical flourish: each necessity result is proved against the least elaborate environment that still forces the failure, so the floor it establishes persists into every harder environment containing that instance as a special case.

What this paper deliberately leaves open is the constructive question: exhibiting a concrete algorithm, in a concrete richer member of Class C, that discharges every Implementation Obligation in Part III simultaneously. That construction is environment-specific by nature, and collapsing it into a single abstract theorem would either trivialize it or smuggle in unstated assumptions about the environment — exactly the failure mode this paper's machine-checked discipline was adopted to avoid. The verified scaffold is offered as the foundation that construction would stand on, not as a substitute for it.

---

## References

George A. Akerlof. The market for 'lemons': Quality uncertainty and the market mechanism. *The Quarterly Journal of Economics*, 84(3):488–500, 1970.

Kenneth J. Arrow and Gerard Debreu. Existence of an equilibrium for a competitive economy. *Econometrica*, 22(3):265–290, 1954.

Ashwinkumar Badanidiyuru, Robert Kleinberg, and Aleksandrs Slivkins. Bandits with knapsacks. *Journal of the ACM*, 65(3):1–55, 2018.

Austin Coursey, Abel Diaz-Gonzalez, Marcos Quinones-Grueiro, and Gautam Biswas. Safe continual reinforcement learning in non-stationary environments. *arXiv preprint arXiv:2604.19737*, 2026.

Leonardo de Moura and Sebastian Ullrich. The Lean 4 theorem prover and programming language. In *Automated Deduction – CADE 28*, pages 625–635. Springer International Publishing, 2021.

Aurélien Garivier and Eric Moulines. On upper-confidence bound policies for switching bandit problems. In *Proceedings of the 22nd International Conference on Algorithmic Learning Theory (ALT 2011)*, pages 174–188. Springer, 2011.

Leslie Pack Kaelbling, Michael L. Littman, and Anthony R. Cassandra. Planning and acting in partially observable stochastic domains. *Artificial Intelligence*, 101(1–2):99–134, 1998.

Tor Lattimore and Csaba Szepesvári. *Bandit Algorithms*. Cambridge University Press, 2020.

Ian Osband, Charles Blundell, Alexander Pritzel, and Benjamin Van Roy. Deep exploration via bootstrapped DQN. In *Advances in Neural Information Processing Systems 29*, pages 4026–4034, 2016.

Ian Osband, Yotam Doron, Matteo Hessel, John Aslanides, Eren Sezener, Andre Saraiva, Katrina McKinney, Tor Lattimore, Csaba Szepesvári, Satinder Singh, Benjamin Van Roy, Richard Sutton, David Silver, and Hado van Hasselt. Behaviour suite for reinforcement learning. In *International Conference on Learning Representations*, 2020.

The mathlib Community. The Lean mathematical library. In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, CPP 2020, pages 367–381. ACM, 2020.

Benjamin Plaut, Hanlin Zhu, and Stuart Russell. Avoiding catastrophe in online learning by asking for help. In *Proceedings of the International Conference on Machine Learning (ICML 2025)*, 2025.

Daniel Russo and Benjamin Van Roy. An information-theoretic analysis of Thompson sampling. *Journal of Machine Learning Research*, 17(1):2442–2471, 2016.

Alexander L. Strehl and Michael L. Littman. An analysis of model-based interval estimation for Markov decision processes. *Journal of Computer and System Sciences*, 74(8):1309–1331, 2008.

Timofey Tomashevskiy. Safe continual reinforcement learning methods for nonstationary environments: Towards a survey of the state of the art. *arXiv preprint arXiv:2601.05152*, 2026.

John von Neumann and Oskar Morgenstern. *Theory of Games and Economic Behavior*. Princeton University Press, 1944.

---

## Appendices

Two appendices are omitted from this Markdown edition:

- **Appendix A** — a complete, line-by-line table mapping every numbered Definition, Theorem, Lemma, and Example in the paper to its exact Lean identifier and file/line location.
- **Appendix B** — the Lean proofs verifying that every environment used in Part I actually exhibits the structural property (P1–P6) it is claimed to witness.

Both are in the [full PDF, archived on Zenodo (DOI 10.5281/zenodo.21177368)](https://doi.org/10.5281/zenodo.21177368). The underlying, authoritative Lean source for both appendices is directly browsable in this repository: `SixPrimitives/Phase0.lean` through `SixPrimitives/Phase5.lean`.

## Citation

```
Ismail, M. (2026). Ismail's Primitives: A Unified Functional Theory of
Necessity, Independence, and Sequential Dependence in Adaptive Decision
Systems. Zenodo, V6.1. https://doi.org/10.5281/zenodo.21177368
```
