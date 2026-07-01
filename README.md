# Ismail's Primitives

### A Unified Functional Theory of Necessity, Independence, and Sequential Dependence in Adaptive Decision Systems

[![build](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml/badge.svg)](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21110934-blue)](https://doi.org/10.5281/zenodo.21110934)

A complete Lean 4 / Mathlib formalization of **Ismail's Primitives**: a
functional theory of what any sequential decision-maker — a person, an
institution, or a machine — must get right before sustained success under
real uncertainty is even possible. This repository contains the formal,
machine-checked companion to [the paper of the same name](https://doi.org/10.5281/zenodo.21110934).

The theory identifies six structural failures that recur across investing,
operations, public policy, and machine learning, and characterizes six
matching primitives — proving, entirely inside Lean's type theory and
checked by the kernel:

| | Primitive | In one line |
|---|---|---|
| **X1** | Objective Tracking | Tell apart two hypotheses that prescribe different actions |
| **X2** | Cross-Context Safety Transfer | Stop touching the action that locks in permanent loss |
| **X3** | Global Attractor Exploration | Keep probing past a comfortable plateau toward a better region |
| **X4** | Policy Simplification | Commit decisively once the evidence supports one option |
| **X5** | Feasibility Projection | Respect a hard constraint rather than trade it off |
| **X6** | Feedback Adaptation | Discard stale evidence once the world has changed |

For each, the repository proves:

- **necessity** — its absence forces linear regret in a minimal environment
  exhibiting the matching structural failure (Part I, six independent
  theorems);
- **mutual independence** — for every one of the thirty ordered pairs, the
  algorithm built for one primitive is shown to lack a different one when
  redeployed on that primitive's home turf (Part II, one master theorem);
  and
- **a verified sequential-dependence scaffold** — six information-theoretic
  links (forward, reverse, and non-reversibility results per link) connect
  the primitives into a cycle X1 → X2 → ⋯ → X6 → X1, closing on an actual
  Doob martingale construction (Part III). This is a logical scaffold, not
  a closed sufficiency proof: several links carry explicit, named
  "Implementation Obligations" — stated hypotheses this paper does not
  discharge for any concrete algorithm, left open by design for a specific
  instantiation to supply. See Section 8 and the Summary of Results in the
  paper for exactly which obligations remain.

## Status

| | |
|---|---|
| Lines of Lean | ~12,700 |
| `sorry` | 0 |
| `axiom` | 0 |
| `opaque` | 0 |
| Linter suppressions | 0 |
| Lean toolchain | `leanprover/lean4:v4.30.0` |
| Mathlib | `v4.30.0` (pinned; see `lakefile.lean`) |

Every definition and theorem in this repository is proved from Mathlib's
axioms alone — no `sorry`, no custom `axiom`, no `opaque` escape hatches, and
no disabled linters. The build log in the Actions tab above is the evidence:
if it's green, the whole library compiles and every proof checks.

## Structure

The library is organized into phases, each building on the last:

```
SixPrimitives.lean        -- root import
SixPrimitives/
  Phase0.lean              -- framework types: Env, Algorithm, primitive predicates
  Phase1.lean               -- standard supporting lemmas (probability, analysis)
  Phase2.lean                -- trajectory measure & environments
  Phase2CMI.lean              -- conditional mutual information
  Phase3.lean                  -- necessity of each primitive
  Phase4.lean                   -- mutual independence of the six primitives
  Phase5.lean                    -- sequential dependence & martingale convergence
```

Dependency order: `Phase0 → Phase1 → Phase2 → Phase2CMI → Phase3 → Phase4 → Phase5`.
Each file only imports the phases before it, so you can read them in that
order and every definition you meet has already been introduced.

## Building it yourself

You don't need to trust the badge — you can verify the whole thing on your
own machine in a few minutes.

**1. Install Lean** (via `elan`, the Lean version manager), if you don't have
it already: see <https://leanprover-community.github.io/get_started.html>.

**2. Clone the repository:**

```bash
git clone https://github.com/M-Ismail-ZA/IsmailsPrimitives.git
cd IsmailsPrimitives
```

**3. Fetch the Mathlib dependency and its precompiled build cache** (this is
what makes the build take minutes instead of hours — it downloads prebuilt
Mathlib binaries instead of compiling Mathlib from source):

```bash
lake update
lake exe cache get
```

**4. Build:**

```bash
lake build
```

If it finishes without error, you have independently confirmed that every
theorem in this repository checks under Lean's kernel.

You can also open the folder in VS Code with the `lean4` extension installed
and browse/step through any file interactively.

## Using this as a dependency

If you want to build on top of Ismail's Primitives in your own Lean project,
add this to your `lakefile.lean`:

```lean
require SixPrimitives from git
  "https://github.com/M-Ismail-ZA/IsmailsPrimitives.git"
```

and `import SixPrimitives` (or a specific phase, e.g. `import SixPrimitives.Phase0`).

## Relation to the paper

This formalization is standalone: it does not depend on the paper, and every
result here is fully self-contained and machine-checked. The paper cites
this repository as the source of truth for its formal claims, and every
numbered definition and theorem in the paper is mapped to its exact Lean
identifier and line range in the paper's Appendix A.

📄 **Read the paper**: [DOI 10.5281/zenodo.21110934](https://doi.org/10.5281/zenodo.21110934)

## Citation

If you build on or extend this work, please cite:

```
Ismail, M. (2026). Ismail's Primitives: A Unified Functional Theory of
Necessity, Independence, and Sequential Dependence in Adaptive Decision
Systems. Zenodo. https://doi.org/10.5281/zenodo.21110934
```

## License

Released under the [MIT License](LICENSE).

## Author

Muhammed Ismail, Independent Researcher
Email: literacity@outlook.com
ORCID: [0009-0000-3713-7105](https://orcid.org/0009-0000-3713-7105)