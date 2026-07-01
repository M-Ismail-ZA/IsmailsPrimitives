# Ismail's Primitives

[![build](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml/badge.svg)](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml)

A complete Lean 4 / Mathlib formalization of **Ismail's Primitives**: a
functional theory of necessity, independence, and sequential dependence for
adaptive decision-making under uncertainty. This repository contains the
formal, machine-checked companion to the paper of the same name.

The theory identifies six structural primitives that a decision-making
algorithm must possess to achieve sublinear regret in a general class of
partially observable environments, and proves — entirely inside Lean's type
theory, checked by the kernel — that each primitive is:

- **necessary** (its absence forces linear regret in some environment),
- **mutually independent** (no primitive is derivable from the others), and
- **sequentially dependent** (the primitives form an ordered informational
  chain, culminating in a martingale convergence result for the learning
  posterior).

## Status

| | |
|---|---|
| Lines of Lean | ~12,700 |
| `sorry` | 0 |
| `axiom` | 0 |
| `opaque` | 0 |
| Linter suppressions | 0 |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | verified against `v4.30.0` |

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
result here is fully self-contained and machine-checked. The paper, in turn,
cites this repository as the source of truth for its formal claims. The paper
is still in preparation and is not yet public; this repository is released
first so the formal results can be inspected and verified independently.

## License

Released under the [MIT License](LICENSE).

## Author

Muhammed Ismail, Independent Researcher
Email: literacity@outlook.com
ORCID: [0009-0000-3713-7105](https://orcid.org/0009-0000-3713-7105)
