# Ismail's Primitives

[![build](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml/badge.svg)](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21177368.svg)](https://doi.org/10.5281/zenodo.21177368)

A complete Lean 4 / Mathlib formalization of **Ismail's Primitives**: a
functional theory of necessity, independence, and sequential dependence for
adaptive decision-making under uncertainty. This repository is the formal,
machine-checked companion to the paper of the same name — published on
Zenodo, DOI: [10.5281/zenodo.21177368](https://doi.org/10.5281/zenodo.21177368).

The theory identifies six structural primitives that any decision-maker —
a person, an institution, or a machine — must possess to achieve sublinear
regret in a general class of partially observable environments under
uncertainty, and proves — entirely inside Lean's type
theory, checked by the kernel, with zero `sorry`, zero custom `axiom`, and
zero `opaque` definitions — that each primitive is:

- **Necessary**: its absence forces linear (Ω(T)) regret in an explicit,
  minimal environment built to exhibit that one structural failure (Part I,
  six independent theorems);
- **Mutually Independent**: no primitive is derivable from, or substitutable
  by, any other — verified across all thirty ordered pairs on a single
  compound environment (Part II, one master theorem covering every pair);
- **Sequentially Dependent**: the six primitives compose into a directed
  information chain X₁→X₂→⋯→X₆→X₁. Necessity is domain-invariant, so Parts I
  and II hold unconditionally; sufficiency is not — what "success" means is
  supplied by the domain, not by the theorem — so Part III proves exactly
  what generalizes: each link is established outright by a forward theorem,
  a reverse theorem, and a non-reversibility result, with the exact point
  where a domain's own goal enters the chain named explicitly rather than
  assumed away. The closing link is grounded in an explicit Doob martingale
  construction over cycles of play (Part III).

Every claim above traces to a specific, named identifier in this repository
— nothing is asserted without a corresponding, checkable Lean proof.

## Status

|                     |                                |
| ------------------- | ------------------------------ |
| Lines of Lean       | ~12,700                        |
| `sorry`             | 0                              |
| `axiom`             | 0                              |
| `opaque`            | 0                              |
| Linter suppressions | 0                              |
| Lean toolchain      | `leanprover/lean4:v4.30.0` |
| Mathlib             | verified against `v4.30.0`     |

Every definition and theorem in this repository is proved from Mathlib's
axioms alone — no `sorry`, no custom `axiom`, no `opaque` escape hatches, and
no disabled linters. The build log in the Actions tab above is the evidence:
if it's green, the whole library compiles and every proof checks. You don't
have to take the table's word for it — the "Building it yourself" section
below reproduces the same check on your own machine.

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

```
git clone https://github.com/M-Ismail-ZA/IsmailsPrimitives.git
cd IsmailsPrimitives
```

**3. Fetch the Mathlib dependency and its precompiled build cache** (this is
what makes the build take minutes instead of hours — it downloads prebuilt
Mathlib binaries instead of compiling Mathlib from source):

```
lake update
lake exe cache get
```

**4. Build:**

```
lake build
```

If it finishes without error, you have independently confirmed that every
theorem in this repository checks under Lean's kernel.

You can also open the folder in VS Code with the `lean4` extension installed
and browse/step through any file interactively.

## Using this as a dependency

If you want to build on top of Ismail's Primitives in your own Lean project,
add this to your `lakefile.lean`:

```
require SixPrimitives from git
  "https://github.com/M-Ismail-ZA/IsmailsPrimitives.git"
```

and `import SixPrimitives` (or a specific phase, e.g. `import SixPrimitives.Phase0`).

## Relation to the paper

This formalization is standalone: it does not depend on the paper, and every
result here is fully self-contained and machine-checked. The paper draws
every one of its formal claims from this repository and cross-references
each theorem, definition, and environment to its exact Lean identifier and
line range (see the correspondence tables in the paper's appendix) — so any
claim in the paper can be checked against the source it names, not taken on
faith.

**Paper:** *Ismail's Primitives: A Unified Functional Theory of Necessity,
Independence, and Sequential Dependence in Adaptive Decision Systems*,
Muhammed Ismail, Zenodo, V6.1 (2026).
DOI: [10.5281/zenodo.21177368](https://doi.org/10.5281/zenodo.21177368)

## License

Released under the [MIT License](https://github.com/M-Ismail-ZA/IsmailsPrimitives/blob/main/LICENSE).

## Author

Muhammed Ismail, Independent Researcher
Email: <literacity@outlook.com> · ORCID: [0009-0000-3713-7105](https://orcid.org/0009-0000-3713-7105)
