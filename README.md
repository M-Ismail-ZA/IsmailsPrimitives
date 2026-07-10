# Ismail's Primitives
*A Unified Functional Theory of Necessity, Independence, and Sequential Dependence in Adaptive Decision Systems*

[![build](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml/badge.svg)](https://github.com/M-Ismail-ZA/IsmailsPrimitives/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21177368.svg)](https://doi.org/10.5281/zenodo.21177368)
![code license](https://img.shields.io/badge/code--license-MIT-blue)
![paper license](https://img.shields.io/badge/paper--license-CC--BY--4.0-lightgrey)

**[Website](https://m-ismail-za.github.io/IsmailsPrimitives/) · [Glossary](https://m-ismail-za.github.io/IsmailsGlossary/) · [Paper (DOI)](https://doi.org/10.5281/zenodo.21177368)**

A complete Lean 4 / Mathlib formalization of **Ismail's Primitives**: a
functional theory of necessity, independence, and sequential dependence for
adaptive decision-making under uncertainty. This repository is the formal,
machine-checked companion to the paper of the same name — published on
Zenodo, DOI: [10.5281/zenodo.21177368](https://doi.org/10.5281/zenodo.21177368).
For the broader motivation, the POMDP framing, and worked examples across
investing, insurance, and consulting, see the
[companion website](https://m-ismail-za.github.io/IsmailsPrimitives/) — this
README stays close to the formalization itself.

The theory identifies six structural primitives that any decision-maker —
a person, an institution, or a machine — must possess to achieve sublinear
regret in a general class of partially observable environments under
uncertainty (the paper calls this environment class **Class C**), and
proves — entirely inside Lean's type theory, checked by the kernel, with
zero `sorry`, zero custom `axiom`, and zero `opaque` definitions — that
each primitive is:

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

## Contents

- [The Six Primitives](#the-six-primitives)
- [Status](#status)
- [Structure](#structure)
- [Building it yourself](#building-it-yourself)
- [Using this as a dependency](#using-this-as-a-dependency)
- [Papers](#papers)
- [Related project: Ismail's Glossary](#related-project-ismails-glossary)
- [License](#license)
- [Author](#author)

## The Six Primitives

`SixPrimitives/Phase0.lean` defines six primitive predicates over decision
rules, referred to throughout the proof and the paper as X1–X6:

| | Primitive | What it requires |
| --- | --- | --- |
| **X1** | Objective Tracking | Maintain separate, updating beliefs about which of several live hypotheses is true, rather than collapsing to one prematurely. |
| **X2** | Cross-Context Safety Transfer | Identify actions that lead to an unrecoverable state and exclude them from the policy. |
| **X3** | Global Attractor Exploration | Keep exploring past a locally comfortable but globally suboptimal plateau. |
| **X4** | Policy Simplification | Convert settled evidence into a fixed, committed decision rather than continuing to hedge. |
| **X5** | Feasibility Projection | Enforce a hard constraint as non-negotiable rather than trading it off against reward. |
| **X6** | Feedback Adaptation | Revise a belief or policy once the environment generating the evidence has shifted. |

Each primitive has a matching structural failure mode (P1–P6 in the paper:
reward ambiguity, absorbing traps, local optima, deterministic optimality,
constrained feasibility, and nonstationarity) — the environments built in
`Phase3.lean` are the minimal instance of each.

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

| File | Lines | Contents |
| --- | ---: | --- |
| `SixPrimitives.lean` | — | Root import |
| `SixPrimitives/Phase0.lean` | 259 | Framework types: `Env`, `Algorithm`, the six primitive predicates |
| `SixPrimitives/Phase1.lean` | 1,603 | Supporting lemmas (probability, analysis) |
| `SixPrimitives/Phase2.lean` | 4,842 | Trajectory measure & environments |
| `SixPrimitives/Phase2CMI.lean` | 1,029 | Conditional mutual information |
| `SixPrimitives/Phase3.lean` | 2,600 | **Part I** — necessity of each primitive |
| `SixPrimitives/Phase4.lean` | 1,534 | **Part II** — mutual independence, all thirty pairs |
| `SixPrimitives/Phase5.lean` | 800 | **Part III** — sequential dependence & martingale convergence |

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

## Papers

This formalization is standalone: it does not depend on any paper, and
every result here is fully self-contained and machine-checked. The main
paper draws every one of its formal claims from this repository and
cross-references each theorem, definition, and environment to its exact
Lean identifier and line range (see the correspondence tables in the
paper's appendix) — so any claim in the paper can be checked against the
source it names, not taken on faith.

### Main paper

**Ismail's Primitives: A Unified Functional Theory of Necessity,
Independence, and Sequential Dependence in Adaptive Decision Systems**
Muhammed Ismail, Zenodo, V6.1 (2026).
DOI: [10.5281/zenodo.21177368](https://doi.org/10.5281/zenodo.21177368) · CC BY 4.0

```bibtex
@article{ismail2026primitives,
  author    = {Ismail, Muhammed},
  title     = {Ismail's Primitives: A Unified Functional Theory of Necessity,
               Independence, and Sequential Dependence in Adaptive Decision
               Systems},
  year      = {2026},
  publisher = {Zenodo},
  version   = {V6.1},
  doi       = {10.5281/zenodo.21177368},
  url       = {https://doi.org/10.5281/zenodo.21177368}
}
```

📄 Also in this repository: [full PDF](paper/Ismails_Primitives.pdf) · [Markdown edition](paper/PAPER.md)

### Extending Ismail's Primitives

The necessity results are stated abstractly enough to travel beyond
business decision-making. Companion papers apply the same six primitives,
under a fixed relabelling, to other domains — each cites the exact Lean
declaration and line range it draws on, the same way the main paper does:

- **Ismail's Primitives and Human Development: A Functional Isomorphism
  Between a Lean-Verified Computational Theory and Developmental
  Psychology.** Argues that Erikson's psychosocial stages, Maslow's
  motivational hierarchy, and Bowlby's attachment phases independently
  converge on the same six-stage sequence proven necessary here.
  DOI: [10.5281/zenodo.21257553](https://doi.org/10.5281/zenodo.21257553) (V3.0)

- **Ismail's Primitives: An Emotional Adaptation Theory for Therapy
  Discovered through Functional Isomorphism.** Derives six therapeutic
  functions from the same primitives, giving the "Dodo Bird verdict" — the
  finding that no single therapy modality reliably outperforms the others —
  a structural explanation.
  DOI: [10.5281/zenodo.21289914](https://doi.org/10.5281/zenodo.21289914) (V2.0)

- **Ismail's Primitives: Lean-verified Economic Adaptation Theory.**
  Re-derives the same necessity and independence theorems under a
  relabelling to economy / coordination mechanism / welfare, recovering
  Walrasian equilibrium as the special case that falls outside Class C.
  DOI: [10.5281/zenodo.21289756](https://doi.org/10.5281/zenodo.21289756) (V2.0)

Further papers extending the theory are in preparation. All papers above
are CC BY 4.0; the Lean formalization in this repository is MIT.

## Related project: Ismail's Glossary

Formalizing this proof meant learning Mathlib well enough to navigate its
9,150 modules — and that work produced a second, independent project as a
byproduct: **Ismail's Glossary**, a complete navigation index for Mathlib4.
It gives every module a short, human-readable description, an interactive
atlas of how Mathlib's 32 top-level domains relate, and a progressive
reference for learning Lean itself.

- Website: [m-ismail-za.github.io/IsmailsGlossary](https://m-ismail-za.github.io/IsmailsGlossary/)
- Repository: [github.com/M-Ismail-ZA/IsmailsGlossary](https://github.com/M-Ismail-ZA/IsmailsGlossary)
- Paper: *Ismail's Glossary: A Complete Navigation Index for Mathlib4*,
  Zenodo, V1.0 (2026).
  DOI: [10.5281/zenodo.21192789](https://doi.org/10.5281/zenodo.21192789)

## License

- **Lean formalization** (this repository): released under the
  [MIT License](https://github.com/M-Ismail-ZA/IsmailsPrimitives/blob/main/LICENSE).
- **Papers**: released under CC BY 4.0 — free to use, cite, and build on;
  attribution is the only requirement.

## Author

Muhammed Ismail is an independent researcher based in South Africa,
self-taught in mathematics. The six primitives were first noticed as a
recurring pattern in his own decision-making in September 2025, and
developed into a complete theory over the months that followed.

As an unaffiliated researcher, a result that needs specialists in formal
logic and decision theory to evaluate the mathematics — and separate
specialists again for each domain it's shown to reach — has no realistic
route through traditional peer review on any useful timeline. So the proof
was built in Lean 4 instead: a claim a kernel checks deterministically,
without first needing to check the author. Learning Mathlib well enough to
do that produced this repository's ~12,700 lines, and, as a byproduct of
the learning itself, [Ismail's Glossary](#related-project-ismails-glossary).

Email: <literacity@outlook.com> · ORCID: [0009-0000-3713-7105](https://orcid.org/0009-0000-3713-7105) · [LinkedIn](https://www.linkedin.com/in/researcher-adaptationtheory/)
