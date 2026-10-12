# Nikoghosyan's conjecture

[![Lean](https://github.com/canghaimeng/Nikoghosyan-conjecture/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/canghaimeng/Nikoghosyan-conjecture/actions/workflows/lean.yml)

A Lean 4 formalization of Nikoghosyan's conjecture on Hamiltonicity of
1-tough graphs with no induced $P_4 \cup P_1$, using mathlib.

## The theorem

Every finite simple graph on at least three vertices that is 1-tough and
contains no induced subgraph isomorphic to $P_4 \cup P_1$ has a Hamiltonian
cycle.

Here $P_4$ is a path on four vertices and $P_1$ is an isolated vertex. A
graph is 1-tough if, for every vertex set $S$ whose deletion leaves at
least two connected components, the number of those components is at
most $|S|$.

The main declarations are in [`Nikoghosyan/Main.lean`](Nikoghosyan/Main.lean):

- `Nikoghosyan.exists_spanning_graphCycle_of_oneTough_noInducedP4UnionP1`
  produces a cycle in the original graph containing every vertex.
- `Nikoghosyan.isHamiltonian_of_oneTough_noInducedP4UnionP1`
  states the result using mathlib's `SimpleGraph.IsHamiltonian`.

For example, the Hamiltonicity theorem can be used as follows:

```lean
import Nikoghosyan.Main

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

example
    (hord : 3 ≤ Fintype.card V)
    (hT : Nikoghosyan.OneTough G)
    (hpat : Nikoghosyan.NoInducedP4UnionP1 G) :
    G.IsHamiltonian :=
  Nikoghosyan.isHamiltonian_of_oneTough_noInducedP4UnionP1 hord hT hpat
```

The hypotheses are exactly the order bound, 1-toughness, and the forbidden
induced subgraph condition. Adjacency decidability is supplied classically
inside the proof. The cycle witness uses edges of the original graph.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/canghaimeng/Nikoghosyan-conjecture.git
cd Nikoghosyan-conjecture
lake exe cache get
lake build Nikoghosyan NikoghosyanPrerequisites
```

The project uses **Lean 4.34.1**, as specified in `lean-toolchain`.
Mathlib is pinned to `v4.34.1`, commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`; `lake-manifest.json` also pins its
transitive dependencies. Elan selects the project's Lean toolchain
automatically.

`lake build` builds the main library. The explicit command above also
builds the complete prerequisite library. GitHub Actions runs both
library targets on pushes and pull requests; the badge shows the actual
workflow result for `main`.

## Source guide

| File or directory | Contents |
| --- | --- |
| [`Nikoghosyan/Basic.lean`](Nikoghosyan/Basic.lean) | Graph predicates, 1-toughness, and forbidden induced subgraphs |
| [`Nikoghosyan/Paths.lean`](Nikoghosyan/Paths.lean), [`Nikoghosyan/Factor.lean`](Nikoghosyan/Factor.lean) | Paths, cycles, and cycle factors |
| [`Nikoghosyan/Cograph/`](Nikoghosyan/Cograph/) | Cograph structure and path constructions |
| [`Nikoghosyan/Prerequisites/`](Nikoghosyan/Prerequisites/) | Prerequisite graph theorems and factor existence |
| [`Nikoghosyan/Absorption/`](Nikoghosyan/Absorption/) | Cycle absorption and merging arguments |
| [`Nikoghosyan/RemainingCase.lean`](Nikoghosyan/RemainingCase.lean) | Final minimum-factor argument |
| [`Nikoghosyan/Main.lean`](Nikoghosyan/Main.lean) | Main theorem and Hamiltonicity corollary |
| [`Nikoghosyan.lean`](Nikoghosyan.lean) | Library entry point |

The repository contains 119 modules under `Nikoghosyan/`, plus the library
entry point. Proofs contain no `sorry` or custom axioms. The two main
theorems depend only on Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. After building, their dependencies
can be inspected in Lean with:

```lean
import Nikoghosyan.Main

#print axioms Nikoghosyan.exists_spanning_graphCycle_of_oneTough_noInducedP4UnionP1
#print axioms Nikoghosyan.isHamiltonian_of_oneTough_noInducedP4UnionP1
```

Copyright and license notices are retained in the source files. The
Apache 2.0 license text referenced by applicable source headers is
provided in [`LICENSE`](LICENSE).

## Euler research workflow

This proof and its Lean formalization are part of the [Euler](https://github.com/canghaimeng/Euler) mathematical research project. Their development used agent-assisted proof exploration, review, and formalization workflows. Euler supports the organization and inspection of mathematical statements, proof dependencies, research records, and verification evidence.

The [Euler case study](https://github.com/canghaimeng/Euler/tree/main/examples/nikoghosyan) describes the result, its significance, and the development history across these workflows.

To cite the Euler software:

```bibtex
@software{chen2026euler,
  author = {Chen, Qiuyu},
  title  = {Euler: Human-Centered Mathematical Research with Frontier-Driven Agents},
  year   = {2026},
  url    = {https://github.com/canghaimeng/Euler}
}
```
