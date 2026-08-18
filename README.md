# NUSLean

Lean 4 + Mathlib formalization of *A near-quadratic lower bound for sets with no
unique sums*.  The corresponding working paper is committed as
[`NUS_edited.tex`](NUS_edited.tex).

The headline result is

> **Theorem 1.2.** `m(p) ≫ (log p / log log p)²`,

where `m(p)` is the least size of a set `A ⊆ 𝔽_p`, `|A| ≥ 2`, in which every element of
`A + A` has at least two unordered representations (Problem 27 in Green's list).

The formalization proves the lower bound.  It does not re-formalize Bedert's
external `O((log p)²)` upper bound, so the paper's full asymptotic corollary uses
that cited result in addition to the Lean theorem.

## Exact informal-to-formal correspondence

The declaration submitted to Comparator is `NUS.m_lower_bound`.  Its complete
mathematical reading is:

> There exist an absolute real constant `c > 0` and a natural-number threshold
> `p₀` such that, for every natural number `p`, if `p` is prime and `p ≥ p₀`, then
> `m(p) ≥ c (log p / log log p)²`.

The notation in that sentence corresponds to Lean as follows:

| Informal mathematics | Lean representation |
|---|---|
| prime field `𝔽_p` | `ZMod p`, under the hypothesis `Fact p.Prime` |
| unordered pair from `A` | a `Multiset` of cardinality two whose entries lie in `A` |
| repeated representation `{a,a}` | allowed, because a multiset rather than a two-element set is used |
| no unique sum | every pair multiset has a distinct pair multiset with the same sum |
| `m(p)` | `Nat.sInf` of the attainable cardinalities at least two; `m_spec` proves attainment for odd primes |
| `log` | `Real.log`, the natural logarithm |
| sufficiently large | an existential threshold `∃ p₀`; the proof can take `p₀ = 64` |
| absolute implied constant | an existential real `∃ c, 0 < c`, independent of `p` |

There is no known weakening or extra mathematical hypothesis in the formal
lower-bound statement.  The only scope boundary is that the cited upper bound
`m(p) = O((log p)²)` is not proved in Lean here.  Consequently this repository
proves Theorem 1.2 and the lower-bound half of the asymptotic corollary, while
the full equality `m(p) = (log p)^{2+o(1)}` additionally relies on Bedert's
external result.

## Authors, process, and licence

The formalization and working paper are maintained by Xinjie.  The work combined
human mathematical direction with AI-assisted proof engineering using OpenAI
Codex; [`formalization.yaml`](formalization.yaml) records the process, provenance,
scope, fidelity notes, and review status in detail.  No independent human peer
review of the complete Lean development is claimed.

The repository is distributed under the [Apache License 2.0](LICENSE).  The
licence applies to this repository snapshot; cited papers and dependencies retain
their own licences.

## Build

```sh
git clone https://github.com/xinjiegit/ben_27_formalization.git
cd ben_27_formalization
lake exe cache get
lake build
lake build Challenge Solution
```

The project pins Lean `v4.32.0`, Mathlib, and its complete dependency closure in
`lean-toolchain` and `lake-manifest.json`.

## Palomar verification surface

This repository uses Palomar's ordinary root layout:

| File | Role |
|---|---|
| `Challenge.lean` | short, Mathlib-only statement surface for mathematical audit |
| `Solution.lean` | exposes the completed proof from `NUSLean.Main` |
| `comparator.json` | records `NUS.m_lower_bound` and the permitted axioms |
| `formalization.yaml` | structured provenance, scope, automation, and review metadata |

`Challenge.lean` intentionally contains one `sorry`.  This is the statement hole
that Comparator fills with the declaration exposed by `Solution.lean`; it is not a
hole in the proof development.  The Palomar submission form is at
<https://submit.palomar-registry.org/>.

## File map

| File | Paper | Contents |
|---|---|---|
| `NUSLean/Defs.lean` | §1, Def. 1.1 | `IsPairFrom`, `HasNoUniqueSum`, `m p`, minimal-subset extraction, `𝔽_p` example |
| `NUSLean/Derangement.lean` | §1 (choice of `μ`) | fiber-preserving fixed-point-free permutations exist |
| `NUSLean/CollisionLattice.lean` | §1, Lemma 1.3 | `MinimalNUS`, `Pairing`, `uvec`, `rho`, `colLat`; full proof of Lemma 1.3 |
| `NUSLean/CleanRectangle.lean` | §2, Lemma 2.1 | proved clean-rectangle bound `p ≤ 2^(|X|+|Y|−2)` |
| `NUSLean/CommonCut.lean` | §3, Lemma 3.1 | configurations, Efron–Stein inequality, and proved common-cut lemma |
| `NUSLean/Contraction.lean` | §3, Lemma 3.2 | bounded-radius forest contraction (proved) |
| `NUSLean/Compression.lean` | §4, Prop. 4.1 | proved compression to `O(√n + n/log p)` core coordinates |
| `NUSLean/FinalDeterminant.lean` | §5 | proved determinant bridge and its linear-algebra helpers |
| `NUSLean/Main.lean` | §5, Thm 1.2 | arithmetic endgame, strengthened setwise bound, and **Theorem 1.2** for `m(p)` (all proved from the bridge) |

## Proof status

**The proof development is fully proved.**  Excluding the deliberate statement
hole in `Challenge.lean`, it is sorry-free.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound` for both headline declarations.

* Definition layer: `hasNoUniqueSum_empty`, `hasNoUniqueSum_univ`
  (`𝔽_p` itself has no unique sum for odd `p`, so `m p` is attained: `m_spec`),
  `exists_minimal` (extraction of an inclusion-minimal subexample).
* `exists_derangement`, `exists_fiberwise_derangement`, and
  `MinimalNUS.exists_pairing` — existence of the fixed-point-free fiber-preserving `μ`.
* **Lemma 1.3 in full**:
  * `MinimalNUS.eq_const_of_rho_dot_eq_zero` — the heart: a rational vector orthogonal
    to all collision rows is constant, via the argmax-set argument and
    inclusion-minimality;
  * `MinimalNUS.finrank_span_rhoQ` — the collision lattice has rational rank `n − 1`;
  * `MinimalNUS.finrank_span_modp_le` — mod-`p` row rank at most `n − 2`
    (`𝟙` and the label vector `a` are two independent orthogonal vectors);
  * `MinimalNUS.p_dvd_maximal_minor` — `p` divides every maximal minor of every
    `(n−1)`-row matrix with rows in the lattice.
* **Lemma 2.1** (`MinimalNUS.clean_rectangle`) — minimal invariant sub-rectangle,
  rational kernel/rank calculation, modular determinant divisibility, and the
  totally-unimodular Laplace bound.
* **Lemma 3.1** (`common_cut`) — finite Bernoulli expectations, a proved
  switch-off Efron–Stein inequality, the coverage estimate, and simultaneous hitting.
* **Lemma 3.2** (`bounded_radius_contraction`) — the forest contraction, via a
  maximum matching, a rank-decreasing parent map (acyclicity from the
  max-rank-vertex-on-a-cycle argument), double-star diameter bounds, and a
  surjection onto the root-avoiding components for the counting conclusion.
* **Proposition 4.1** (`compression`) — the full round iteration, primitive forest
  pivots, live-block mass accounting, coefficient growth, and terminal core bound.
* **Section 5 determinant bridge** (`key_inequality_proof`) — selection of `K−1`
  independent quotient collision rows, a nonzero minor divisible by `p`, its
  `ℓ¹` determinant bound, and the resulting logarithmic inequality.
* `numeric_reduction` — the closing arithmetic of §5: from
  `X ≤ C(√n + n/X)·log n` (with `X = log p`) deduce `n ≥ c(X/log X)²`.
* `main_lower_bound` (the strengthened setwise form) and `m_lower_bound`
  (**Theorem 1.2**, and the lower-bound half of the corollary) — proved without
  missing premises. Their proofs perform the actual reduction: minimal subexample →
  enumeration → pairing → determinant bridge → numeric endgame.

## Design notes

* Unordered pairs/index pairs are `Sym2` (of `ZMod p`-elements as two-element
  `Multiset`s, of indices as `Sym2 (Fin n)`); `{a,a}` is allowed, matching the paper.
* `HasNoUniqueSum` is stated in the paper's "equivalently" form: every two-element
  multiset from `A` has a distinct equal-sum mate.
* The paper's `μ` (one cyclic permutation per fiber) is abstracted into `Pairing`:
  a fixed-point-free permutation of `Sym2 (Fin n)` preserving the fibers of the sum
  map — the only two properties the proofs use.  Existence is proved.
* Logarithmic bounds are stated in exponential/`Real.log` form
  (e.g. `p ≤ 2^(|X|+|Y|−2)` for `|X|+|Y| ≥ log₂ p + 2`).
* In Lemma 3.2 the vertex set is `Option V`: `none` is the root; a rootless instance
  is the special case where no edge meets `none`.
* "Sufficiently large `p`" is normalized to `64 ≤ p` (which makes
  `L = ⌊log₂ p / 3⌋ ≥ 2`) plus the absolute constants carried through the statements.
