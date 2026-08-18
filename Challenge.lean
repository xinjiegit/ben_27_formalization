import Mathlib

/-!
# A near-quadratic lower bound for sets with no unique sums

This is the small statement surface submitted to the Palomar Registry.  It is
intended to be read independently of the proof development.

For a prime `p`, `ZMod p` is the prime field `𝔽_p`.  An unordered
representation is a two-element multiset drawn from `A`; thus `{a, b}` and
`{b, a}` are the same representation, while the repeated-element case
`{a, a}` is allowed.  A set has no unique sum exactly when every such multiset
has a different multiset from the same set with the same sum.  The quantity
`m p` is the least cardinality, constrained to be at least two, of such a set.

The theorem says that there are an absolute real constant `c > 0` and a
natural-number threshold `p₀` such that every prime `p ≥ p₀` satisfies

`m(p) ≥ c (log p / log log p)²`,

where `Real.log` is the natural logarithm and natural numbers are coerced to
real numbers in the displayed inequality.

The deliberate `sorry` below states the claim to be checked.  `Solution.lean`
imports the completed proof, and Comparator verifies that its declaration has
this exact statement and uses only the permitted standard Lean axioms.
-/

namespace NUS

variable {G : Type*} [AddCommGroup G]

/-- `IsPairFrom A t` means that `t` is a two-element multiset whose elements
belong to `A`.  Its two elements are allowed to coincide. -/
def IsPairFrom (A : Finset G) (t : Multiset G) : Prop :=
  Multiset.card t = 2 ∧ ∀ x ∈ t, x ∈ A

/-- A finite set has no unique sum when every unordered representation of a
sum by two elements of the set has a different unordered representation with
the same sum. -/
def HasNoUniqueSum (A : Finset G) : Prop :=
  ∀ t : Multiset G, IsPairFrom A t →
    ∃ t' : Multiset G, IsPairFrom A t' ∧ t' ≠ t ∧ t'.sum = t.sum

/-- `m p` is the least cardinality, subject to cardinality at least two, of a
subset of `ZMod p` having no unique sum. -/
noncomputable def m (p : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset (ZMod p), A.card = k ∧ 2 ≤ k ∧ HasNoUniqueSum A}

/-- **Theorem 1.2 (exact quantified form).**  There exist an absolute real
constant `c > 0` and a natural-number threshold `p₀` such that, for every
natural number `p`, if `p` is prime and `p₀ ≤ p`, then

`c * (log p / log (log p))² ≤ m(p)`.

Thus every sufficiently large prime-field set of cardinality at least two
with no uniquely represented sum has cardinality at least this quantity. -/
theorem m_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, Fact p.Prime → p₀ ≤ p →
      c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ m p := by
  sorry

end NUS
