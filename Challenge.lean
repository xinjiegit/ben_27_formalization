import Mathlib

/-!
# A near-quadratic lower bound for sets with no unique sums

This is the small statement surface submitted to the Palomar Registry.  It is
intended to be read independently of the proof development.  The repeated
element case `{a, a}` is allowed: an unordered representation is a two-element
multiset, not a two-element set.

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

/-- There is an absolute constant `c > 0` such that, for every sufficiently
large prime `p`,

`m(p) ≥ c (log p / log log p)²`.
-/
theorem m_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, Fact p.Prime → p₀ ≤ p →
      c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ m p := by
  sorry

end NUS
