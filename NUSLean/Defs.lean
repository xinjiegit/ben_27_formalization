/-
# Sets with no unique sums: basic definitions

Formalization of the paper "A near-quadratic lower bound for sets with no unique sums"
(working draft of July 21, 2026), Section 1.

This file contains:
* Definition 1.1 (`IsPairFrom`, `HasNoUniqueSum`), in the equivalent "every pair has a
  distinct equal-sum mate" form given in the paper;
* the quantity `m p` (Problem 27 in Green's list);
* extraction of an inclusion-minimal example (`exists_minimal`);
* the example showing that `𝔽_p` itself has no unique sum for odd `p`
  (`hasNoUniqueSum_univ`), so that `m p` is well defined and attained.
-/
import Mathlib

namespace NUS

open Finset

/-- Equality of two-element multisets, spelled out. -/
theorem multiset_pair_eq_pair {α : Type*} {a b c d : α} :
    ({a, b} : Multiset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  constructor
  · intro h
    rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨hac, hbd⟩ | ⟨_, cs, hb, hd⟩
    · exact Or.inl ⟨hac, Multiset.singleton_inj.mp hbd⟩
    · rw [Multiset.singleton_eq_cons_iff] at hb hd
      exact Or.inr ⟨hd.1.symm, hb.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm a b

variable {G : Type*} [AddCommGroup G]

/-- `IsPairFrom A t`: `t` is a two-element multiset drawn from `A`
(the two elements may coincide). -/
def IsPairFrom (A : Finset G) (t : Multiset G) : Prop :=
  Multiset.card t = 2 ∧ ∀ x ∈ t, x ∈ A

/-- **Definition 1.1.**  `A` has no unique sum if every two-element multiset from `A`
admits a *different* two-element multiset from `A` with the same sum.  This is the
"equivalently" form of the definition in the paper; it says exactly that every element
of `A + A` has at least two distinct unordered representations. -/
def HasNoUniqueSum (A : Finset G) : Prop :=
  ∀ t : Multiset G, IsPairFrom A t →
    ∃ t' : Multiset G, IsPairFrom A t' ∧ t' ≠ t ∧ t'.sum = t.sum

/-- The empty set vacuously has no unique sum; this is why the definition of `m p`
carries the side condition `2 ≤ |A|`. -/
theorem hasNoUniqueSum_empty : HasNoUniqueSum (∅ : Finset G) := by
  rintro t ⟨hcard, hmem⟩
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp hcard
  exact absurd (hmem x (by simp)) (by simp)

/-- Every set having no unique sum (of size at least two) contains an inclusion-minimal
subset with the same properties.  This is the reduction made at the start of the proof
of Theorem 1.2. -/
theorem exists_minimal (A : Finset G) :
    2 ≤ A.card → HasNoUniqueSum A →
      ∃ B, B ⊆ A ∧ 2 ≤ B.card ∧ HasNoUniqueSum B ∧
        ∀ C, C ⊂ B → 2 ≤ C.card → ¬HasNoUniqueSum C := by
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro h2 h
    by_cases hmin : ∀ C, C ⊂ A → 2 ≤ C.card → ¬HasNoUniqueSum C
    · exact ⟨A, Finset.Subset.refl A, h2, h, hmin⟩
    · push Not at hmin
      obtain ⟨C, hCA, hC2, hCnus⟩ := hmin
      obtain ⟨B, hBC, hB2, hBnus, hBmin⟩ := ih C hCA hC2 hCnus
      exact ⟨B, hBC.trans hCA.subset, hB2, hBnus, hBmin⟩

/-! ## The quantity `m p` -/

/-- `m p`: the least cardinality of a set `A ⊆ 𝔽_p`, `|A| ≥ 2`, having no unique sum
(Problem 27 in Green's list). -/
noncomputable def m (p : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset (ZMod p), A.card = k ∧ 2 ≤ k ∧ HasNoUniqueSum A}

/-- For odd `p`, the whole of `𝔽_p` has no unique sum: replace `{a, b}` by
`{a + 1, b - 1}`, or by `{b + 1, a - 1}` in the degenerate case `b = a + 1`. -/
theorem hasNoUniqueSum_univ (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    HasNoUniqueSum (univ : Finset (ZMod p)) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rintro t ⟨hcard, -⟩
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcard
  by_cases hab : b = a + 1
  · -- degenerate case: use `{b + 1, a - 1}`
    refine ⟨{b + 1, a - 1}, ⟨rfl, fun x _ => mem_univ x⟩, ?_, by
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      ring⟩
    rw [Ne, multiset_pair_eq_pair]
    rintro (⟨hba, -⟩ | ⟨hbb, -⟩)
    · -- `b + 1 = a` together with `b = a + 1` forces `2 = 0`
      apply h2
      have : a + (1 + 1) = a + 0 := by
        rw [← add_assoc, ← hab, hba, add_zero]
      have h20 : (1 + 1 : ZMod p) = 0 := add_left_cancel this
      calc (2 : ZMod p) = 1 + 1 := by norm_num
        _ = 0 := h20
    · -- `b + 1 = b` forces `1 = 0`
      exact h1 (add_left_cancel (show b + 1 = b + 0 by rw [add_zero]; exact hbb))
  · -- main case: use `{a + 1, b - 1}`
    refine ⟨{a + 1, b - 1}, ⟨rfl, fun x _ => mem_univ x⟩, ?_, by
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      ring⟩
    rw [Ne, multiset_pair_eq_pair]
    rintro (⟨haa, -⟩ | ⟨hab', -⟩)
    · exact h1 (add_left_cancel (show a + 1 = a + 0 by rw [add_zero]; exact haa))
    · exact hab hab'.symm

/-- For odd primes the defining set of `m p` is nonempty, hence the infimum is attained. -/
theorem m_spec (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ A : Finset (ZMod p), A.card = m p ∧ 2 ≤ m p ∧ HasNoUniqueSum A := by
  have hmem : m p ∈ {k | ∃ A : Finset (ZMod p), A.card = k ∧ 2 ≤ k ∧ HasNoUniqueSum A} := by
    apply Nat.sInf_mem
    refine ⟨p, univ, ?_, hp.out.two_le, hasNoUniqueSum_univ p hp2⟩
    haveI : NeZero p := ⟨hp.out.pos.ne'⟩
    rw [card_univ, ZMod.card]
  obtain ⟨A, hA, h2, hnus⟩ := hmem
  exact ⟨A, hA, h2, hnus⟩

end NUS
