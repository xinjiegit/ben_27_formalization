/-
# Fiber-preserving fixed-point-free permutations

The paper chooses, on every fiber of the sum map `σ`, one cyclic permutation, and lets
`μ` be the union of these cycles; the only properties ever used are that `μ` is a
fixed-point-free permutation preserving the fibers of `σ`.  This file proves the
existence of such a permutation for any map whose nonempty fibers all have at least two
elements.
-/
import Mathlib

namespace NUS

/-- Every finite type with at least two elements admits a fixed-point-free permutation. -/
theorem exists_derangement (α : Type*) [Fintype α] [DecidableEq α]
    (h : 2 ≤ Fintype.card α) : ∃ π : Equiv.Perm α, ∀ x, π x ≠ x := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 2 := ⟨Fintype.card α - 2, by omega⟩
  let e : α ≃ Fin (k + 2) := Fintype.equivFinOfCardEq hk
  refine ⟨e.trans ((finRotate (k + 2)).trans e.symm), fun x hx => ?_⟩
  replace hx := congrArg e hx
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, finRotate_apply] at hx
  have h1 : (1 : Fin (k + 2)) = 0 :=
    add_left_cancel (show e x + 1 = e x + 0 by rw [add_zero]; exact hx)
  rw [Fin.one_eq_zero_iff] at h1
  omega

/-- If every point of a finite type has a distinct mate in the same fiber of `f`, then
there is a fixed-point-free permutation preserving the fibers of `f`. -/
theorem exists_fiberwise_derangement {α β : Type*} [Fintype α] [DecidableEq α]
    (f : α → β) (h : ∀ x, ∃ y, y ≠ x ∧ f y = f x) :
    ∃ π : Equiv.Perm α, (∀ x, f (π x) = f x) ∧ ∀ x, π x ≠ x := by
  classical
  have hfib : ∀ b : β, ∃ δ : Equiv.Perm {y // f y = b}, ∀ z, δ z ≠ z := by
    intro b
    rcases isEmpty_or_nonempty {y // f y = b} with hE | hN
    · exact ⟨Equiv.refl _, fun z => (hE.false z).elim⟩
    · obtain ⟨⟨x, hx⟩⟩ := hN
      obtain ⟨y, hyx, hyf⟩ := h x
      have hcard : 2 ≤ Fintype.card {y // f y = b} := by
        haveI : Nontrivial {y // f y = b} :=
          ⟨⟨⟨y, hyf.trans hx⟩, ⟨x, hx⟩, by simpa using hyx⟩⟩
        exact Fintype.one_lt_card
      exact exists_derangement _ hcard
  choose δ hδ using hfib
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight δ).trans (Equiv.sigmaFiberEquiv f)), fun x => ?_, fun x hx => ?_⟩
  · exact (δ (f x) ⟨x, rfl⟩).2
  · exact hδ (f x) ⟨x, rfl⟩ (Subtype.ext hx)

end NUS
