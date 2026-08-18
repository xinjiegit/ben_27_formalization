/-
# The final determinant and the main theorem (Section 5)

This file assembles the proof of Theorem 1.2:

* `key_inequality` — the Section 5 determinant argument: combining Proposition 4.1
  (compression) with Lemma 1.3 (`p` divides every maximal minor) and Hadamard's
  inequality yields `p ≤ (4M)^{K-1}` with `M = n^{O(1)}` and
  `K = O(√n + n/log p)`, i.e. `log p ≤ C (√n + n/log p) log n`.  Its proof is
  factored into `FinalDeterminant.lean`.
* `numeric_reduction` — the closing arithmetic: the displayed inequality forces
  `n ≫ (log p / log log p)²`.  Proved.
* `main_lower_bound` — the strengthened setwise form used to prove **Theorem 1.2**,
  proved from the two ingredients above together with the Section 1 results
  (inclusion-minimal extraction, existence of a pairing).
* `m_lower_bound` — **Theorem 1.2** as stated for `m(p)`; it is also the lower-bound
  half of the **Corollary** `m(p) = (log p)^{2+o(1)}`.
-/
import NUSLean.FinalDeterminant

namespace NUS

open MinimalNUS

/-- Any finite set can be enumerated by an embedding of `Fin`. -/
theorem exists_enum {γ : Type*} (B : Finset γ) :
    ∃ a : Fin B.card ↪ γ, Finset.univ.map a = B := by
  classical
  let e : ↥B ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe B)
  refine ⟨⟨fun i => (e.symm i : γ), fun i j hij => ?_⟩, ?_⟩
  · exact e.symm.injective (Subtype.coe_injective hij)
  · ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩

/-- **The Section 5 determinant bound.**  In a unimodular coordinate system adapted to
the primitive pivots of Proposition 4.1, `K − 1` further collision rows have their
images in the core; Lemma 1.3 makes the resulting maximal minor a nonzero multiple of
`p`, while Hadamard's inequality bounds it by `(4M)^{K-1}` with `M = n^{O(1)}`.
Taking logarithms gives the displayed inequality.  -/
theorem key_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (_ : S.Pairing),
        64 ≤ p →
        Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n := by
  exact key_inequality_proof

/-- **The closing arithmetic of Section 5.**  If `X = log p` satisfies
`X ≤ C(√n + n/X)·log n`, then `n ≫ (X / log X)²`. -/
theorem numeric_reduction (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ p n : ℕ, 64 ≤ p → 2 ≤ n →
      Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n →
      c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ n := by
  refine ⟨min 1 (1 / (16 * C ^ 2)), by positivity, ?_⟩
  intro p n hp hn hkey
  set X := Real.log p with hXdef
  set L := Real.log X with hLdef
  -- basic estimates
  have hX4 : 4 ≤ X := by
    have h1 : Real.log 64 ≤ X := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hp
    have h2 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    have h1 : Real.log 4 ≤ L := by
      apply Real.log_le_log (by norm_num) hX4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  have hL0 : 0 < L := by linarith
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hn
  have hsn1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hsn0 : 0 < Real.sqrt n := by linarith
  have hlogn0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rcases le_or_gt (X ^ 2) (n : ℝ) with hcase | hcase
  · -- if `n ≥ X²` the bound is immediate
    have hXL : X / L ≤ X := by
      rw [div_le_iff₀ hL0]
      nlinarith
    have h1 : (X / L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hXL 2
    calc min 1 (1 / (16 * C ^ 2)) * (X / L) ^ 2
        ≤ 1 * (X / L) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (X / L) ^ 2 := one_mul _
      _ ≤ X ^ 2 := h1
      _ ≤ n := hcase
  · -- otherwise `n < X²`; then `√n ≤ X`, `n/X ≤ √n`, `log n ≤ 2 log X`
    have hsX : Real.sqrt n ≤ X := by
      have := Real.sqrt_le_sqrt hcase.le
      rwa [Real.sqrt_sq hX0.le] at this
    have hnX : (n : ℝ) / X ≤ Real.sqrt n := by
      rw [div_le_iff₀ hX0]
      calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        _ ≤ Real.sqrt n * X := by
            apply mul_le_mul_of_nonneg_left hsX hsn0.le
    have hlogn : Real.log n ≤ 2 * L := by
      calc Real.log n ≤ Real.log (X ^ 2) := Real.log_le_log hn0 hcase.le
        _ = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
    -- hence `X ≤ 4C√n·L`
    have hXb : X ≤ 4 * C * Real.sqrt n * L := by
      have hstep : C * (Real.sqrt n + n / X) * Real.log n ≤
          C * (Real.sqrt n + Real.sqrt n) * (2 * L) := by
        gcongr
      calc X ≤ C * (Real.sqrt n + n / X) * Real.log n := hkey
        _ ≤ C * (Real.sqrt n + Real.sqrt n) * (2 * L) := hstep
        _ = 4 * C * Real.sqrt n * L := by ring
    -- square it
    have hXsq : X ^ 2 ≤ 16 * C ^ 2 * n * L ^ 2 := by
      have h := pow_le_pow_left₀ hX0.le hXb 2
      calc X ^ 2 ≤ (4 * C * Real.sqrt n * L) ^ 2 := h
        _ = 16 * C ^ 2 * (Real.sqrt n * Real.sqrt n) * L ^ 2 := by ring
        _ = 16 * C ^ 2 * n * L ^ 2 := by rw [Real.mul_self_sqrt hn0.le]
    have hdiv : (X / L) ^ 2 ≤ 16 * C ^ 2 * n := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    calc min 1 (1 / (16 * C ^ 2)) * (X / L) ^ 2
        ≤ 1 / (16 * C ^ 2) * (X / L) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ 1 / (16 * C ^ 2) * (16 * C ^ 2 * n) := by
          apply mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = n := by field_simp

/-- The strengthened setwise form of **Theorem 1.2**.  There is an absolute constant
`c > 0` such that, for every sufficiently large prime `p`, every set `A ⊆ 𝔽_p` with
`|A| ≥ 2` having no unique sum satisfies
`|A| ≥ c (log p / log log p)²`. -/
theorem main_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, Fact p.Prime → p₀ ≤ p →
      ∀ A : Finset (ZMod p), 2 ≤ A.card → HasNoUniqueSum A →
        c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ A.card := by
  obtain ⟨C, hC, hkey⟩ := key_inequality
  obtain ⟨c, hc, hnum⟩ := numeric_reduction C hC
  refine ⟨c, hc, 64, ?_⟩
  intro p hp hp₀ A hA2 hAnus
  -- pass to an inclusion-minimal subexample
  obtain ⟨B, hBA, hB2, hBnus, hBmin⟩ := exists_minimal A hA2 hAnus
  obtain ⟨a, ha⟩ := exists_enum B
  have hSnus : HasNoUniqueSum (Finset.univ.map a) := by rw [ha]; exact hBnus
  have hSmin : ∀ C', C' ⊂ Finset.univ.map a → 2 ≤ C'.card → ¬HasNoUniqueSum C' := by
    rw [ha]; exact hBmin
  let S : MinimalNUS p B.card := ⟨a, hB2, hSnus, hSmin⟩
  obtain ⟨P⟩ := S.exists_pairing
  have hkey' := hkey p B.card hp S P hp₀
  have hnum' := hnum p B.card hp₀ hB2 hkey'
  calc c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ B.card := hnum'
    _ ≤ A.card := by exact_mod_cast Finset.card_le_card hBA

/-- **Theorem 1.2.**  For all sufficiently large primes,
`m(p) ≥ c (log p / log log p)²`.  This is also the lower-bound half of the
**Corollary**; together with Bedert's construction `m(p) = O((log p)²)`, it gives
`m(p) = (log p)^{2+o(1)}`. -/
theorem m_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, Fact p.Prime → p₀ ≤ p →
      c * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ m p := by
  obtain ⟨c, hc, p₀, hmain⟩ := main_lower_bound
  refine ⟨c, hc, max p₀ 3, ?_⟩
  intro p hp hp₀
  haveI := hp
  have hp2 : p ≠ 2 := by
    have h3 := le_trans (le_max_right p₀ 3) hp₀
    omega
  obtain ⟨A, hAcard, hm2, hAnus⟩ := m_spec p hp2
  have h2A : 2 ≤ A.card := by rw [hAcard]; exact hm2
  have := hmain p hp (le_trans (le_max_left p₀ 3) hp₀) A h2A hAnus
  rw [hAcard] at this
  exact this

end NUS
