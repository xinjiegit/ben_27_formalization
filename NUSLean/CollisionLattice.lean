/-
# The collision lattice of an inclusion-minimal example (Section 1)

Fix an inclusion-minimal set `A = {a_1, …, a_n} ⊆ 𝔽_p` having no unique sum.  The set of
unordered index pairs `Ω = {(i,j) : i ≤ j}` is formalized as `Sym2 (Fin n)`.  The paper
chooses, on each fiber of the sum map `σ(i,j) = a_i + a_j`, a cyclic permutation `μ`,
and forms the collision rows `ρ_t = u_t − u_{μ(t)}` spanning the collision lattice `Λ`.

Main results of this file (Lemma 1.3 of the paper, proved in full):
* `MinimalNUS.finrank_span_rhoQ` — the lattice has rational rank `n − 1`;
* `MinimalNUS.finrank_span_modp_le` — mod `p` the row rank is at most `n − 2`;
* `MinimalNUS.p_dvd_maximal_minor` — hence every maximal minor of an `(n−1)`-row
  matrix with rows in `Λ` is divisible by `p`.
-/
import NUSLean.Defs
import NUSLean.Derangement

namespace NUS

open Finset Matrix

/-- Every element of `Sym2 α` is of the form `s(x, y)`. -/
theorem sym2_surj {α : Type*} (z : Sym2 α) : ∃ x y, z = s(x, y) :=
  Sym2.ind (fun x y => ⟨x, y, rfl⟩) z

/-! ### The vectors `u_t` and pair sums -/

variable {n : ℕ}

/-- `u_t = e_i + e_j ∈ ℤ^n` for `t = {i,j}`; in particular `u_{i,i} = 2·e_i`. -/
def uvec : Sym2 (Fin n) → (Fin n → ℤ) :=
  Sym2.lift ⟨fun i j => Pi.single i 1 + Pi.single j 1, fun _ _ => add_comm _ _⟩

@[simp] theorem uvec_mk (i j : Fin n) :
    uvec s(i, j) = Pi.single i 1 + Pi.single j 1 := rfl

/-- The symmetric pair-sum `x_i + x_j`, as a function on unordered index pairs. -/
def pairSum {R : Type*} [AddCommMonoid R] (x : Fin n → R) : Sym2 (Fin n) → R :=
  Sym2.lift ⟨fun i j => x i + x j, fun _ _ => add_comm _ _⟩

@[simp] theorem pairSum_mk {R : Type*} [AddCommMonoid R] (x : Fin n → R) (i j : Fin n) :
    pairSum x s(i, j) = x i + x j := rfl

/-- The fundamental computation: `⟨u_t, x⟩` is the pair sum of `x` at `t`
(after extending scalars along `ℤ → R`). -/
theorem uvec_cast_dot {R : Type*} [CommRing R] (t : Sym2 (Fin n)) (x : Fin n → R) :
    (fun k => ((uvec t k : ℤ) : R)) ⬝ᵥ x = pairSum x t := by
  induction t using Sym2.ind with
  | _ i j =>
    simp only [uvec_mk, pairSum_mk, dotProduct, Pi.add_apply, Pi.single_apply]
    push_cast
    simp [add_mul, ite_mul, Finset.sum_add_distrib]

/-! ### Minimal systems and pairings -/

/-- An inclusion-minimal set with no unique sum in `𝔽_p`, presented through an
enumeration `a : Fin n ↪ ZMod p` of its elements. -/
structure MinimalNUS (p n : ℕ) where
  /-- the enumeration of the elements of `A` -/
  a : Fin n ↪ ZMod p
  two_le : 2 ≤ n
  nus : HasNoUniqueSum (Finset.univ.map a)
  minimal : ∀ C, C ⊂ Finset.univ.map a → 2 ≤ C.card → ¬HasNoUniqueSum C

namespace MinimalNUS

variable {p : ℕ} (S : MinimalNUS p n)

/-- The underlying set `A ⊆ 𝔽_p`. -/
def carrier : Finset (ZMod p) := Finset.univ.map S.a

theorem mem_carrier (i : Fin n) : S.a i ∈ S.carrier :=
  mem_map_of_mem _ (mem_univ i)

/-- The sum map `σ : Ω → 𝔽_p`, `σ{i,j} = a_i + a_j`. -/
def sumMap : Sym2 (Fin n) → ZMod p :=
  Sym2.lift ⟨fun i j => S.a i + S.a j, fun _ _ => add_comm _ _⟩

@[simp] theorem sumMap_mk (i j : Fin n) : S.sumMap s(i, j) = S.a i + S.a j := rfl

theorem pairSum_a (t : Sym2 (Fin n)) : pairSum (fun i => S.a i) t = S.sumMap t := by
  induction t using Sym2.ind with
  | _ i j => rfl

/-- The two-element multiset `{a_i, a_j}` indexed by `t = {i,j}`. -/
def pairMul : Sym2 (Fin n) → Multiset (ZMod p) :=
  Sym2.lift ⟨fun i j => {S.a i, S.a j}, fun _ _ => Multiset.pair_comm _ _⟩

@[simp] theorem pairMul_mk (i j : Fin n) : S.pairMul s(i, j) = {S.a i, S.a j} := rfl

theorem isPairFrom_pairMul (t : Sym2 (Fin n)) : IsPairFrom S.carrier (S.pairMul t) := by
  induction t using Sym2.ind with
  | _ i j =>
    refine ⟨by simp, ?_⟩
    intro x hx
    rcases (by simpa using hx : x = S.a i ∨ x = S.a j) with rfl | rfl
    exacts [S.mem_carrier i, S.mem_carrier j]

theorem sum_pairMul (t : Sym2 (Fin n)) : (S.pairMul t).sum = S.sumMap t := by
  induction t using Sym2.ind with
  | _ i j => simp

/-- Since `A` has no unique sum, every index pair has a distinct index pair with the
same sum: the fibers of `σ` all have at least two elements. -/
theorem exists_mate (t : Sym2 (Fin n)) :
    ∃ t' : Sym2 (Fin n), t' ≠ t ∧ S.sumMap t' = S.sumMap t := by
  obtain ⟨m', ⟨hcard, hmem⟩, hne, hsum⟩ := S.nus (S.pairMul t) (S.isPairFrom_pairMul t)
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hcard
  obtain ⟨i', -, hi'⟩ := Finset.mem_map.mp (hmem c (by simp))
  obtain ⟨j', -, hj'⟩ := Finset.mem_map.mp (hmem d (by simp))
  refine ⟨s(i', j'), fun hEq => hne ?_, ?_⟩
  · have : S.pairMul s(i', j') = S.pairMul t := by rw [hEq]
    rw [pairMul_mk, hi', hj'] at this
    exact this
  · have : ({c, d} : Multiset (ZMod p)).sum = S.sumMap t := by rw [hsum, S.sum_pairMul]
    rw [sumMap_mk, hi', hj']
    simpa using this

/-- A pairing `μ`: a fixed-point-free permutation of the unordered index pairs
preserving the fibers of the sum map.  (The paper takes the union of one cyclic
permutation on each fiber; only these two properties are ever used.) -/
structure Pairing (S : MinimalNUS p n) where
  /-- the permutation of index pairs -/
  μ : Equiv.Perm (Sym2 (Fin n))
  sumMap_fix : ∀ t, S.sumMap (μ t) = S.sumMap t
  ne : ∀ t, μ t ≠ t

/-- Existence of a pairing (the choice of `μ` at the start of Section 1). -/
theorem exists_pairing : Nonempty S.Pairing := by
  obtain ⟨π, hfib, hne⟩ := exists_fiberwise_derangement S.sumMap fun t => by
    obtain ⟨t', h1, h2⟩ := S.exists_mate t
    exact ⟨t', h1, h2⟩
  exact ⟨⟨π, hfib, hne⟩⟩

/-! ### Collision rows and the collision lattice -/

/-- The collision row `ρ_t = u_t − u_{μ(t)} ∈ ℤ^n`. -/
def rho (P : S.Pairing) (t : Sym2 (Fin n)) : Fin n → ℤ :=
  uvec t - uvec (P.μ t)

/-- The collision lattice `Λ = span_ℤ {ρ_t}`. -/
def colLat (P : S.Pairing) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range (S.rho P))

/-- `⟨ρ_t, x⟩ = (x_i + x_j) − (x_{i'} + x_{j'})` where `μ(t) = {i',j'}`. -/
theorem rho_cast_dot {R : Type*} [CommRing R] (P : S.Pairing) (t : Sym2 (Fin n))
    (x : Fin n → R) :
    (fun k => ((S.rho P t k : ℤ) : R)) ⬝ᵥ x = pairSum x t - pairSum x (P.μ t) := by
  have hfun : (fun k => ((S.rho P t k : ℤ) : R)) =
      (fun k => ((uvec t k : ℤ) : R)) - fun k => ((uvec (P.μ t) k : ℤ) : R) := by
    funext k
    simp [rho]
  rw [hfun, sub_dotProduct, uvec_cast_dot, uvec_cast_dot]

/-- The collision rows are orthogonal to the all-ones vector (over any ring). -/
theorem rho_cast_dot_one {R : Type*} [CommRing R] (P : S.Pairing) (t : Sym2 (Fin n)) :
    (fun k => ((S.rho P t k : ℤ) : R)) ⬝ᵥ (fun _ => (1 : R)) = 0 := by
  rw [rho_cast_dot]
  have h2 : ∀ z : Sym2 (Fin n), pairSum (fun _ => (1 : R)) z = 2 := by
    intro z
    induction z using Sym2.ind with
    | _ i j => rw [pairSum_mk]; norm_num
  rw [h2, h2, sub_self]

/-- Mod `p`, the collision rows are orthogonal to the label vector `a`. -/
theorem rho_cast_dot_a (P : S.Pairing) (t : Sym2 (Fin n)) :
    (fun k => ((S.rho P t k : ℤ) : ZMod p)) ⬝ᵥ (fun i => S.a i) = 0 := by
  rw [rho_cast_dot, pairSum_a, pairSum_a, P.sumMap_fix, sub_self]

/-! ### The kernel of the collision rows: the heart of Lemma 1.3

A rational vector orthogonal to all collision rows must be constant; otherwise its
argmax index set `M` would produce a proper subset of `A` with no unique sum,
contradicting inclusion-minimality. -/

theorem eq_const_of_rho_dot_eq_zero (P : S.Pairing) (x : Fin n → ℚ)
    (hx : ∀ t, (fun k => ((S.rho P t k : ℤ) : ℚ)) ⬝ᵥ x = 0) (i j : Fin n) : x i = x j := by
  by_contra hne
  -- pair sums are invariant along μ
  have hw : ∀ t, pairSum x (P.μ t) = pairSum x t := by
    intro t
    have h := hx t
    rw [S.rho_cast_dot P t x, sub_eq_zero] at h
    exact h.symm
  -- the argmax set M
  haveI hne' : Nonempty (Fin n) := ⟨i⟩
  have himg : (Finset.univ.image x).Nonempty :=
    Finset.univ_nonempty.image x
  set xmax := (Finset.univ.image x).max' himg with hxmax
  set M := Finset.univ.filter (fun k => x k = xmax) with hMdef
  have hle : ∀ k, x k ≤ xmax := fun k =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem x (Finset.mem_univ k))
  have hmemM : ∀ k, k ∈ M ↔ x k = xmax := by
    intro k
    simp [hMdef]
  have hMne : M.Nonempty := by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp ((Finset.univ.image x).max'_mem himg)
    exact ⟨k, (hmemM k).mpr hk⟩
  -- μ-stability of pairs inside M
  have hstab : ∀ t : Sym2 (Fin n), (∀ k ∈ t, k ∈ M) → ∀ k ∈ P.μ t, k ∈ M := by
    intro t ht
    obtain ⟨i₀, j₀, rfl⟩ := sym2_surj t
    obtain ⟨i₁, j₁, h₁⟩ := sym2_surj (P.μ s(i₀, j₀))
    have hi₀ : x i₀ = xmax := (hmemM i₀).mp (ht i₀ (Sym2.mem_mk_left _ _))
    have hj₀ : x j₀ = xmax := (hmemM j₀).mp (ht j₀ (Sym2.mem_mk_right _ _))
    have hsum : x i₁ + x j₁ = x i₀ + x j₀ := by
      have := hw s(i₀, j₀)
      rw [h₁, pairSum_mk, pairSum_mk] at this
      exact this
    have hmax1 : x i₁ = xmax ∧ x j₁ = xmax := by
      constructor <;> [skip; skip] <;>
        · have h1 := hle i₁
          have h2 := hle j₁
          rw [hi₀, hj₀] at hsum
          linarith
    intro k hk
    rw [h₁] at hk
    rcases Sym2.mem_iff.mp hk with rfl | rfl
    · exact (hmemM k).mpr hmax1.1
    · exact (hmemM k).mpr hmax1.2
  -- M has at least two elements
  have hM2 : 2 ≤ M.card := by
    by_contra hlt
    obtain ⟨i₁, hMi₁⟩ := Finset.card_eq_one.mp
      (le_antisymm (by omega) (Finset.card_pos.mpr hMne))
    have hmem : ∀ k ∈ s(i₁, i₁), k ∈ M := by
      intro k hk
      rcases Sym2.mem_iff.mp hk with rfl | rfl <;> simp [hMi₁]
    have hin := hstab s(i₁, i₁) hmem
    obtain ⟨c, d, hcd⟩ := sym2_surj (P.μ s(i₁, i₁))
    have hc : c ∈ M := hin c (by rw [hcd]; exact Sym2.mem_mk_left _ _)
    have hd : d ∈ M := hin d (by rw [hcd]; exact Sym2.mem_mk_right _ _)
    rw [hMi₁, Finset.mem_singleton] at hc hd
    exact P.ne s(i₁, i₁) (by rw [hcd, hc, hd])
  -- M is proper
  have hMuniv : M ≠ Finset.univ := by
    intro hEq
    apply hne
    have hi : x i = xmax := (hmemM i).mp (hEq ▸ Finset.mem_univ i)
    have hj : x j = xmax := (hmemM j).mp (hEq ▸ Finset.mem_univ j)
    rw [hi, hj]
  -- the sub-example on the argmax indices
  set B := M.map S.a with hBdef
  have hBcard : 2 ≤ B.card := by rw [hBdef, Finset.card_map]; exact hM2
  have hBsub : B ⊂ S.carrier :=
    Finset.map_ssubset_map.mpr (Finset.ssubset_univ_iff.mpr hMuniv)
  have hBnus : HasNoUniqueSum B := by
    rintro tm ⟨hcard2, hmem2⟩
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hcard2
    obtain ⟨i₀, hi₀M, hi₀⟩ := Finset.mem_map.mp (hmem2 c (by simp))
    obtain ⟨j₀, hj₀M, hj₀⟩ := Finset.mem_map.mp (hmem2 d (by simp))
    obtain ⟨i₁, j₁, h₁⟩ := sym2_surj (P.μ s(i₀, j₀))
    have hin : ∀ k ∈ P.μ s(i₀, j₀), k ∈ M := by
      apply hstab
      intro k hk
      rcases Sym2.mem_iff.mp hk with rfl | rfl
      exacts [hi₀M, hj₀M]
    have hi₁M : i₁ ∈ M := hin i₁ (by rw [h₁]; exact Sym2.mem_mk_left _ _)
    have hj₁M : j₁ ∈ M := hin j₁ (by rw [h₁]; exact Sym2.mem_mk_right _ _)
    refine ⟨{S.a i₁, S.a j₁}, ⟨by simp, ?_⟩, ?_, ?_⟩
    · intro z hz
      rcases (by simpa using hz : z = S.a i₁ ∨ z = S.a j₁) with rfl | rfl
      exacts [Finset.mem_map_of_mem _ hi₁M, Finset.mem_map_of_mem _ hj₁M]
    · -- distinctness, from `μ t ≠ t` and injectivity of the enumeration
      intro hEqm
      apply P.ne s(i₀, j₀)
      rw [h₁]
      rw [← hi₀, ← hj₀, multiset_pair_eq_pair] at hEqm
      rcases hEqm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [S.a.injective h1, S.a.injective h2]
      · rw [S.a.injective h1, S.a.injective h2]
        exact Sym2.eq_swap
    · -- equal sums, from μ preserving the fibers of σ
      have hfix := P.sumMap_fix s(i₀, j₀)
      rw [h₁, sumMap_mk, sumMap_mk] at hfix
      simpa [← hi₀, ← hj₀] using hfix
  exact S.minimal B hBsub hBcard hBnus

/-! ### Lemma 1.3(a): the rational rank is `n − 1` -/

/-- The collision rows over `ℚ`. -/
def rhoQ (P : S.Pairing) (t : Sym2 (Fin n)) : Fin n → ℚ :=
  fun k => ((S.rho P t k : ℤ) : ℚ)

/-- **Lemma 1.3, first part.**  The collision lattice has rational rank `n − 1`. -/
theorem finrank_span_rhoQ (P : S.Pairing) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (S.rhoQ P))) = n - 1 := by
  classical
  have hn := S.two_le
  set R : Matrix (Sym2 (Fin n)) (Fin n) ℚ := Matrix.of fun t => S.rhoQ P t with hRdef
  -- the kernel of `x ↦ (⟨ρ_t, x⟩)_t` is the line of constant vectors
  have hker : LinearMap.ker R.mulVecLin = Submodule.span ℚ {fun _ => (1 : ℚ)} := by
    apply le_antisymm
    · intro x hxk
      have hx : ∀ t, (fun k => ((S.rho P t k : ℤ) : ℚ)) ⬝ᵥ x = 0 := by
        intro t
        have := LinearMap.mem_ker.mp hxk
        exact congrFun this t
      have hconst := S.eq_const_of_rho_dot_eq_zero P x hx
      refine Submodule.mem_span_singleton.mpr ⟨x ⟨0, by omega⟩, ?_⟩
      funext k
      simp [hconst k ⟨0, by omega⟩]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      funext t
      simpa [hRdef, Matrix.mulVecLin_apply, Matrix.mulVec, rhoQ] using
        S.rho_cast_dot_one (R := ℚ) P t
  have hkerrank : Module.finrank ℚ (LinearMap.ker R.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton ?_
    intro hzero
    have := congrFun hzero ⟨0, by omega⟩
    norm_num at this
  have hrn := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  rw [hkerrank, Module.finrank_pi] at hrn
  have hrank : R.rank = n - 1 := by
    have : R.rank + 1 = n := by
      rw [Matrix.rank]
      simpa using hrn
    omega
  have hspan := R.rank_eq_finrank_span_row
  rw [hrank] at hspan
  have hrange : Set.range R.row = Set.range (S.rhoQ P) := rfl
  rw [hrange] at hspan
  exact hspan.symm

/-! ### Lemma 1.3(b),(c): the modular defect -/

/-- Mod-`p` reduction of integer vectors, as a `ℤ`-linear map. -/
def modp (p : ℕ) {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod p) where
  toFun v := fun k => ((v k : ℤ) : ZMod p)
  map_add' u v := by
    funext k
    simp
  map_smul' c v := by
    funext k
    simp [zsmul_eq_mul]

/-- Every vector of the collision lattice is orthogonal, mod `p`, to both the all-ones
vector and the label vector `a`. -/
theorem colLat_orth (P : S.Pairing) {y : Fin n → ℤ} (hy : y ∈ S.colLat P) :
    (modp p y) ⬝ᵥ (fun _ => (1 : ZMod p)) = 0 ∧ (modp p y) ⬝ᵥ (fun i => S.a i) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact ⟨S.rho_cast_dot_one P t, S.rho_cast_dot_a P t⟩
  | zero => simp
  | add u v hu hv hu' hv' =>
    rw [map_add, add_dotProduct, add_dotProduct, hu'.1, hv'.1, hu'.2, hv'.2]
    simp
  | smul c u hu hu' =>
    rw [map_smul, smul_dotProduct, smul_dotProduct, hu'.1, hu'.2]
    simp

section ModularDefect

variable [Fact p.Prime]

/-- The `n × 2` matrix with columns `𝟙` and `a`, transposed: its kernel is the space `W`
of vectors orthogonal to both. -/
def Bt : Matrix (Fin 2) (Fin n) (ZMod p) :=
  Matrix.of ![fun _ => (1 : ZMod p), fun i => S.a i]

theorem Bt_rank : (Bt S).rank = 2 := by
  have hn := S.two_le
  have i₀ : Fin n := ⟨0, by omega⟩
  have i₁ : Fin n := ⟨1, by omega⟩
  have hli : LinearIndependent (ZMod p) (Bt S).row := by
    have hrow : (Bt S).row = ![fun _ => (1 : ZMod p), fun i => S.a i] := rfl
    rw [hrow, linearIndependent_fin2]
    constructor
    · -- the label vector is nonzero: `a` is injective and `n ≥ 2`
      intro hzero
      have h0 : S.a ⟨0, by omega⟩ = 0 := congrFun (by simpa using hzero) _
      have h1 : S.a ⟨1, by omega⟩ = 0 := congrFun (by simpa using hzero) _
      have := S.a.injective (h0.trans h1.symm)
      simp [Fin.ext_iff] at this
    · -- no multiple of the label vector is the all-ones vector
      intro c hc
      have h0 : c * S.a ⟨0, by omega⟩ = 1 := congrFun (by simpa using hc) _
      have h1 : c * S.a ⟨1, by omega⟩ = 1 := congrFun (by simpa using hc) _
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, zero_mul] at h0
        exact zero_ne_one h0
      have : S.a ⟨0, by omega⟩ = S.a ⟨1, by omega⟩ :=
        mul_left_cancel₀ hc0 (h0.trans h1.symm)
      have := S.a.injective this
      simp [Fin.ext_iff] at this
  have := hli.rank_matrix
  simpa using this

/-- The space of mod-`p` vectors orthogonal to `𝟙` and to `a` has dimension `n − 2`. -/
theorem finrank_ker_Bt :
    Module.finrank (ZMod p) (LinearMap.ker (Bt S).mulVecLin) = n - 2 := by
  have hn := S.two_le
  have hrn := LinearMap.finrank_range_add_finrank_ker (Bt S).mulVecLin
  rw [Module.finrank_pi] at hrn
  have hr : Module.finrank (ZMod p) (LinearMap.range (Bt S).mulVecLin) = 2 := by
    have := Bt_rank S
    rw [Matrix.rank] at this
    exact this
  rw [hr] at hrn
  simp only [Fintype.card_fin] at hrn
  omega

theorem mem_ker_Bt_of_orth {y : Fin n → ZMod p}
    (h1 : y ⬝ᵥ (fun _ => (1 : ZMod p)) = 0) (ha : y ⬝ᵥ (fun i => S.a i) = 0) :
    y ∈ LinearMap.ker (Bt S).mulVecLin := by
  rw [LinearMap.mem_ker]
  funext r
  fin_cases r
  · simpa [Bt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct_comm] using h1
  · simpa [Bt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct_comm] using ha

/-- **Lemma 1.3, second part.**  Mod `p`, the rows of the collision lattice span a space
of dimension at most `n − 2`. -/
theorem finrank_span_modp_le (P : S.Pairing) :
    Module.finrank (ZMod p)
      (Submodule.span (ZMod p) (Set.range (fun t => modp p (S.rho P t)))) ≤ n - 2 := by
  have hsub : Submodule.span (ZMod p) (Set.range (fun t => modp p (S.rho P t))) ≤
      LinearMap.ker (Bt S).mulVecLin := by
    rw [Submodule.span_le]
    rintro y ⟨t, rfl⟩
    have horth := S.colLat_orth P (Submodule.subset_span (Set.mem_range_self t))
    exact S.mem_ker_Bt_of_orth horth.1 horth.2
  calc Module.finrank (ZMod p) (Submodule.span (ZMod p) _)
      ≤ Module.finrank (ZMod p) (LinearMap.ker (Bt S).mulVecLin) :=
        Submodule.finrank_mono hsub
    _ = n - 2 := finrank_ker_Bt S

/-- **Lemma 1.3, final part.**  Every maximal minor of an `(n−1)`-row integer matrix
whose rows lie in the collision lattice is divisible by `p`. -/
theorem p_dvd_maximal_minor (P : S.Pairing)
    (v : Fin (n - 1) → (Fin n → ℤ)) (hv : ∀ r, v r ∈ S.colLat P)
    (cols : Fin (n - 1) ↪ Fin n) :
    (p : ℤ) ∣ (Matrix.of fun r l => v r (cols l)).det := by
  classical
  have hn := S.two_le
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ((Matrix.of fun r l => v r (cols l)).det : ZMod p) =
      (Matrix.of fun r l => ((v r (cols l) : ℤ) : ZMod p)).det :=
    RingHom.map_det (Int.castRingHom (ZMod p)) (Matrix.of fun r l => v r (cols l))
  rw [key]
  -- suppose the reduced square matrix were nonsingular
  by_contra hdet
  have hsq : LinearIndependent (ZMod p)
      (fun r => (Matrix.of fun r l => ((v r (cols l) : ℤ) : ZMod p)) r) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  -- then the full mod-p rows would be independent
  have hfull : LinearIndependent (ZMod p) (fun r => modp p (v r)) := by
    rw [Fintype.linearIndependent_iff] at hsq ⊢
    intro g hg
    apply hsq g
    funext l
    have := congrFun hg (cols l)
    simpa [modp, Matrix.map_apply, Finset.sum_apply] using this
  -- but they lie in a space of dimension n − 2
  have hmem : ∀ r, modp p (v r) ∈ LinearMap.ker (Bt S).mulVecLin := by
    intro r
    have horth := S.colLat_orth P (hv r)
    exact S.mem_ker_Bt_of_orth horth.1 horth.2
  have hres : LinearIndependent (ZMod p)
      (fun r => (⟨modp p (v r), hmem r⟩ : LinearMap.ker (Bt S).mulVecLin)) := by
    apply LinearIndependent.of_comp (LinearMap.ker (Bt S).mulVecLin).subtype
    exact hfull
  have hcard := hres.fintype_card_le_finrank
  rw [finrank_ker_Bt S, Fintype.card_fin] at hcard
  omega

/-- Generalization of `p_dvd_maximal_minor`: for an arbitrary integer matrix `U`,
`p` divides `det (V * U)` whenever the `n − 1` rows of `V` lie in the collision
lattice.  Maximal minors are the case of column-selection matrices; this form also
covers arbitrary (e.g. unimodular) column operations, as needed in Section 5. -/
theorem p_dvd_det_mul (P : S.Pairing)
    (v : Fin (n - 1) → (Fin n → ℤ)) (hv : ∀ r, v r ∈ S.colLat P)
    (U : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    (p : ℤ) ∣ (Matrix.of v * U).det := by
  classical
  have hn := S.two_le
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : (((Matrix.of v * U).det : ℤ) : ZMod p) =
      ((Matrix.of v * U).map ⇑(Int.castRingHom (ZMod p))).det :=
    RingHom.map_det (Int.castRingHom (ZMod p)) _
  rw [key, Matrix.map_mul]
  by_contra hdet
  -- the reduced row matrix has rank at most `n − 2` …
  have hzero : (Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) * (Bt S)ᵀ = 0 := by
    ext r c
    have horth := S.colLat_orth P (hv r)
    fin_cases c
    · simpa [Matrix.mul_apply, Matrix.map_apply, Bt, modp, dotProduct,
        mul_comm] using horth.1
    · simpa [Matrix.mul_apply, Matrix.map_apply, Bt, modp, dotProduct,
        mul_comm] using horth.2
  have hrank2 := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, Bt_rank S, Fintype.card_fin] at hrank2
  have hVrank : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p))).rank ≤ n - 2 := by omega
  have hprod : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) *
      U.map ⇑(Int.castRingHom (ZMod p))).rank ≤ n - 2 :=
    le_trans (Matrix.rank_mul_le_left _ _) hVrank
  -- … while a nonzero determinant would force rank `n − 1`
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hfull : ((Matrix.of v).map ⇑(Int.castRingHom (ZMod p)) *
      U.map ⇑(Int.castRingHom (ZMod p))).rank = n - 1 := by
    have := hli.rank_matrix
    simpa using this
  omega

end ModularDefect

end MinimalNUS

end NUS
