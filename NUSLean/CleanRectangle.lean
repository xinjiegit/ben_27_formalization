/-
# Clean rectangles (Section 2)

For disjoint nonempty `X, Y ⊆ [n]`, the rectangle `X × Y` is the set of unordered index
pairs with one endpoint in `X` and the other in `Y`.  Lemma 2.1 says that a
`μ`-invariant rectangle must satisfy `|X| + |Y| ≥ log₂ p + 2`, stated below in the
equivalent exponential form `p ≤ 2^(|X|+|Y|-2)`.

The formalized proof below follows the paper: pass to a minimal invariant sub-rectangle
`X' × Y'`; the restricted collision rows have rational rank `x + y − 2` (kernel = the
two side-constant vectors, by minimality); a square submatrix obtained by deleting one
column on each side has nonzero determinant `D`; mod `p` the label vector gives a third
kernel vector, so `p ∣ D`; and a Laplace expansion across the retained `X'`-columns
together with total unimodularity of difference-of-basis-vector matrices bounds
`|D| ≤ C(x+y-2, x-1) ≤ 2^(x+y-2)`.
-/
import NUSLean.CollisionLattice
import Mathlib.Analysis.InnerProductSpace.Orientation

namespace NUS

open Finset Matrix
open scoped RealInnerProductSpace

/-- Hadamard's determinant inequality, in the row-vector form used below. -/
theorem abs_det_le_prod_euclidean_row_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))‖ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) := ⟨by simp⟩
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    EuclideanSpace.basisFun (Fin d) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin d)) (Fin d) := b.toBasis.orientation
  let v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => WithLp.toLp 2 (A i)
  have h := o.abs_volumeForm_apply_le v
  rw [o.volumeForm_robust' b v] at h
  have hd : b.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply]
    rw [show b.toBasis.toMatrix v = Aᵀ by
      ext i j
      simp [b, v, Module.Basis.toMatrix_apply], Matrix.det_transpose]
  rwa [hd] at h

/-! ### Near-unimodular rows

A row is *near-unimodular* if all its entries lie in `{-1, 0, 1}` with at most one `+1`
and at most one `-1`.  A square integer matrix all of whose rows are near-unimodular has
determinant `0` or `±1`: rows with two nonzero entries sum to zero, so either the all-ones
vector is in the kernel, or some row has at most one nonzero entry and we expand along it. -/

section NearUnimodular

/-- All entries in `{-1, 0, 1}`, at most one `+1`, at most one `-1`. -/
def NearUni {κ : Type*} (v : κ → ℤ) : Prop :=
  (∀ c, v c = 1 ∨ v c = 0 ∨ v c = -1) ∧
    (∀ c c', v c = 1 → v c' = 1 → c = c') ∧
    ∀ c c', v c = -1 → v c' = -1 → c = c'

theorem NearUni.comp {κ κ' : Type*} {v : κ → ℤ} (hv : NearUni v) {f : κ' → κ}
    (hf : Function.Injective f) : NearUni (v ∘ f) :=
  ⟨fun c => hv.1 (f c), fun c c' h h' => hf (hv.2.1 (f c) (f c') h h'),
    fun c c' h h' => hf (hv.2.2 (f c) (f c') h h')⟩

/-- The difference `e_a - e_b ∈ ℤ^α` of two standard basis vectors. -/
def isub {α : Type*} [DecidableEq α] (a b : α) : α → ℤ :=
  Pi.single a 1 - Pi.single b 1

theorem isub_apply {α : Type*} [DecidableEq α] (a b k : α) :
    isub a b k = (if k = a then (1 : ℤ) else 0) - if k = b then (1 : ℤ) else 0 := by
  rw [isub, Pi.sub_apply, Pi.single_apply, Pi.single_apply]

/-- The difference of two indicator vectors, pulled back along an injective map, is
near-unimodular. -/
theorem nearUni_isub {α : Type*} [DecidableEq α] {κ : Type*} {a b : α} {f : κ → α}
    (hf : Function.Injective f) :
    NearUni (fun c => isub a b (f c)) := by
  have hone : ∀ c, isub a b (f c) = 1 → f c = a := by
    intro c h
    rw [isub_apply] at h
    rcases eq_or_ne (f c) a with h1 | h1
    · exact h1
    · rw [if_neg h1] at h
      rcases eq_or_ne (f c) b with h2 | h2
      · rw [if_pos h2] at h; norm_num at h
      · rw [if_neg h2] at h; norm_num at h
  have hmone : ∀ c, isub a b (f c) = -1 → f c = b := by
    intro c h
    rw [isub_apply] at h
    rcases eq_or_ne (f c) b with h2 | h2
    · exact h2
    · rw [if_neg h2, sub_zero] at h
      rcases eq_or_ne (f c) a with h1 | h1
      · rw [if_pos h1] at h; norm_num at h
      · rw [if_neg h1] at h; norm_num at h
  refine ⟨fun c => ?_, fun c c' hc hc' => ?_, fun c c' hc hc' => ?_⟩
  · show isub a b (f c) = 1 ∨ isub a b (f c) = 0 ∨ isub a b (f c) = -1
    rw [isub_apply]
    rcases eq_or_ne (f c) a with h1 | h1 <;> rcases eq_or_ne (f c) b with h2 | h2
    · rw [if_pos h1, if_pos h2]; norm_num
    · rw [if_pos h1, if_neg h2]; norm_num
    · rw [if_neg h1, if_pos h2]; norm_num
    · rw [if_neg h1, if_neg h2]; norm_num
  · exact hf ((hone c hc).trans (hone c' hc').symm)
  · exact hf ((hmone c hc).trans (hmone c' hc').symm)

theorem sum_isub_eq_zero {α : Type*} [DecidableEq α] (T : Finset α) {a b : α}
    (ha : a ∈ T) (hb : b ∈ T) : ∑ k ∈ T, isub a b k = 0 := by
  simp [isub, Finset.sum_sub_distrib, ha, hb]

theorem isub_ne_zero_support {α : Type*} [DecidableEq α] {a b k : α}
    (h : isub a b k ≠ 0) : k = a ∨ k = b := by
  rw [isub_apply] at h
  by_cases ha : k = a
  · exact Or.inl ha
  by_cases hb : k = b
  · exact Or.inr hb
  simp [ha, hb] at h

theorem sum_sq_isub_le_two {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    ∑ k, (((isub a b k : ℤ) : ℝ) ^ 2) ≤ 2 := by
  by_cases h : a = b
  · subst b
    simp [isub]
  · calc
      ∑ k, (((isub a b k : ℤ) : ℝ) ^ 2) =
          ∑ k, (((if k = a then 1 else 0) : ℝ) ^ 2 +
            ((if k = b then 1 else 0) : ℝ) ^ 2 -
            2 * (if k = a then 1 else 0) * (if k = b then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [isub, Pi.sub_apply, Pi.single_apply]
              push_cast
              ring
      _ = 2 := by
        have hp : ∀ k : α,
            (((if k = a then 1 else 0) : ℝ) ^ 2 +
              ((if k = b then 1 else 0) : ℝ) ^ 2 -
              2 * (if k = a then 1 else 0) * (if k = b then 1 else 0)) =
            (if k = a then 1 else 0) + (if k = b then 1 else 0) := by
          intro k
          by_cases ha : k = a
          · have hb : k ≠ b := fun e => h (ha.symm.trans e)
            simp [ha, h]
          · by_cases hb : k = b <;> simp [ha, hb, Ne.symm h]
        simp_rw [hp, Finset.sum_add_distrib]
        norm_num
      _ ≤ 2 := le_rfl

/-- Select a prescribed number of independent members from a spanning family. -/
theorem exists_indep_family_of_finrank {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {ι : Type*} (g : ι → V) (d : ℕ)
    (hd : d ≤ Module.finrank F (Submodule.span F (Set.range g))) :
    ∃ t : Fin d → ι, LinearIndependent F (fun j => g (t j)) := by
  classical
  obtain ⟨sb, hsub, hspan, hli⟩ := exists_linearIndependent F (Set.range g)
  have hfin : sb.Finite := hli.setFinite
  haveI := hfin.fintype
  have hcard : d ≤ Fintype.card sb := by
    have h1 : Module.finrank F (Submodule.span F sb) = sb.toFinset.card :=
      finrank_span_set_eq_card hli
    rw [hspan] at h1
    rw [Set.toFinset_card] at h1
    omega
  let emb : Fin d ↪ sb :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin sb).symm.toEmbedding
  have hsel : ∀ x : sb, ∃ i : ι, g i = (x : V) := fun x => hsub x.2
  choose sel hsel using hsel
  refine ⟨fun j => sel (emb j), ?_⟩
  have hfun : (fun j => g (sel (emb j))) = (fun x : sb => (x : V)) ∘ emb := by
    funext j
    simp [hsel]
  rw [hfun]
  exact hli.comp emb emb.injective

/-- Independent rows yield a nonsingular square coordinate minor. -/
theorem exists_coordinate_minor {F κ : Type*} [Field F] [Fintype κ] [DecidableEq κ]
    {d : ℕ} (g : Fin d → (κ → F)) (hg : LinearIndependent F g) :
    ∃ c : Fin d ↪ κ, (Matrix.of fun i j => g i (c j)).det ≠ 0 := by
  classical
  let A : Matrix (Fin d) κ F := g
  have hrank : A.rank = d := by
    have h := hg.rank_matrix
    simpa only [A, Fintype.card_fin] using h
  have hspan : d ≤ Module.finrank F
      (Submodule.span F (Set.range (fun k : κ => A.col k))) := by
    rw [← A.rank_eq_finrank_span_cols, hrank]
  obtain ⟨c, hc⟩ := exists_indep_family_of_finrank (fun k : κ => A.col k) d hspan
  have cinj : Function.Injective c := by
    intro i j hij
    apply hc.injective
    simp [hij]
  refine ⟨⟨c, cinj⟩, ?_⟩
  let B : Matrix (Fin d) (Fin d) F := Matrix.of fun i j => g i (c j)
  have hcols : LinearIndependent F (fun j => B.col j) := by
    change LinearIndependent F (fun j i => g i (c j))
    have heq : (fun j => A.col (c j)) = (fun j i => g i (c j)) := by
      funext j i
      rfl
    rw [← heq]
    exact hc
  have hu : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (B.isUnit_iff_isUnit_det.mp hu).ne_zero

/-- **Near-unimodularity bound.**  A square integer matrix whose rows all have entries in
`{-1, 0, 1}` with at most one `+1` and at most one `-1` has determinant `0` or `±1`. -/
theorem det_natAbs_le_one : ∀ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ),
    (∀ r, NearUni (A r)) → A.det.natAbs ≤ 1 := by
  intro N
  induction N with
  | zero =>
    intro A _
    rw [Matrix.det_fin_zero]
    exact le_refl 1
  | succ N ih =>
    intro A hA
    by_cases hall : ∀ r, (∃ c, A r c = 1) ∧ ∃ c, A r c = -1
    · -- every row has both a `+1` and a `-1`: all row sums vanish, so `det = 0`
      have hdet : A.det = 0 := by
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), ?_⟩
        funext r
        obtain ⟨⟨cp, hcp⟩, cm, hcm⟩ := hall r
        have hcpm : cp ≠ cm := by
          intro h
          rw [h, hcm] at hcp
          norm_num at hcp
        have hzero : ∀ c ∈ (Finset.univ : Finset (Fin (N + 1))),
            c ∉ ({cp, cm} : Finset (Fin (N + 1))) → A r c * 1 = 0 := by
          intro c _ hc
          have hccp : c ≠ cp := fun h => hc (by simp [h])
          have hccm : c ≠ cm := fun h => hc (by simp [h])
          rcases (hA r).1 c with h1 | h1 | h1
          · exact absurd ((hA r).2.1 c cp h1 hcp) hccp
          · rw [h1, zero_mul]
          · exact absurd ((hA r).2.2 c cm h1 hcm) hccm
        show ∑ c, A r c * 1 = 0
        rw [← Finset.sum_subset (Finset.subset_univ ({cp, cm} : Finset (Fin (N + 1)))) hzero,
          Finset.sum_pair hcpm, hcp, hcm]
        norm_num
      rw [hdet]
      norm_num
    · -- some row misses `+1` or misses `-1`: it has at most one nonzero entry
      rcases not_forall.mp hall with ⟨r₀, hr₀⟩
      have hone : ∀ c c', A r₀ c ≠ 0 → A r₀ c' ≠ 0 → c = c' := by
        intro c c' hc hc'
        rcases (hA r₀).1 c with h1 | h1 | h1
        · rcases (hA r₀).1 c' with h2 | h2 | h2
          · exact (hA r₀).2.1 c c' h1 h2
          · exact absurd h2 hc'
          · exact absurd ⟨⟨c, h1⟩, ⟨c', h2⟩⟩ hr₀
        · exact absurd h1 hc
        · rcases (hA r₀).1 c' with h2 | h2 | h2
          · exact absurd ⟨⟨c', h2⟩, ⟨c, h1⟩⟩ hr₀
          · exact absurd h2 hc'
          · exact (hA r₀).2.2 c c' h1 h2
      by_cases hex : ∃ c₀, A r₀ c₀ ≠ 0
      · -- expand along the almost-zero row `r₀`
        obtain ⟨c₀, hc₀⟩ := hex
        rw [Matrix.det_succ_row A r₀,
          Finset.sum_eq_single_of_mem c₀ (Finset.mem_univ c₀) ?_]
        · rw [Int.natAbs_mul, Int.natAbs_mul]
          have h1 : ((-1 : ℤ) ^ ((r₀ : ℕ) + (c₀ : ℕ))).natAbs = 1 := by
            rw [Int.natAbs_pow]
            norm_num
          have h2 : (A r₀ c₀).natAbs = 1 := by
            rcases (hA r₀).1 c₀ with h | h | h
            · rw [h]; rfl
            · exact absurd h hc₀
            · rw [h]; rfl
          have h3 : ((A.submatrix r₀.succAbove c₀.succAbove).det).natAbs ≤ 1 := by
            apply ih
            intro r'
            exact (hA (r₀.succAbove r')).comp Fin.succAbove_right_injective
          rw [h1, h2, one_mul, one_mul]
          exact h3
        · intro c _ hcne
          have hc : A r₀ c = 0 := by
            by_contra h
            exact hcne (hone c c₀ h hc₀)
          rw [hc, mul_zero, zero_mul]
      · -- the row is zero
        have hz : ∀ c, A r₀ c = 0 := by
          intro c
          by_contra h
          exact hex ⟨c, h⟩
        rw [Matrix.det_eq_zero_of_row_eq_zero r₀ hz]
        norm_num

end NearUnimodular

namespace MinimalNUS

variable {p n : ℕ}

/-- The rectangle determined by `X` and `Y`: unordered index pairs having one index in
`X` and the other in `Y`. -/
def rectangle (X Y : Finset (Fin n)) : Set (Sym2 (Fin n)) :=
  {t | ∃ i ∈ X, ∃ j ∈ Y, t = s(i, j)}

/-- The collision row of a rectangle pair splits as a sum of two near-unimodular parts,
one supported on each side. -/
theorem rho_eq_isub_add_isub (S : MinimalNUS p n) (P : S.Pairing) {i j i' j' : Fin n}
    (hEq : P.μ s(i, j) = s(i', j')) :
    S.rho P s(i, j) = fun k => isub i i' k + isub j j' k := by
  funext k
  simp only [rho, hEq, uvec_mk, Pi.sub_apply, Pi.add_apply, isub_apply, Pi.single_apply]
  ring

/-- Collision rows of rectangle pairs vanish outside the four endpoints. -/
theorem rho_apply_eq_zero (S : MinimalNUS p n) (P : S.Pairing) {i j i' j' k : Fin n}
    (hEq : P.μ s(i, j) = s(i', j')) (h1 : k ≠ i) (h2 : k ≠ j) (h3 : k ≠ i') (h4 : k ≠ j') :
    S.rho P s(i, j) k = 0 := by
  simp only [rho, hEq, uvec_mk, Pi.sub_apply, Pi.add_apply, Pi.single_apply,
    if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring

/-- A collision row inside an invariant disjoint rectangle has coordinate sum zero on
each of the two sides separately. -/
theorem sum_rho_rectangle_side_eq_zero (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y)
    (t : ↑(rectangle X Y)) :
    (∑ k ∈ X, S.rho P t.1 k = 0) ∧ (∑ k ∈ Y, S.rho P t.1 k = 0) := by
  classical
  obtain ⟨i, hi, j, hj, ht⟩ := t.2
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
  rw [ht]
  rw [rho_eq_isub_add_isub S P hEq]
  have hji : j ∉ X := fun h => Finset.disjoint_left.mp hXY h hj
  have hj'i : j' ∉ X := fun h => Finset.disjoint_left.mp hXY h hj'
  have hij : i ∉ Y := fun h => Finset.disjoint_left.mp hXY hi h
  have hi'j : i' ∉ Y := fun h => Finset.disjoint_left.mp hXY hi' h
  constructor
  · rw [Finset.sum_add_distrib, sum_isub_eq_zero X hi hi']
    simp [isub, hji, hj'i]
  · rw [Finset.sum_add_distrib, sum_isub_eq_zero Y hj hj']
    simp [isub, hij, hi'j]

/-- A rectangle collision row has Euclidean norm at most `2`. -/
theorem sum_sq_rho_rectangle_le_four (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y)
    (t : ↑(rectangle X Y)) :
    ∑ k, (((S.rho P t.1 k : ℤ) : ℝ) ^ 2) ≤ 4 := by
  classical
  obtain ⟨i, hi, j, hj, ht⟩ := t.2
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
  rw [ht, rho_eq_isub_add_isub S P hEq]
  have hcross : ∀ k, (isub i i' k : ℝ) * (isub j j' k : ℝ) = 0 := by
    intro k
    by_cases hx : isub i i' k = 0
    · simp [hx]
    by_cases hy : isub j j' k = 0
    · simp [hy]
    obtain hik | hik := isub_ne_zero_support hx
    <;> obtain hjk | hjk := isub_ne_zero_support hy
    all_goals
      have hkX : k ∈ X := by first | simpa [hik] using hi | simpa [hik] using hi'
      have hkY : k ∈ Y := by first | simpa [hjk] using hj | simpa [hjk] using hj'
      exact (Finset.disjoint_left.mp hXY hkX hkY).elim
  calc
    ∑ k, (((isub i i' k + isub j j' k : ℤ) : ℝ) ^ 2) =
        (∑ k, (((isub i i' k : ℤ) : ℝ) ^ 2)) +
          ∑ k, (((isub j j' k : ℤ) : ℝ) ^ 2) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            push_cast
            rw [add_sq]
            nlinarith [hcross k]
    _ ≤ 2 + 2 := add_le_add (sum_sq_isub_le_two i i') (sum_sq_isub_le_two j j')
    _ = 4 := by norm_num

/-- For a vector supported inside `U`, the dot product computed over the coordinates in `U`
agrees with the full dot product. -/
theorem sum_subtype_mul_eq_dot {R : Type*} [CommRing R] {U : Finset (Fin n)} {v : Fin n → ℤ}
    (hsupp : ∀ k, k ∉ U → v k = 0) (w : Fin n → R) :
    ∑ k : ↥U, w k.1 * ((v k.1 : ℤ) : R) = (fun k => ((v k : ℤ) : R)) ⬝ᵥ w := by
  rw [Finset.sum_coe_sort U (fun k => w k * ((v k : ℤ) : R)), dotProduct_comm]
  simp only [dotProduct]
  exact Finset.sum_subset (Finset.subset_univ U) fun k _ hk => by rw [hsupp k hk]; norm_num

/-- A `μ`-invariant rectangle has at least three vertices: a `1 × 1` rectangle would force
`μ` to fix its unique pair. -/
theorem three_le_of_invariant (S : MinimalNUS p n) (P : S.Pairing) {X' Y' : Finset (Fin n)}
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') :
    3 ≤ X'.card + Y'.card := by
  by_contra hlt
  have hx := Finset.card_pos.mpr hX'
  have hy := Finset.card_pos.mpr hY'
  have hx1 : X'.card = 1 := by omega
  have hy1 : Y'.card = 1 := by omega
  obtain ⟨i₀, hX0⟩ := Finset.card_eq_one.mp hx1
  obtain ⟨j₀, hY0⟩ := Finset.card_eq_one.mp hy1
  obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i₀, j₀) ⟨i₀, by simp [hX0], j₀, by simp [hY0], rfl⟩
  rw [hX0, Finset.mem_singleton] at hi'
  rw [hY0, Finset.mem_singleton] at hj'
  exact P.ne s(i₀, j₀) (by rw [hEq, hi', hj'])

/-- Every invariant rectangle contains one minimal under taking nonempty invariant
subrectangles. -/
theorem exists_minimal_rectangle (S : MinimalNUS p n) (P : S.Pairing)
    {X Y : Finset (Fin n)} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y) :
    ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ X'.Nonempty ∧ Y'.Nonempty ∧
      (∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') ∧
      ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
        (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') →
        X'' = X' ∧ Y'' = Y' := by
  classical
  let Good : ℕ → Prop := fun k => ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧
    X'.Nonempty ∧ Y'.Nonempty ∧
    (∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y') ∧
    X'.card + Y'.card = k
  have hex : ∃ k, Good k := ⟨X.card + Y.card, X, Y, Subset.rfl, Subset.rfl,
    hX, hY, hinv, rfl⟩
  let k₀ := Nat.find hex
  obtain ⟨X', Y', hXsub, hYsub, hXne, hYne, hinv', hcard⟩ := Nat.find_spec hex
  refine ⟨X', Y', hXsub, hYsub, hXne, hYne, hinv', ?_⟩
  intro X'' Y'' hXX hYY hX'' hY'' hinv''
  have hgood : Good (X''.card + Y''.card) :=
    ⟨X'', Y'', hXX.trans hXsub, hYY.trans hYsub, hX'', hY'', hinv'', rfl⟩
  have hmincard : k₀ ≤ X''.card + Y''.card := Nat.find_min' hex hgood
  have hleX := Finset.card_le_card hXX
  have hleY := Finset.card_le_card hYY
  dsimp only [k₀] at hmincard
  have hsum : X''.card + Y''.card = X'.card + Y'.card := by
    omega
  have heqX : X''.card = X'.card := by omega
  have heqY : Y''.card = Y'.card := by omega
  exact ⟨Finset.eq_of_subset_of_card_le hXX heqX.ge,
    Finset.eq_of_subset_of_card_le hYY heqY.ge⟩

/-- **The argmax step.**  On a *minimal* invariant rectangle, a rational vector whose pair
sums are `μ`-invariant over the rectangle is constant on each side: the argmax sets on the
two sides span an invariant sub-rectangle, which by minimality is everything. -/
theorem const_on_sides (S : MinimalNUS p n) (P : S.Pairing) {X' Y' : Finset (Fin n)}
    (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y')
    (hmin : ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
      (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') → X'' = X' ∧ Y'' = Y')
    (W : Fin n → ℚ)
    (hW : ∀ i ∈ X', ∀ j ∈ Y', pairSum W (P.μ s(i, j)) = pairSum W s(i, j)) :
    (∀ i₁ ∈ X', ∀ i₂ ∈ X', W i₁ = W i₂) ∧ ∀ j₁ ∈ Y', ∀ j₂ ∈ Y', W j₁ = W j₂ := by
  classical
  have hXimg : (X'.image W).Nonempty := hX'.image W
  have hYimg : (Y'.image W).Nonempty := hY'.image W
  set mX := (X'.image W).max' hXimg with hmX
  set mY := (Y'.image W).max' hYimg with hmY
  have hleX : ∀ i ∈ X', W i ≤ mX := fun i hi =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem W hi)
  have hleY : ∀ j ∈ Y', W j ≤ mY := fun j hj =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem W hj)
  set A := X'.filter (fun k => W k = mX) with hA
  set B := Y'.filter (fun k => W k = mY) with hB
  have hAsub : A ⊆ X' := Finset.filter_subset _ _
  have hBsub : B ⊆ Y' := Finset.filter_subset _ _
  have hAne : A.Nonempty := by
    obtain ⟨i, hi, hWi⟩ := Finset.mem_image.mp ((X'.image W).max'_mem hXimg)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hWi⟩⟩
  have hBne : B.Nonempty := by
    obtain ⟨j, hj, hWj⟩ := Finset.mem_image.mp ((Y'.image W).max'_mem hYimg)
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hWj⟩⟩
  have hABinv : ∀ t ∈ rectangle A B, P.μ t ∈ rectangle A B := by
    rintro t ⟨i, hiA, j, hjB, rfl⟩
    have hiX : i ∈ X' := hAsub hiA
    have hjY : j ∈ Y' := hBsub hjB
    obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hiX, j, hjY, rfl⟩
    have hsum : W i' + W j' = W i + W j := by
      have h := hW i hiX j hjY
      rw [hEq, pairSum_mk, pairSum_mk] at h
      exact h
    have hWi : W i = mX := (Finset.mem_filter.mp hiA).2
    have hWj : W j = mY := (Finset.mem_filter.mp hjB).2
    have hWi' : W i' = mX := by
      have h1 := hleX i' hi'
      have h2 := hleY j' hj'
      rw [hWi, hWj] at hsum
      linarith
    have hWj' : W j' = mY := by
      rw [hWi, hWj, hWi'] at hsum
      linarith
    exact ⟨i', Finset.mem_filter.mpr ⟨hi', hWi'⟩, j', Finset.mem_filter.mpr ⟨hj', hWj'⟩, hEq⟩
  obtain ⟨hAX, hBY⟩ := hmin A B hAsub hBsub hAne hBne hABinv
  constructor
  · intro i₁ h₁ i₂ h₂
    have e₁ : W i₁ = mX := (Finset.mem_filter.mp (by rw [hAX]; exact h₁ : i₁ ∈ A)).2
    have e₂ : W i₂ = mX := (Finset.mem_filter.mp (by rw [hAX]; exact h₂ : i₂ ∈ A)).2
    rw [e₁, e₂]
  · intro j₁ h₁ j₂ h₂
    have e₁ : W j₁ = mY := (Finset.mem_filter.mp (by rw [hBY]; exact h₁ : j₁ ∈ B)).2
    have e₂ : W j₂ = mY := (Finset.mem_filter.mp (by rw [hBY]; exact h₂ : j₂ ∈ B)).2
    rw [e₁, e₂]

/-- On a minimal invariant rectangle, the restricted collision rows have rank at least
the number of vertices minus two. -/
theorem finrank_rectRows_ge (S : MinimalNUS p n) (P : S.Pairing)
    {X' Y' : Finset (Fin n)} (hX' : X'.Nonempty) (hY' : Y'.Nonempty)
    (hinv : ∀ t ∈ rectangle X' Y', P.μ t ∈ rectangle X' Y')
    (hmin : ∀ X'' Y'', X'' ⊆ X' → Y'' ⊆ Y' → X''.Nonempty → Y''.Nonempty →
      (∀ t ∈ rectangle X'' Y'', P.μ t ∈ rectangle X'' Y'') → X'' = X' ∧ Y'' = Y') :
    (X' ∪ Y').card - 2 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun t : ↑(rectangle X' Y') =>
        fun k : ↑(X' ∪ Y') => ((S.rho P t.1 k.1 : ℤ) : ℚ)))) := by
  classical
  let U := X' ∪ Y'
  let I := ↑(rectangle X' Y')
  let A : Matrix I ↑U ℚ := Matrix.of fun t k => ((S.rho P t.1 k.1 : ℤ) : ℚ)
  obtain ⟨ix, hix⟩ := hX'
  obtain ⟨iy, hiy⟩ := hY'
  have hkerle : Module.finrank ℚ (LinearMap.ker A.mulVecLin) ≤ 2 := by
    let ixU : ↑U := ⟨ix, Finset.mem_union_left _ hix⟩
    let iyU : ↑U := ⟨iy, Finset.mem_union_right _ hiy⟩
    let ev : LinearMap.ker A.mulVecLin →ₗ[ℚ] (Fin 2 → ℚ) :=
      { toFun := fun w => ![w.1 ixU, w.1 iyU]
        map_add' := by intro u v; funext j; fin_cases j <;> rfl
        map_smul' := by intro c w; funext j; fin_cases j <;> rfl }
    have hev : Function.Injective ev := by
      intro u v huv
      apply Subtype.ext
      funext k
      let W : Fin n → ℚ := fun z => if hz : z ∈ U then u.1 ⟨z, hz⟩ - v.1 ⟨z, hz⟩ else 0
      have horth : ∀ i ∈ X', ∀ j ∈ Y',
          pairSum W (P.μ s(i, j)) = pairSum W s(i, j) := by
        intro i hi j hj
        let t : I := ⟨s(i, j), i, hi, j, hj, rfl⟩
        obtain ⟨i', hi', j', hj', hEq⟩ := hinv s(i, j) ⟨i, hi, j, hj, rfl⟩
        have hsupp : ∀ z, z ∉ U → S.rho P s(i, j) z = 0 := by
          intro z hz
          apply rho_apply_eq_zero S P hEq
          · intro h; subst z; exact hz (Finset.mem_union_left _ hi)
          · intro h; subst z; exact hz (Finset.mem_union_right _ hj)
          · intro h; subst z; exact hz (Finset.mem_union_left _ hi')
          · intro h; subst z; exact hz (Finset.mem_union_right _ hj')
        have hu0 : ∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z = 0 := by
          have hz := congrFun (LinearMap.mem_ker.mp u.2) t
          change (∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z) = 0 at hz
          exact hz
        have hv0 : ∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z = 0 := by
          have hz := congrFun (LinearMap.mem_ker.mp v.2) t
          change (∑ z : ↑U, ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z) = 0 at hz
          exact hz
        have hdot : (fun z => ((S.rho P s(i, j) z : ℤ) : ℚ)) ⬝ᵥ W = 0 := by
          rw [← sum_subtype_mul_eq_dot hsupp W]
          calc ∑ z : ↑U, W z.1 * ((S.rho P s(i, j) z.1 : ℤ) : ℚ)
              = ∑ z : ↑U, (((S.rho P s(i, j) z.1 : ℤ) : ℚ) * u.1 z -
                  ((S.rho P s(i, j) z.1 : ℤ) : ℚ) * v.1 z) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    simp only [W, dif_pos z.2]
                    ring
            _ = 0 := by rw [Finset.sum_sub_distrib, hu0, hv0, sub_self]
        rw [S.rho_cast_dot P s(i, j), sub_eq_zero] at hdot
        exact hdot.symm
      have hc := const_on_sides S P ⟨ix, hix⟩ ⟨iy, hiy⟩ hinv hmin W horth
      have huv0 : ev u = ev v := huv
      have hx0 : u.1 ixU = v.1 ixU := by
        have := congrFun huv0 0
        simpa [ev] using this
      have hy0 : u.1 iyU = v.1 iyU := by
        have := congrFun huv0 1
        simpa [ev] using this
      have hkU : k.1 ∈ U := k.2
      rcases Finset.mem_union.mp hkU with hkX | hkY
      · have hh := hc.1 k.1 hkX ix hix
        have hWk : W k.1 = u.1 k - v.1 k := by simp [W, k.2]
        have hWix : W ix = u.1 ixU - v.1 ixU := by
          have hixU : ix ∈ U := Finset.mem_union_left Y' hix
          have heq : (⟨ix, hixU⟩ : ↑U) = ixU := Subtype.ext (by rfl)
          rw [show W ix = u.1 ⟨ix, hixU⟩ - v.1 ⟨ix, hixU⟩ by
            simp only [W, dif_pos hixU], heq]
        rw [hWk, hWix] at hh
        exact sub_eq_zero.mp (hh.trans (sub_eq_zero.mpr hx0))
      · have hh := hc.2 k.1 hkY iy hiy
        have hWk : W k.1 = u.1 k - v.1 k := by simp [W, k.2]
        have hWiy : W iy = u.1 iyU - v.1 iyU := by
          have hiyU : iy ∈ U := Finset.mem_union_right X' hiy
          have heq : (⟨iy, hiyU⟩ : ↑U) = iyU := Subtype.ext (by rfl)
          rw [show W iy = u.1 ⟨iy, hiyU⟩ - v.1 ⟨iy, hiyU⟩ by
            simp only [W, dif_pos hiyU], heq]
        rw [hWk, hWiy] at hh
        exact sub_eq_zero.mp (hh.trans (sub_eq_zero.mpr hy0))
    have hr := LinearMap.finrank_le_finrank_of_injective hev
    simpa [Module.finrank_pi] using hr
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdomain : Module.finrank ℚ (↑U → ℚ) = U.card := by simp
  rw [hdomain] at hrn
  have hrange : U.card - 2 ≤ Module.finrank ℚ (LinearMap.range A.mulVecLin) := by omega
  have hrank : A.rank = Module.finrank ℚ (LinearMap.range A.mulVecLin) := rfl
  rw [← hrank, A.rank_eq_finrank_span_row] at hrange
  change (X' ∪ Y').card - 2 ≤ Module.finrank ℚ
    (Submodule.span ℚ (Set.range (fun t : ↑(rectangle X' Y') =>
      fun k : ↑(X' ∪ Y') => ((S.rho P t.1 k.1 : ℤ) : ℚ)))) at hrange
  exact hrange

/-- **Lemma 2.1 (Clean rectangle).**  If `μ` maps the rectangle `X × Y` into itself,
then `p ≤ 2^(|X|+|Y|−2)`, i.e. `|X| + |Y| ≥ log₂ p + 2`. -/
theorem clean_rectangle [Fact p.Prime] (S : MinimalNUS p n) (P : S.Pairing)
    (X Y : Finset (Fin n)) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hinv : ∀ t ∈ rectangle X Y, P.μ t ∈ rectangle X Y) :
    p ≤ 2 ^ (X.card + Y.card - 2) := by
  classical
  obtain ⟨X', Y', hXsub, hYsub, hX', hY', hinv', hmin⟩ :=
    exists_minimal_rectangle S P hX hY hinv
  have hXY' : Disjoint X' Y' := hXY.mono hXsub hYsub
  let U := X' ∪ Y'
  let d := U.card - 2
  have hUcard : U.card = X'.card + Y'.card := by
    simpa [U] using Finset.card_union_of_disjoint hXY'
  have hthree : 3 ≤ U.card := by
    rw [hUcard]
    exact three_le_of_invariant S P hX' hY' hinv'
  let rowQ : ↑(rectangle X' Y') → (↑U → ℚ) := fun t k =>
    ((S.rho P t.1 k.1 : ℤ) : ℚ)
  have hrank := finrank_rectRows_ge S P hX' hY' hinv' hmin
  change d ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range rowQ)) at hrank
  obtain ⟨r, hr⟩ := exists_indep_family_of_finrank rowQ d hrank
  obtain ⟨c, hc⟩ := exists_coordinate_minor (fun i => rowQ (r i)) hr
  let B : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => S.rho P (r i).1 (c j).1
  have hBne : B.det ≠ 0 := by
    intro hzero
    have hcast : (B.map (fun z : ℤ => (z : ℚ))).det = 0 := by
      rw [← Int.cast_det, hzero]
      norm_num
    apply hc
    change (B.map (fun z : ℤ => (z : ℚ))).det = 0
    exact hcast
  have hpdiv : (p : ℤ) ∣ B.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    let R : Matrix (Fin d) ↑U (ZMod p) := Matrix.of fun i k =>
      ((S.rho P (r i).1 k.1 : ℤ) : ZMod p)
    let K : Matrix ↑U (Fin 3) (ZMod p) := Matrix.of fun k q =>
      if q = 0 then if k.1 ∈ X' then 1 else 0
      else if q = 1 then if k.1 ∈ Y' then 1 else 0
      else S.a k.1
    obtain ⟨ix, hix⟩ := hX'
    obtain ⟨iy, hiy⟩ := hY'
    have hixY : ix ∉ Y' := fun h => Finset.disjoint_left.mp hXY' hix h
    have hiyX : iy ∉ X' := fun h => Finset.disjoint_left.mp hXY' h hiy
    have hextra : ∃ z, (z ∈ X' ∧ z ≠ ix) ∨ (z ∈ Y' ∧ z ≠ iy) := by
      by_contra h
      push Not at h
      have hxle : X'.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (h a).1 ha |>.trans ((h b).1 hb).symm
      have hyle : Y'.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (h a).2 ha |>.trans ((h b).2 hb).symm
      rw [hUcard] at hthree
      omega
    obtain ⟨z, hz⟩ := hextra
    have hKli : LinearIndependent (ZMod p) (fun q => K.col q) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have ex := congrFun hg ⟨ix, Finset.mem_union_left Y' hix⟩
      have ey := congrFun hg ⟨iy, Finset.mem_union_right X' hiy⟩
      simp [K, hix, hixY, hiy, hiyX, Fin.sum_univ_succ] at ex ey
      have eg : g 2 = 0 := by
        rcases hz with ⟨hz, hzne⟩ | ⟨hz, hzne⟩
        · have ez := congrFun hg ⟨z, Finset.mem_union_left Y' hz⟩
          have hznot : z ∉ Y' := fun h => Finset.disjoint_left.mp hXY' hz h
          simp [K, hz, hznot, Fin.sum_univ_succ] at ez
          have hm : g 2 * (S.a z - S.a ix) = 0 := by
            linear_combination ez - ex
          rcases mul_eq_zero.mp hm with h0 | h0
          · exact h0
          · exact absurd (sub_eq_zero.mp h0) (fun e => hzne (S.a.injective e))
        · have ez := congrFun hg ⟨z, Finset.mem_union_right X' hz⟩
          have hznot : z ∉ X' := fun h => Finset.disjoint_left.mp hXY' h hz
          simp [K, hz, hznot, Fin.sum_univ_succ] at ez
          have hm : g 2 * (S.a z - S.a iy) = 0 := by
            linear_combination ez - ey
          rcases mul_eq_zero.mp hm with h0 | h0
          · exact h0
          · exact absurd (sub_eq_zero.mp h0) (fun e => hzne (S.a.injective e))
      have e0 : g 0 = 0 := by simpa [eg] using ex
      have e1 : g 1 = 0 := by simpa [eg] using ey
      intro q
      fin_cases q <;> assumption
    have hKrank : K.rank = 3 := by
      have h := hKli.rank_matrix
      simpa using h
    have hRK : R * K = 0 := by
      ext i q
      rw [Matrix.mul_apply]
      have hsupp : ∀ k, k ∉ U → S.rho P (r i).1 k = 0 := by
        intro k hk
        obtain ⟨a, ha, b, hb, ht⟩ := (r i).2
        obtain ⟨a', ha', b', hb', hEq⟩ := hinv' s(a, b) ⟨a, ha, b, hb, rfl⟩
        rw [ht]
        apply rho_apply_eq_zero S P hEq
        · intro e; subst k; exact hk (Finset.mem_union_left _ ha)
        · intro e; subst k; exact hk (Finset.mem_union_right _ hb)
        · intro e; subst k; exact hk (Finset.mem_union_left _ ha')
        · intro e; subst k; exact hk (Finset.mem_union_right _ hb')
      fin_cases q
      · have hs := (sum_rho_rectangle_side_eq_zero S P hXY' hinv' (r i)).1
        change ∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
          (if k.1 ∈ X' then 1 else 0) = 0
        rw [show (∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
            (if k.1 ∈ X' then 1 else 0)) =
            (∑ k : Fin n, ((S.rho P (r i).1 k : ℤ) : ZMod p) *
              (if k ∈ X' then 1 else 0)) by
              simpa [mul_comm, dotProduct] using sum_subtype_mul_eq_dot (R := ZMod p) hsupp
                (fun k => if k ∈ X' then 1 else 0)]
        rw [← Finset.sum_subset (Finset.subset_univ X')]
        · simpa using congrArg (fun z : ℤ => (z : ZMod p)) hs
        · intro k _ hk
          simp [hk]
      · have hs := (sum_rho_rectangle_side_eq_zero S P hXY' hinv' (r i)).2
        change ∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
          (if k.1 ∈ Y' then 1 else 0) = 0
        rw [show (∑ k : ↑U, ((S.rho P (r i).1 k.1 : ℤ) : ZMod p) *
            (if k.1 ∈ Y' then 1 else 0)) =
            (∑ k : Fin n, ((S.rho P (r i).1 k : ℤ) : ZMod p) *
              (if k ∈ Y' then 1 else 0)) by
              simpa [mul_comm, dotProduct] using sum_subtype_mul_eq_dot (R := ZMod p) hsupp
                (fun k => if k ∈ Y' then 1 else 0)]
        rw [← Finset.sum_subset (Finset.subset_univ Y')]
        · simpa using congrArg (fun z : ℤ => (z : ZMod p)) hs
        · intro k _ hk
          simp [hk]
      ·
        have hdot := S.rho_cast_dot_a P (r i).1
        rw [← sum_subtype_mul_eq_dot hsupp (fun k => S.a k)] at hdot
        simpa [R, K, mul_comm] using hdot
    have hranksum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hRK
    rw [hKrank] at hranksum
    have hRrank : R.rank ≤ d - 1 := by
      have hdU : d = U.card - 2 := rfl
      rw [Fintype.card_coe] at hranksum
      omega
    by_contra hdet
    let BM : Matrix (Fin d) (Fin d) (ZMod p) := B.map (fun z : ℤ => (z : ZMod p))
    have hdetM : BM.det ≠ 0 := by
      rw [← Int.cast_det]
      exact hdet
    have hsmallLI : LinearIndependent (ZMod p)
        (fun i => BM.row i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero hdetM
    have hfullLI : LinearIndependent (ZMod p) (fun i => R.row i) := by
      rw [Fintype.linearIndependent_iff] at hsmallLI ⊢
      intro g hg
      apply hsmallLI g
      funext j
      have e := congrFun hg (c j)
      simpa [R, BM, B] using e
    have hfullrank : R.rank = d := by
      have h := hfullLI.rank_matrix
      simpa using h
    omega
  have hBbound : B.det.natAbs ≤ 2 ^ d := by
    let BR : Matrix (Fin d) (Fin d) ℝ := B.map (fun z : ℤ => (z : ℝ))
    have hrow : ∀ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤ 2 := by
      intro i
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
      constructor
      · norm_num
      have hsel : ∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2) ≤
          ∑ k : Fin n, (((S.rho P (r i).1 k : ℤ) : ℝ) ^ 2) := by
        let emb : Fin d ↪ Fin n := c.trans ⟨Subtype.val, Subtype.val_injective⟩
        rw [show (∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2)) =
            ∑ k ∈ Finset.univ.map emb,
              (((S.rho P (r i).1 k : ℤ) : ℝ) ^ 2) by
              rw [Finset.sum_map]
              rfl]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => sq_nonneg _)
      have hfour := sum_sq_rho_rectangle_le_four S P hXY' hinv' (r i)
      simp only [Real.norm_eq_abs, sq_abs]
      dsimp only [BR, Matrix.map_apply]
      change (∑ j : Fin d, (((B i j : ℤ) : ℝ) ^ 2)) ≤ 2 ^ 2
      rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
      change @LE.le ℝ Real.instPreorder.toLE
        (∑ j : Fin d, (((S.rho P (r i).1 (c j).1 : ℤ) : ℝ) ^ 2)) 4
      exact hsel.trans hfour
    have hhad := abs_det_le_prod_euclidean_row_norm BR
    have hprod : ∏ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤
        (2 : ℝ) ^ d := by
      calc
        ∏ i, ‖(WithLp.toLp 2 (BR i) : EuclideanSpace ℝ (Fin d))‖ ≤ ∏ _ : Fin d, (2 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hrow i)
        _ = (2 : ℝ) ^ d := by simp
    have hreal : |(B.det : ℝ)| ≤ (2 : ℝ) ^ d := by
      rw [Int.cast_det]
      exact hhad.trans hprod
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact_mod_cast hreal
  have hpB : p ≤ B.det.natAbs := by
    obtain ⟨q, hq⟩ := hpdiv
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hq
      exact hBne hq
    rw [hq, Int.natAbs_mul]
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hq1 : 1 ≤ q.natAbs := (Int.natAbs_pos.mpr hq0).nat_succ_le
    simpa using Nat.mul_le_mul_left p hq1
  calc
    p ≤ B.det.natAbs := hpB
    _ ≤ 2 ^ d := hBbound
    _ ≤ 2 ^ (X.card + Y.card - 2) := by
      apply Nat.pow_le_pow_right (by omega)
      dsimp [d, U]
      have hx := Finset.card_le_card hXsub
      have hy := Finset.card_le_card hYsub
      rw [Finset.card_union_of_disjoint hXY']
      omega

end MinimalNUS

end NUS
