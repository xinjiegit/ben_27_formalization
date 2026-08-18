/-
# Section 5: the determinant bridge

From the compression proposition (Proposition 4.1, `NUS.compression`) to the key
inequality `log p ≤ C (√n + n / log p) log n` of Theorem 1.2.

The argument: the compressed subgroup `Q ≤ Λ` has corank `K`; stacking a `ℤ`-basis of
`Q` (rank `n − K`) with `K − 1` well-chosen collision rows produces an `(n−1)`-row
integer matrix with rows in the collision lattice `Λ`.  In the coordinates given by a
basis of `Q` together with a section of `ℤⁿ → ℤⁿ/Q`, this matrix becomes block
triangular with an identity block, so Lemma 1.3 (`p_dvd_det_mul`) forces `p` to divide
the corresponding `(K−1) × (K−1)` minor of the coefficient matrix `W` of the collision
rows in the quotient basis.  Choosing the collision rows with linearly independent
`W`-rows makes some such minor nonzero, whence `p ≤ (4 n^{C₀})^{K−1}` by the entrywise
`ℓ¹` bound on determinants; taking logarithms gives the key inequality.
-/
import NUSLean.Compression

namespace NUS

open Finset Matrix

/-! ### An entrywise `ℓ¹` bound for determinants -/

/-- The determinant is at most the product of the column `ℓ¹`-norms. -/
theorem abs_det_le_prod_col_l1 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    |A.det| ≤ ∏ c, ∑ r, |A r c| := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have habs : ∀ σ : Equiv.Perm (Fin N),
      |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = ∏ i, |A (σ i) i| := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, Units.smul_def, Finset.abs_prod]
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin N) => (⇑σ : Fin N → Fin N)) :=
    fun σ τ h => Equiv.coe_fn_injective h
  calc ∑ σ : Equiv.Perm (Fin N), |Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      = ∑ σ : Equiv.Perm (Fin N), ∏ i, |A (σ i) i| :=
        Finset.sum_congr rfl fun σ _ => habs σ
    _ = ∑ f ∈ Finset.univ.map ⟨_, hinj⟩, ∏ i, |A (f i) i| :=
        (Finset.sum_map Finset.univ ⟨_, hinj⟩ (fun g => ∏ i, |A (g i) i|)).symm
    _ ≤ ∑ f : Fin N → Fin N, ∏ i, |A (f i) i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = ∏ i, ∑ r, |A r i| := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Determinant `ℓ¹` bound.**  The determinant of an integer matrix is at most the
product of the `ℓ¹`-norms of its rows. -/
theorem abs_det_le_prod_row_l1 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    |A.det| ≤ ∏ r, ∑ c, |A r c| := by
  have h := abs_det_le_prod_col_l1 Aᵀ
  rw [Matrix.det_transpose] at h
  simpa using h

/-! ### Small linear-algebra helpers -/

/-- A `ℤ`-linear functional on `ℤⁿ` is determined by its values on the coordinate
vectors. -/
theorem lin_pi_decomp {n : ℕ} (ℓ : (Fin n → ℤ) →ₗ[ℤ] ℤ) (w : Fin n → ℤ) :
    ℓ w = ∑ i, w i * ℓ (Pi.single i 1) := by
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin n → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ℓ.map_smul, smul_eq_mul]

/-- Every element of the collision lattice has coordinate sum zero. -/
theorem MinimalNUS.sum_eq_zero_of_mem_colLat {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) {w : Fin n → ℤ} (hw : w ∈ S.colLat P) : ∑ k, w k = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, rfl⟩ := hw
    have h := S.rho_cast_dot_one (R := ℤ) P t
    simpa [dotProduct] using h
  | zero => simp
  | add u v _ _ hu hv => simp [Finset.sum_add_distrib, hu, hv]
  | smul c u _ hu =>
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hu, mul_zero]

/-- From a spanning family whose span has dimension at least `d`, one can select `d`
members forming a linearly independent family. -/
theorem exists_indep_family {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
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

/-- A `m × (m+1)` matrix with linearly independent rows has a nonvanishing maximal
minor obtained by deleting a single column. -/
theorem exists_succAbove_det_ne_zero {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin m) (Fin (m + 1)) F) (hA : LinearIndependent F (fun i => A i)) :
    ∃ c : Fin (m + 1), (A.submatrix id c.succAbove).det ≠ 0 := by
  classical
  -- rank–nullity: the kernel of `x ↦ A *ᵥ x` is one-dimensional
  have hrank : A.rank = m := by
    have h := hA.rank_matrix
    simpa using h
  have hker : Module.finrank F (LinearMap.ker A.mulVecLin) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi] at hrn
    rw [Matrix.rank] at hrank
    simp only [Fintype.card_fin] at hrn
    omega
  let z' := Module.finBasisOfFinrankEq F (LinearMap.ker A.mulVecLin) hker
  have hz0 : ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) ≠ 0 := by
    intro h
    exact z'.ne_zero 0 (Subtype.ext h)
  obtain ⟨c, hc⟩ : ∃ c, ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) c ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (funext h)
  refine ⟨c, fun hdet => ?_⟩
  obtain ⟨v, hv0, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set w : Fin (m + 1) → F := c.insertNth 0 v with hwdef
  have hw : A *ᵥ w = 0 := by
    funext j
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succAbove (fun k => A j k * w k) c]
    have hzero : w c = 0 := by rw [hwdef]; exact Fin.insertNth_apply_same (α := fun _ => F) c 0 v
    have hrest : ∀ j' : Fin m, w (c.succAbove j') = v j' := by
      intro j'
      rw [hwdef]
      exact Fin.insertNth_apply_succAbove (α := fun _ => F) c 0 v j'
    rw [hzero, mul_zero, zero_add]
    have := congrFun hvz j
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.submatrix_apply, id_eq] at this
    simp only [hrest]
    exact this
  have hwker : w ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hw
  -- the kernel is spanned by `z' 0`, and `w` vanishes at `c` while `z' 0` does not
  set q : LinearMap.ker A.mulVecLin := ⟨w, hwker⟩ with hqdef
  have hq : q = z'.repr q 0 • z' 0 := by
    conv_lhs => rw [← z'.sum_repr q]
    rw [Fin.sum_univ_one]
  have hwc : w c = z'.repr q 0 * ((z' 0 : LinearMap.ker A.mulVecLin) : Fin (m + 1) → F) c := by
    have := congrArg (fun x : LinearMap.ker A.mulVecLin => (x : Fin (m + 1) → F) c) hq
    simpa using this
  have hzc : w c = 0 := by rw [hwdef]; exact Fin.insertNth_apply_same (α := fun _ => F) c 0 v
  have hcoeff : z'.repr q 0 = 0 := by
    rw [hzc] at hwc
    rcases mul_eq_zero.mp hwc.symm with h | h
    · exact h
    · exact absurd h hc
  have hqzero : q = 0 := by
    rw [hq, hcoeff, zero_smul]
  have hwzero : w = 0 := congrArg (fun x : LinearMap.ker A.mulVecLin => (x : Fin (m + 1) → F)) hqzero
  apply hv0
  funext j'
  have h1 := congrFun hwzero (c.succAbove j')
  rw [hwdef] at h1
  rw [Fin.insertNth_apply_succAbove] at h1
  simpa using h1

/-! ### The rank of the collision lattice and its compressed image -/

def castZQ {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v i := v i
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem castZQ_injective {n : ℕ} : Function.Injective (castZQ (n := n)) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change ((x i : ℤ) : ℚ) = ((y i : ℤ) : ℚ) at hi
  exact_mod_cast hi

theorem MinimalNUS.finrank_colLat {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : Module.finrank ℤ (S.colLat P) = n - 1 := by
  classical
  let f := (castZQ (n := n)).domRestrict (S.colLat P)
  have hf : Function.Injective f := castZQ_injective.comp Subtype.val_injective
  have hrange : f.range = Submodule.span ℤ (Set.range (S.rhoQ P)) := by
    rw [LinearMap.range_domRestrict, MinimalNUS.colLat, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨S.rho P t, ⟨t, rfl⟩, rfl⟩
  have heq := LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hf)
  rw [hrange] at heq
  letI : Module.Finite ℤ (Submodule.span ℤ (Set.range (S.rhoQ P))) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range _)
  calc
    Module.finrank ℤ (S.colLat P) =
        Module.finrank ℤ (Submodule.span ℤ (Set.range (S.rhoQ P))) := heq
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (S.rhoQ P))) :=
      (Submodule.finrank_span_eq_finrank_span ℤ ℚ _).symm
    _ = n - 1 := S.finrank_span_rhoQ P

theorem MinimalNUS.quotient_collision_rank {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) :
    Module.finrank ℤ (Submodule.span ℤ
      (Set.range fun t => Submodule.Quotient.mk (S.rho P t) :
        Set ((Fin n → ℤ) ⧸ Q))) = K - 1 := by
  classical
  let f := Q.mkQ.domRestrict (S.colLat P)
  have hker : f.ker = Submodule.comap (S.colLat P).subtype Q := by
    simp [f, LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have hkerrank : Module.finrank ℤ f.ker = Module.finrank ℤ Q := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hQ)
  have hrange : f.range = Submodule.span ℤ
      (Set.range fun t => Submodule.Quotient.mk (S.rho P t) :
        Set ((Fin n → ℤ) ⧸ Q)) := by
    rw [LinearMap.range_domRestrict, MinimalNUS.colLat, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨S.rho P t, ⟨t, rfl⟩, rfl⟩
  have hequiv := LinearEquiv.finrank_eq f.quotKerEquivRange
  rw [hrange] at hequiv
  have hsum := f.ker.finrank_quotient_add_finrank
  rw [hequiv, hkerrank, hQr, S.finrank_colLat P] at hsum
  have hambient := Q.finrank_quotient_add_finrank
  have hbfin : Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) = K := by
    simpa using Module.finrank_eq_card_basis b
  have hamb : Module.finrank ℤ (Fin n → ℤ) = n := by
    simpa using Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
  have hsumQ : K + (n - K) = n := by
    calc
      K + (n - K) = Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) +
          Module.finrank ℤ Q := by rw [hbfin, hQr]
      _ = Module.finrank ℤ (Fin n → ℤ) := hambient
      _ = n := hamb
  have hKn : K ≤ n := by omega
  have hn := S.two_le
  have hK1 : 1 ≤ K := by omega
  have hleft := hsum
  rw [Nat.add_comm] at hleft
  have hright : (n - K) + (K - 1) = n - 1 := by omega
  apply Nat.add_left_cancel (n := n - K)
  exact hleft.trans hright.symm

noncomputable def quotientCoordsZ {n K : ℕ} {Q : Submodule ℤ (Fin n → ℤ)}
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (x : (Fin n → ℤ) ⧸ Q) : Fin K → ℤ := fun k => b.repr x k

noncomputable def quotientCoordsQ {n K : ℕ} {Q : Submodule ℤ (Fin n → ℤ)}
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (x : (Fin n → ℤ) ⧸ Q) : Fin K → ℚ := fun k => b.repr x k

theorem MinimalNUS.quotientCoordsQ_collision_rank {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) = K - 1 := by
  classical
  let e := b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin K)
  have hmap : Submodule.map e.toLinearMap (Submodule.span ℤ
      (Set.range fun t => (Submodule.Quotient.mk (S.rho P t) :
        (Fin n → ℤ) ⧸ Q))) =
      Submodule.span ℤ (Set.range fun t =>
        quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t))) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Submodule.Quotient.mk (S.rho P t), ⟨t, rfl⟩, rfl⟩
  have he := LinearEquiv.finrank_map_eq e (Submodule.span ℤ
    (Set.range fun t => Submodule.Quotient.mk (S.rho P t)))
  rw [hmap, S.quotient_collision_rank P Q hQ hQr b] at he
  let f := (castZQ (n := K)).domRestrict (Submodule.span ℤ
    (Set.range fun t => quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t))))
  have hf : Function.Injective f := castZQ_injective.comp Subtype.val_injective
  have hfrange : f.range = Submodule.span ℤ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t))) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t)), ⟨t, rfl⟩, rfl⟩
  have hef := LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hf)
  rw [hfrange] at hef
  letI : Module.Finite ℤ (Submodule.span ℤ (Set.range fun t =>
      quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range _)
  calc
    Module.finrank ℚ (Submodule.span ℚ (Set.range fun t =>
        quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range fun t =>
        quotientCoordsQ b (Submodule.Quotient.mk (S.rho P t)))) :=
        Submodule.finrank_span_eq_finrank_span ℤ ℚ _
    _ = Module.finrank ℤ (Submodule.span ℤ (Set.range fun t =>
        quotientCoordsZ b (Submodule.Quotient.mk (S.rho P t)))) := hef.symm
    _ = K - 1 := he

/-- The nonzero core minor is still a maximal collision-lattice minor after adjoining
a basis of `Q`; hence it is divisible by `p`. -/
theorem MinimalNUS.p_dvd_quotient_minor {p n K : ℕ} [Fact p.Prime]
    (S : MinimalNUS p n) (P : S.Pairing)
    (Q : Submodule ℤ (Fin n → ℤ)) (hQ : Q ≤ S.colLat P)
    (hQr : Module.finrank ℤ Q = n - K)
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q))
    (hKn : K ≤ n) (hK1 : 1 ≤ K)
    (t : Fin (K - 1) → Sym2 (Fin n)) (c : Fin ((K - 1) + 1)) :
    (p : ℤ) ∣ (Matrix.of fun i j =>
      b.repr (Submodule.Quotient.mk (S.rho P (t i)))
        (finCongr (Nat.sub_add_cancel hK1) (c.succAbove j))).det := by
  classical
  let inc : Fin (K - 1) ↪ Fin K :=
    ⟨fun j => finCongr (Nat.sub_add_cancel hK1) (c.succAbove j),
      fun _ _ h => by simpa using h⟩
  let bQ := Module.finBasisOfFinrankEq ℤ Q hQr
  let e := Module.Basis.sumQuot bQ b
  let I := Fin (n - K) ⊕ Fin (K - 1)
  let rows : I → (Fin n → ℤ) := Sum.elim (fun i => bQ i) (fun j => S.rho P (t j))
  let cols : I → (Fin (n - K) ⊕ Fin K) := Sum.map id inc
  have hcard : Fintype.card (Fin (n - 1)) = Fintype.card I := by
    simp [I]
    omega
  let er : Fin (n - 1) ≃ I := Fintype.equivOfCardEq hcard
  let v : Fin (n - 1) → (Fin n → ℤ) := fun r => rows (er r)
  have hv : ∀ r, v r ∈ S.colLat P := by
    intro r
    change rows (er r) ∈ S.colLat P
    rcases hri : er r with i | j
    · change (bQ i : Fin n → ℤ) ∈ S.colLat P
      exact hQ (bQ i).2
    · change S.rho P (t j) ∈ S.colLat P
      exact Submodule.subset_span (Set.mem_range_self (t j))
  let U : Matrix (Fin n) (Fin (n - 1)) ℤ := fun a j =>
    e.repr (Pi.single a 1) (cols (er j))
  have hmul : Matrix.of v * U =
      (Matrix.of fun r s => e.repr (rows r) (cols s)).reindex er.symm er.symm := by
    ext r j
    simpa [Matrix.mul_apply, U, v, Matrix.reindex_apply] using
      (lin_pi_decomp (e.coord (cols (er j))) (rows (er r))).symm
  have hp := S.p_dvd_det_mul P v hv U
  rw [hmul, Matrix.det_reindex_self] at hp
  have hblock : (Matrix.of fun r s => e.repr (rows r) (cols s)) =
      Matrix.fromBlocks (1 : Matrix (Fin (n - K)) (Fin (n - K)) ℤ) 0
        (Matrix.of fun i j => e.repr (S.rho P (t i)) (Sum.inl j))
        (Matrix.of fun i j =>
          b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)) := by
    ext r s
    rcases r with i | i <;> rcases s with j | j
    · simp [e, rows, cols, bQ, Matrix.one_apply, Finsupp.single_apply]
    · simp [e, rows, cols, bQ]
    · simp [rows, cols]
    · exact Module.Basis.sumQuot_repr_inr bQ b (S.rho P (t i)) (inc j)
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul] at hp
  simpa [inc] using hp

theorem sum_abs_uvec_le_two {n : ℕ} (t : Sym2 (Fin n)) :
    ∑ i, |uvec t i| ≤ 2 := by
  classical
  induction t using Sym2.ind with
  | _ a b =>
    rw [uvec_mk]
    have ha : (∑ i, |(Pi.single a 1 : Fin n → ℤ) i|) = 1 := by
      simp only [Pi.single_apply, abs_ite, abs_one, abs_zero]
      have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) a
        (fun _ => (1 : ℤ))
      simpa only [Finset.mem_univ, if_true] using h
    have hb : (∑ i, |(Pi.single b 1 : Fin n → ℤ) i|) = 1 := by
      simp only [Pi.single_apply, abs_ite, abs_one, abs_zero]
      have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) b
        (fun _ => (1 : ℤ))
      simpa only [Finset.mem_univ, if_true] using h
    calc
      ∑ i, |((Pi.single a 1 : Fin n → ℤ) + (Pi.single b 1 : Fin n → ℤ)) i| ≤
          ∑ i, (|(Pi.single a 1 : Fin n → ℤ) i| +
            |(Pi.single b 1 : Fin n → ℤ) i|) :=
        Finset.sum_le_sum fun i _ => abs_add_le _ _
      _ = (∑ i, |(Pi.single a 1 : Fin n → ℤ) i|) +
          ∑ i, |(Pi.single b 1 : Fin n → ℤ) i| := Finset.sum_add_distrib
      _ = 2 := by rw [ha, hb]; norm_num

theorem MinimalNUS.sum_abs_rho_le_four {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (t : Sym2 (Fin n)) : ∑ i, |S.rho P t i| ≤ 4 := by
  have ht := sum_abs_uvec_le_two t
  have hmu := sum_abs_uvec_le_two (P.μ t)
  calc
    ∑ i, |S.rho P t i| ≤ ∑ i, (|uvec t i| + |uvec (P.μ t) i|) := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_sub _ _
    _ = (∑ i, |uvec t i|) + ∑ i, |uvec (P.μ t) i| := Finset.sum_add_distrib
    _ ≤ 4 := by omega

theorem MinimalNUS.core_rho_norm_le {p n K : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) (Q : Submodule ℤ (Fin n → ℤ))
    (b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q)) (M : ℤ) (hM : 0 ≤ M)
    (hb : ∀ i : Fin n,
      ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤ M)
    (t : Sym2 (Fin n)) :
    ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P t)) k| ≤ 4 * M := by
  classical
  have hdecomp : ∀ k, b.repr (Submodule.Quotient.mk (S.rho P t)) k =
      ∑ i, S.rho P t i * b.repr (Submodule.Quotient.mk (Pi.single i 1)) k := by
    intro k
    exact lin_pi_decomp ((b.coord k).comp Q.mkQ) (S.rho P t)
  calc
    ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P t)) k| =
        ∑ k, |∑ i, S.rho P t i *
          b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hdecomp]
    _ ≤ ∑ k, ∑ i, |S.rho P t i *
          b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |S.rho P t i| *
          (∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [abs_mul]
      rw [Finset.mul_sum]
    _ ≤ ∑ i, |S.rho P t i| * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = (∑ i, |S.rho P t i|) * M := by rw [Finset.sum_mul]
    _ ≤ 4 * M := mul_le_mul_of_nonneg_right (S.sum_abs_rho_le_four P t) hM

theorem key_inequality_proof :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (_ : S.Pairing),
        64 ≤ p →
        Real.log p ≤ C * (Real.sqrt n + n / Real.log p) * Real.log n := by
  classical
  obtain ⟨C₀, hC₀, hcomp⟩ := compression
  refine ⟨(C₀ : ℝ) * ((C₀ : ℝ) + 2), by positivity, ?_⟩
  intro p n hpFact S P hp64
  obtain ⟨K, Q, hQ, hprim, hQr, hKbound, b, hb⟩ := hcomp p n hpFact S P hp64
  have hn2 := S.two_le
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp64))
  have hM : (0 : ℤ) ≤ (n : ℤ) ^ C₀ := by positivity
  have hbfin : Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) = K := by
    simpa using Module.finrank_eq_card_basis b
  have hambient := Q.finrank_quotient_add_finrank
  have hamb : Module.finrank ℤ (Fin n → ℤ) = n := by
    simpa using Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
  have hsumQ : K + (n - K) = n := by
    calc
      K + (n - K) = Module.finrank ℤ ((Fin n → ℤ) ⧸ Q) + Module.finrank ℤ Q := by
        rw [hbfin, hQr]
      _ = Module.finrank ℤ (Fin n → ℤ) := hambient
      _ = n := hamb
  have hKn : K ≤ n := by omega
  have hrank := S.quotient_collision_rank P Q hQ hQr b
  have hK1 : 1 ≤ K := by
    have hcol := S.finrank_colLat P
    have hmono := Submodule.finrank_mono hQ
    rw [hQr, hcol] at hmono
    omega
  have hspan := S.quotientCoordsQ_collision_rank P Q hQ hQr b
  obtain ⟨t, ht⟩ := exists_indep_family
    (fun z => quotientCoordsQ b (Submodule.Quotient.mk (S.rho P z))) (K - 1)
      (by rw [hspan])
  let A : Matrix (Fin (K - 1)) (Fin K) ℚ := Matrix.of fun i =>
    quotientCoordsQ b (Submodule.Quotient.mk (S.rho P (t i)))
  have hA : LinearIndependent ℚ (fun i => A i) := ht
  let ek : Fin ((K - 1) + 1) ≃ Fin K := finCongr (Nat.sub_add_cancel hK1)
  let le : (Fin K → ℚ) ≃ₗ[ℚ] (Fin ((K - 1) + 1) → ℚ) :=
    (LinearEquiv.piCongrLeft ℚ (fun _ : Fin K => ℚ) ek).symm
  let A' : Matrix (Fin (K - 1)) (Fin ((K - 1) + 1)) ℚ := A.submatrix id ek
  have hA' : LinearIndependent ℚ (fun i => A' i) := by
    change LinearIndependent ℚ (fun i => le (A i))
    exact hA.map' le.toLinearMap (LinearMap.ker_eq_bot.mpr le.injective)
  let c0 := Classical.choose (exists_succAbove_det_ne_zero A' hA')
  have hc0 : (A'.submatrix id c0.succAbove).det ≠ 0 :=
    Classical.choose_spec (exists_succAbove_det_ne_zero A' hA')
  let inc : Fin (K - 1) ↪ Fin K :=
    ⟨fun j => ek (c0.succAbove j), fun _ _ h => by simpa [ek] using h⟩
  let D : Matrix (Fin (K - 1)) (Fin (K - 1)) ℤ := Matrix.of fun i j =>
    b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)
  have hcastD : D.map (Int.castRingHom ℚ) = A'.submatrix id c0.succAbove := by
    ext i j
    simp [D, A', A, inc, ek, quotientCoordsQ]
  have hD0 : D.det ≠ 0 := by
    intro h
    apply hc0
    calc
      (A'.submatrix id c0.succAbove).det = (D.map (Int.castRingHom ℚ)).det :=
        congrArg Matrix.det hcastD.symm
      _ = (D.det : ℚ) := by simpa using (Int.cast_det (R := ℚ) D).symm
      _ = 0 := by simp [h]
  have hpD : (p : ℤ) ∣ D.det := by
    have hp := S.p_dvd_quotient_minor P Q hQ hQr b hKn hK1 t c0
    simpa [D, inc, ek] using hp
  have hpabs : p ≤ Int.natAbs D.det := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpD hD0
  have hrow : ∀ i, ∑ j, |D i j| ≤ 4 * (n : ℤ) ^ C₀ := by
    intro i
    calc
      ∑ j, |D i j| =
          ∑ j, |b.repr (Submodule.Quotient.mk (S.rho P (t i))) (inc j)| := rfl
      _ = ∑ k ∈ Finset.univ.map inc,
          |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k| :=
        (Finset.sum_map Finset.univ inc fun k =>
          |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k|).symm
      _ ≤ ∑ k, |b.repr (Submodule.Quotient.mk (S.rho P (t i))) k| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => abs_nonneg _)
      _ ≤ 4 * (n : ℤ) ^ C₀ := S.core_rho_norm_le P Q b _ hM hb (t i)
  have hdet : |D.det| ≤ (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by
    calc
      |D.det| ≤ ∏ i, ∑ j, |D i j| := abs_det_le_prod_row_l1 D
      _ ≤ ∏ _ : Fin (K - 1), (4 * (n : ℤ) ^ C₀) := by
        exact Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hrow i)
      _ = (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by simp
  have hpPowNat : p ≤ (4 * n ^ C₀) ^ (K - 1) := by
    have habsNat : Int.natAbs D.det ≤ (4 * n ^ C₀) ^ (K - 1) := by
      have hz : (Int.natAbs D.det : ℤ) ≤ (4 * (n : ℤ) ^ C₀) ^ (K - 1) := by
        simpa using hdet
      exact_mod_cast hz
    exact hpabs.trans habsNat
  have hbase : (0 : ℝ) < 4 * n ^ C₀ := by positivity
  have hlogPow : Real.log p ≤ ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := by
    calc
      Real.log p ≤ Real.log ((4 * n ^ C₀) ^ (K - 1)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hpPowNat
      _ = ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := by
        rw [Real.log_pow]
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hlogbase : Real.log (4 * n ^ C₀) ≤ ((C₀ : ℝ) + 2) * Real.log n := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ C₀ ≠ 0), Real.log_pow]
    have hlog4 : Real.log 4 ≤ 2 * Real.log n := by
      have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2n
      calc
        Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        _ ≤ 2 * Real.log n := mul_le_mul_of_nonneg_left hh (by norm_num)
    nlinarith
  have hKreal : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have hfactor0 : 0 ≤ ((C₀ : ℝ) + 2) * Real.log n := by positivity
  calc
    Real.log p ≤ ((K - 1 : ℕ) : ℝ) * Real.log (4 * n ^ C₀) := hlogPow
    _ ≤ ((K - 1 : ℕ) : ℝ) * (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_left hlogbase (by positivity)
    _ ≤ (K : ℝ) * (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_right hKreal hfactor0
    _ ≤ ((C₀ : ℝ) * (Real.sqrt n + n / Real.log p)) *
        (((C₀ : ℝ) + 2) * Real.log n) :=
      mul_le_mul_of_nonneg_right hKbound hfactor0
    _ = (C₀ : ℝ) * ((C₀ : ℝ) + 2) *
        (Real.sqrt n + n / Real.log p) * Real.log n := by ring

end NUS
