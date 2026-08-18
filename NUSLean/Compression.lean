/-
# Integral contraction (Section 4, Proposition 4.1)

The compression proposition: an inclusion-minimal example admits a primitive subgroup
`Q ⊆ Λ` of corank `K = O(√n + n / log p)` such that `ℤⁿ/Q` is free of rank `K` and every
original coordinate has an `n^{O(1)}`-bounded representation in a suitable basis.

The paper's proof runs the round-based contraction: live blocks below weight
`L = ⌊log₂p/3⌋`, departing rows from Lemma 2.1 for every pair of light blocks, the
anchor classification (direct / easy / proper), the common cut of Lemma 3.1, the forest
contraction of Lemma 3.2, and the `M_{r+1} ≤ 60 M_r` coefficient-growth bookkeeping
over `O(log n)` rounds.  The formal proof below follows that construction.
-/
import NUSLean.CollisionLattice
import NUSLean.CleanRectangle
import NUSLean.CommonCut
import NUSLean.Contraction

namespace NUS

open MinimalNUS

/-- The uncompressed initial state: the zero subgroup is primitive, and its quotient
has the images of the standard coordinate vectors as a basis.  This is also the
terminal construction whenever the requested corank estimate already allows `K = n`. -/
theorem compression_bot_case (C p n : ℕ) (S : MinimalNUS p n) (P : S.Pairing)
    (hC : 0 < C)
    (hbound : (n : ℝ) ≤ C * (Real.sqrt n + n / Real.log p)) :
    ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
      Q ≤ S.colLat P ∧
      (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
      Module.finrank ℤ Q = n - K ∧
      ((K : ℝ) ≤ C * (Real.sqrt n + n / Real.log p)) ∧
      ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
        ∀ i : Fin n,
          ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤ (n : ℤ) ^ C := by
  classical
  refine ⟨n, ⊥, bot_le, ?_, by simp, hbound, ?_⟩
  · intro v c hc hcv
    simpa only [Submodule.mem_bot] using (smul_eq_zero.mp hcv).resolve_left hc
  · let e : (Fin n → ℤ) ≃ₗ[ℤ] ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
      LinearEquiv.ofBijective (⊥ : Submodule ℤ (Fin n → ℤ)).mkQ
        ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ],
          Submodule.mkQ_surjective _⟩
    let b := (Pi.basisFun ℤ (Fin n)).map e
    refine ⟨b, ?_⟩
    intro i
    have he : e.symm (Submodule.Quotient.mk (Pi.single i 1)) = Pi.single i 1 := by
      rw [e.symm_apply_eq]
      rfl
    have hsum : ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| = 1 := by
      simp only [b, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, he]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_apply, hji]
      · simp
    rw [hsum]
    have hn : (1 : ℤ) ≤ n := by exact_mod_cast S.two_le.trans' (by omega)
    exact one_le_pow₀ hn

/-- Two light blocks have a collision row which leaves their rectangle.  This is the
precise contrapositive of the clean-rectangle lemma used at the start of every round. -/
theorem exists_departing_pair {p n : ℕ} [Fact p.Prime] (S : MinimalNUS p n)
    (P : S.Pairing) (X Y : Finset (Fin n)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXY : Disjoint X Y) (hlight : 2 ^ (X.card + Y.card - 2) < p) :
    ∃ t ∈ MinimalNUS.rectangle X Y, P.μ t ∉ MinimalNUS.rectangle X Y := by
  by_contra h
  push Not at h
  have hinv : ∀ t ∈ MinimalNUS.rectangle X Y,
      P.μ t ∈ MinimalNUS.rectangle X Y := by
    intro t ht
    exact h t ht
  have hp := MinimalNUS.clean_rectangle S P X Y hX hY hXY hinv
  omega

/-! ### The abstract noncore part of a departing row -/

/-- The coefficient vector of the live part of (4.1).  Multiplicity in `ν` is
intentional: diagonal image pairs contribute twice to the same live coordinate. -/
def departingLive {V : Type*} [DecidableEq V] (i j : V) (ν : Multiset V) : V → ℤ :=
  Pi.single i 1 + Pi.single j 1 - fun v => (ν.count v : ℤ)

/-- A live coefficient vector is a unit relation when it is, up to sign, either one
coordinate or the difference of two coordinates. -/
def IsUnitRelation {V : Type*} [DecidableEq V] (w : V → ℤ) : Prop :=
  (∃ a, w = Pi.single a 1) ∨
  (∃ a b, a ≠ b ∧ w = Pi.single a 1 - Pi.single b 1) ∨
  (∃ a, w = -(Pi.single a 1)) ∨
  ∃ a b, a ≠ b ∧ w = -(Pi.single a 1 - Pi.single b 1)

/-- A unit relation taking value one at `i` can be oriented with `i` as its positive
endpoint. -/
theorem unitRelation_normalize_at_one {V : Type*} [DecidableEq V]
    {w : V → ℤ} (i : V) (hu : IsUnitRelation w) (hi : w i = 1) :
    w = Pi.single i 1 ∨
      ∃ b, b ≠ i ∧ w = Pi.single i 1 - Pi.single b 1 := by
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
  · have hai : a = i := by
      by_contra h
      have hv := congrFun ha i
      simp [Pi.single_apply, h] at hv hi
      omega
    subst a
    exact Or.inl ha
  · have hai : a = i := by
      by_contra hia
      have hbi : b ≠ i := by
        intro hbi
        subst b
        have hv := congrFun ha i
        simp [Pi.single_apply, hia] at hv hi
        omega
      have hv := congrFun ha i
      simp [Pi.single_apply, hia, hbi] at hv hi
      omega
    subst a
    exact Or.inr ⟨b, hab.symm, ha⟩
  · exfalso
    have hv := congrFun ha i
    by_cases hai : a = i <;> simp [Pi.single_apply, hai] at hv hi <;> omega
  · have hbi : b = i := by
      by_contra hbi
      have hai : a ≠ i := by
        intro hai
        subst a
        have hv := congrFun ha i
        simp [Pi.single_apply, hbi] at hv hi
        omega
      have hv := congrFun ha i
      simp [Pi.single_apply, hai, hbi] at hv hi
      omega
    subst b
    right
    refine ⟨a, hab, ?_⟩
    rw [ha]
    ext v
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring

/-- Restricting coordinates after promotion preserves a unit relation incident with
an unpromoted positive endpoint. -/
theorem unitRelation_restrict_at_one {V : Type*} [Fintype V] [DecidableEq V]
    {w : V → ℤ} (i : V) (hu : IsUnitRelation w) (hi : w i = 1)
    (T : Finset V) (hiT : i ∉ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => w v.1) := by
  rcases unitRelation_normalize_at_one i hu hi with hw | ⟨b, hbi, hw⟩
  · left
    refine ⟨⟨i, hiT⟩, ?_⟩
    funext v
    rw [hw]
    simp [Pi.single_apply, Subtype.ext_iff]
  · by_cases hbT : b ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      rw [hw]
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp [Pi.single_apply, hvb, Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨b, hbT⟩, ?_, ?_⟩
      · exact fun e => hbi (congrArg Subtype.val e).symm
      · funext v
        rw [hw]
        simp [Pi.single_apply, Subtype.ext_iff]

theorem multiset_card_le_two_cases {V : Type*} (ν : Multiset V) (hν : ν.card ≤ 2) :
    ν = 0 ∨ (∃ a, ν = {a}) ∨ ∃ a b, ν = {a, b} := by
  rcases Nat.eq_zero_or_pos ν.card with h0 | hp
  · exact Or.inl (Multiset.card_eq_zero.mp h0)
  have hc : ν.card = 1 ∨ ν.card = 2 := by omega
  rcases hc with h1 | h2
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    exact Or.inr (Or.inl ⟨a, ha⟩)
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp h2
    exact Or.inr (Or.inr ⟨a, b, hab⟩)

theorem count_pair_apply {V : Type*} [DecidableEq V] (a b v : V) :
    (({a, b} : Multiset V).count v : ℤ) =
      (Pi.single a (1 : ℤ) : V → ℤ) v + (Pi.single b (1 : ℤ) : V → ℤ) v := by
  have hc : ({a, b} : Multiset V).count v =
      (if v = a then 1 else 0) + if v = b then 1 else 0 := by
    rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    rw [add_comm]
  rw [hc]
  simp only [Pi.single_apply]
  push_cast
  rfl

theorem count_singleton_apply {V : Type*} [DecidableEq V] (a v : V) :
    (({a} : Multiset V).count v : ℤ) = (Pi.single a (1 : ℤ) : V → ℤ) v := by
  rw [Multiset.count_singleton]
  simp only [Pi.single_apply]
  split <;> norm_num

/-- If the outgoing live multiset contains the second endpoint, cancellation makes
the departing row a unit relation.  This is the `direct` case in Section 4. -/
theorem departingLive_unit_of_mem_right {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hcard : ν.card ≤ 2) (hmem : j ∈ ν)
    (hne : ν ≠ {i, j}) : IsUnitRelation (departingLive i j ν) := by
  rcases multiset_card_le_two_cases ν hcard with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · rw [h0] at hmem
    simp at hmem
  · subst ν
    simp only [Multiset.mem_singleton] at hmem
    subst a
    left
    refine ⟨i, ?_⟩
    ext v
    simp [departingLive, count_singleton_apply]
  · subst ν
    rw [Multiset.insert_eq_cons] at hmem
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · by_cases hbi : b = i
      · subst b
        exact absurd (Multiset.pair_comm j i) hne
      · right; left
        refine ⟨i, b, Ne.symm hbi, ?_⟩
        ext v
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [count_pair_apply]
        ring
    · by_cases hai : a = i
      · subst a
        exact absurd (by simpa) hne
      · right; left
        refine ⟨i, a, Ne.symm hai, ?_⟩
        ext v
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [count_pair_apply]
        ring

theorem departingLive_comm {V : Type*} [DecidableEq V] (i j : V) (ν : Multiset V) :
    departingLive i j ν = departingLive j i ν := by
  ext v
  simp only [departingLive, Pi.add_apply, Pi.sub_apply]
  ring

/-- The symmetric immediate-cancellation case. -/
theorem departingLive_unit_of_mem_left {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hcard : ν.card ≤ 2) (hmem : i ∈ ν)
    (hne : ν ≠ {i, j}) : IsUnitRelation (departingLive i j ν) := by
  have hne' : ν ≠ {j, i} := by
    intro h
    apply hne
    rw [h, Multiset.pair_comm]
  rw [departingLive_comm i j ν]
  exact departingLive_unit_of_mem_right j i ν hcard hmem hne'

/-- In the direct-cancellation case the surviving anchor coefficient is exactly one. -/
theorem departingLive_anchor_of_mem_right {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hcard : ν.card ≤ 2)
    (hmem : j ∈ ν) (hne : ν ≠ {i, j}) : departingLive i j ν i = 1 := by
  rcases multiset_card_le_two_cases ν hcard with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · subst ν
    simp at hmem
  · subst ν
    simp only [Multiset.mem_singleton] at hmem
    subst a
    simp [departingLive, count_singleton_apply, Pi.single_apply, hij]
  · subst ν
    have hj : j = a ∨ j = b := by simpa using hmem
    have hi : i ≠ a ∧ i ≠ b := by
      constructor
      · intro hia
        subst a
        rcases hj with hji | hjb
        · exact hij hji.symm
        · apply hne
          simpa [hjb]
      · intro hib
        subst b
        rcases hj with hja | hji
        · subst j
          exact hne (Multiset.pair_comm a i)
        · exact hij hji.symm
    simp only [departingLive, Pi.add_apply, Pi.sub_apply]
    rw [count_pair_apply]
    simp [Pi.single_apply, hij, hi.1, hi.2]

/-- Symmetric immediate cancellation leaves coefficient one at the label. -/
theorem departingLive_label_of_mem_left {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hcard : ν.card ≤ 2)
    (hmem : i ∈ ν) (hne : ν ≠ {i, j}) : departingLive i j ν j = 1 := by
  rw [departingLive_comm]
  apply departingLive_anchor_of_mem_right j i ν hij.symm hcard hmem
  intro h
  apply hne
  exact h.trans (Multiset.pair_comm j i)

theorem departingLive_anchor_of_not_mem {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hij : i ≠ j) (hi : i ∉ ν) :
    departingLive i j ν i = 1 := by
  simp [departingLive, Pi.single_apply, hij, Multiset.count_eq_zero.mpr hi]

/-- Subtracting two proper rows of the same type cancels both the anchor and the type,
leaving the unit difference between their labels. -/
theorem departingLive_sub_same_type {V : Type*} [DecidableEq V]
    (i j j' : V) (ν : Multiset V) :
    departingLive i j ν - departingLive i j' ν =
      Pi.single j 1 - Pi.single j' 1 := by
  ext v
  simp only [departingLive, Pi.add_apply, Pi.sub_apply]
  ring

def IsEasyDeparture {V : Type*} (i j : V) (ν : Multiset V) : Prop :=
  i ∉ ν ∧ j ∉ ν ∧ ν.card ≤ 1

def IsProperDeparture {V : Type*} (i j : V) (ν : Multiset V) : Prop :=
  i ∉ ν ∧ j ∉ ν ∧ ν.card = 2

/-- Sampling the label of an easy departure turns its surviving live part into a
unit relation.  The outgoing multiset has size at most one, so it either disappears
into the promoted core or supplies the other endpoint of a live edge. -/
theorem easy_after_promote_unit {V : Type*} [Fintype V] [DecidableEq V]
    {i j : V} {ν : Multiset V} (h : IsEasyDeparture i j ν)
    (T : Finset V) (hiT : i ∉ T) (hjT : j ∈ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => departingLive i j ν v.1) := by
  classical
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiT hjT
  rcases Nat.eq_zero_or_pos ν.card with hzero | hpos
  · have hν : ν = 0 := Multiset.card_eq_zero.mp hzero
    left
    refine ⟨⟨i, hiT⟩, ?_⟩
    funext v
    have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
    simp [departingLive, hν, Pi.single_apply, hvj, Subtype.ext_iff]
  · have hle : ν.card ≤ 1 := h.2.2
    have hcard : ν.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hcard
    have hia : i ≠ a := by simpa using h.1
    by_cases haT : a ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
      simp [departingLive, count_singleton_apply, Pi.single_apply, hvj, hva,
        Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨a, haT⟩, ?_, ?_⟩
      · exact fun e => hia (congrArg Subtype.val e)
      · funext v
        have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
        simp [departingLive, count_singleton_apply, Pi.single_apply, hvj,
          Subtype.ext_iff]

/-- A hit proper configuration likewise leaves a unit row: its distinguished label
and at least one member of its two-element type enter the core, leaving either
`x_i` or `x_i-x_a`. -/
theorem proper_after_promote_unit {V : Type*} [Fintype V] [DecidableEq V]
    {i j : V} {ν : Multiset V} (h : IsProperDeparture i j ν)
    (T : Finset V) (hiT : i ∉ T) (hjT : j ∈ T)
    (hhit : ∃ u ∈ T, u ∈ ν) :
    IsUnitRelation (fun v : {v : V // v ∉ T} => departingLive i j ν v.1) := by
  classical
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiT hjT
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h.2.2
  have hia : i ≠ a := by
    intro e
    subst a
    exact h.1 (by simp)
  have hib : i ≠ b := by
    intro e
    subst b
    exact h.1 (by simp)
  rcases hhit with ⟨u, huT, huν⟩
  have habT : a ∈ T ∨ b ∈ T := by
    have huv : u = a ∨ u = b := by simpa using huν
    rcases huv with rfl | rfl
    · exact Or.inl huT
    · exact Or.inr huT
  by_cases haT : a ∈ T
  · by_cases hbT : b ∈ T
    · left
      refine ⟨⟨i, hiT⟩, ?_⟩
      funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp only [departingLive, Pi.add_apply, Pi.sub_apply]
      rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
        (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
          (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
      simp [departingLive, Pi.single_apply, hvj, hva, hvb, Subtype.ext_iff]
    · right; left
      refine ⟨⟨i, hiT⟩, ⟨b, hbT⟩, ?_, ?_⟩
      · exact fun e => hib (congrArg Subtype.val e)
      · funext v
        have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
        have hva : v.1 ≠ a := fun e => v.2 (e ▸ haT)
        simp only [departingLive, Pi.add_apply, Pi.sub_apply]
        rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
          (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
            (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
        simp [departingLive, Pi.single_apply, hvj, hva, Subtype.ext_iff]
  · have hbT : b ∈ T := habT.resolve_left haT
    right; left
    refine ⟨⟨i, hiT⟩, ⟨a, haT⟩, ?_, ?_⟩
    · exact fun e => hia (congrArg Subtype.val e)
    · funext v
      have hvj : v.1 ≠ j := fun e => v.2 (e ▸ hjT)
      have hvb : v.1 ≠ b := fun e => v.2 (e ▸ hbT)
      simp only [departingLive, Pi.add_apply, Pi.sub_apply]
      rw [show (({a, b} : Multiset V).count v.1 : ℤ) =
        (Pi.single a (1 : ℤ) : V → ℤ) v.1 +
          (Pi.single b (1 : ℤ) : V → ℤ) v.1 by exact count_pair_apply a b v.1]
      simp [departingLive, Pi.single_apply, hvj, hvb, Subtype.ext_iff]

/-- The exhaustive direct/easy/proper classification following (4.1). -/
theorem departing_classification {V : Type*} [DecidableEq V]
    (i j : V) (ν : Multiset V) (hcard : ν.card ≤ 2) (hne : ν ≠ {i, j}) :
    IsUnitRelation (departingLive i j ν) ∨
      IsEasyDeparture i j ν ∨ IsProperDeparture i j ν := by
  by_cases hi : i ∈ ν
  · exact Or.inl (departingLive_unit_of_mem_left i j ν hcard hi hne)
  by_cases hj : j ∈ ν
  · exact Or.inl (departingLive_unit_of_mem_right i j ν hcard hj hne)
  right
  rcases lt_or_eq_of_le hcard with hlt | heq
  · exact Or.inl ⟨hi, hj, by omega⟩
  · exact Or.inr ⟨hi, hj, heq⟩

theorem proper_support_avoids_label {V : Type*} [DecidableEq V] {i j : V} {ν : Multiset V}
    (h : IsProperDeparture i j ν) : j ∉ ν.toFinset := by
  simpa using h.2.1

theorem proper_eq_pair {V : Type*} {i j : V} {ν : Multiset V}
    (h : IsProperDeparture i j ν) : ∃ a b, ν = {a, b} :=
  Multiset.card_eq_two.mp h.2.2

/-- A proper departure is exactly a common-cut configuration: its label is outside
the support of its two-element type. -/
theorem exists_configuration_of_proper {V : Type*} [DecidableEq V]
    {i j : V} {ν : Multiset V} (h : IsProperDeparture i j ν) :
    ∃ a b : V, ∃ c : Configuration V, ν = {a, b} ∧ c.j = j ∧ c.τ = s(a, b) := by
  obtain ⟨a, b, hab⟩ := proper_eq_pair h
  subst ν
  have hja : j ≠ a := by
    intro e
    subst a
    exact h.2.1 (by simp)
  have hjb : j ≠ b := by
    intro e
    subst b
    exact h.2.1 (by simp)
  refine ⟨a, b, ⟨j, s(a, b), ?_⟩, rfl, rfl, rfl⟩
  · simpa [Sym2.mem_iff, hja, hjb]

/-! ### Live blocks and projection of collision rows -/

/-- A family of disjoint live blocks, encoded by a partial owner map.  Indices whose
owner is `none` have already been promoted to the core. -/
structure LiveBlocks (n : ℕ) (V : Type*) where
  block : V → Finset (Fin n)
  owner : Fin n → Option V
  mem_block_iff : ∀ a v, a ∈ block v ↔ owner a = some v
  nonempty : ∀ v, (block v).Nonempty

noncomputable def LiveBlocks.heavy {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => L ≤ (B.block v).card

def LiveBlocks.mass {n : ℕ} {V : Type*} [Fintype V]
    (B : LiveBlocks n V) : ℕ := ∑ v, (B.block v).card

theorem LiveBlocks.disjoint {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (hij : i ≠ j) : Disjoint (B.block i) (B.block j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  have hi := (B.mem_block_iff a i).mp hai
  have hj := (B.mem_block_iff a j).mp haj
  exact hij (Option.some.inj (hi.symm.trans hj))

theorem LiveBlocks.mass_le {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) : B.mass ≤ n := by
  classical
  have hd : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint B.block := by
    intro i hi j hj hij
    exact B.disjoint hij
  calc
    B.mass = (Finset.univ.biUnion B.block).card := (Finset.card_biUnion hd).symm
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

/-- The multiset of still-live owners of the two endpoints of an index pair. -/
def liveLabels {n : ℕ} {V : Type*} (B : LiveBlocks n V) : Sym2 (Fin n) → Multiset V :=
  Sym2.lift ⟨fun a b => (B.owner a).toList + (B.owner b).toList, by
    intro a b
    exact add_comm _ _⟩

theorem liveLabels_mk {n : ℕ} {V : Type*} (B : LiveBlocks n V) (a b : Fin n) :
    liveLabels B s(a, b) = (B.owner a).toList + (B.owner b).toList := rfl

theorem liveLabels_card_le_two {n : ℕ} {V : Type*} (B : LiveBlocks n V)
    (t : Sym2 (Fin n)) : (liveLabels B t).card ≤ 2 := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      simp only [liveLabels_mk, Multiset.card_add, Option.toList]
      split <;> split <;> simp

theorem liveLabels_source_pair {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} {t : Sym2 (Fin n)}
    (ht : t ∈ MinimalNUS.rectangle (B.block i) (B.block j)) :
    liveLabels B t = {i, j} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  rw [liveLabels_mk, (B.mem_block_iff a i).mp ha, (B.mem_block_iff b j).mp hb]
  simp [Multiset.insert_eq_cons]

theorem mem_rectangle_of_liveLabels_eq_pair {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (hij : i ≠ j) {t : Sym2 (Fin n)}
    (ht : liveLabels B t = {i, j}) :
    t ∈ MinimalNUS.rectangle (B.block i) (B.block j) := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [liveLabels_mk] at ht
      rcases hOA : B.owner a with _ | u
      · have hc := congrArg Multiset.card ht
        simp [hOA] at hc
        rcases hOB : B.owner b with _ | v <;> simp [hOB] at hc
      rcases hOB : B.owner b with _ | v
      · have hc := congrArg Multiset.card ht
        simp [hOA, hOB] at hc
      have huv : ({u, v} : Multiset V) = {i, j} := by
        simpa [hOA, hOB, Multiset.insert_eq_cons] using ht
      rcases (multiset_pair_eq_pair.mp huv) with ⟨hui, hvj⟩ | ⟨huj, hvi⟩
      · subst u; subst v
        exact ⟨a, (B.mem_block_iff a i).mpr hOA, b,
          (B.mem_block_iff b j).mpr hOB, rfl⟩
      · subst u; subst v
        rw [Sym2.eq_swap]
        exact ⟨b, (B.mem_block_iff b i).mpr hOB, a,
          (B.mem_block_iff a j).mpr hOA, rfl⟩

theorem liveLabels_departing_ne {n : ℕ} {V : Type*} [DecidableEq V]
    (B : LiveBlocks n V) {i j : V} (hij : i ≠ j) {t : Sym2 (Fin n)}
    (hout : t ∉ MinimalNUS.rectangle (B.block i) (B.block j)) :
    liveLabels B t ≠ {i, j} := by
  intro h
  exact hout (mem_rectangle_of_liveLabels_eq_pair B hij h)

/-- Algebraic data maintained during contraction.  The quotient basis is split into
permanent core coordinates and one coordinate for each live block. -/
structure CompressionState {p n : ℕ} (S : MinimalNUS p n) (P : S.Pairing)
    (C V : Type*) [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V] where
  Q : Submodule ℤ (Fin n → ℤ)
  le_colLat : Q ≤ S.colLat P
  primitive : ∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q
  basis : Module.Basis (Sum C V) ℤ ((Fin n → ℤ) ⧸ Q)
  blocks : LiveBlocks n V
  live_coord : ∀ a v,
    basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) =
      if blocks.owner a = some v then 1 else 0

namespace CompressionState

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {B : LiveBlocks n V}

noncomputable def projectedRow (st : CompressionState S P C V) (t : Sym2 (Fin n)) : Sum C V → ℤ :=
  st.basis.repr (Submodule.Quotient.mk (S.rho P t))

/-- The quantitative part of the round invariant: after removing the single live
coordinate (if any), every original coordinate has core `ℓ¹`-norm at most `M`. -/
def CoreBound (st : CompressionState S P C V) (M : ℤ) : Prop :=
  ∀ a : Fin n,
    ∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| ≤ M

theorem coreBound_nonneg (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) : 0 ≤ M := by
  classical
  let a : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) S.two_le⟩
  exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hM a)

/-- The core part of the image of a two-index incidence vector has norm at most
`2M`. -/
theorem core_norm_uvec_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : C,
        |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)| ≤ 2 * M := by
  classical
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [uvec_mk, Submodule.Quotient.mk_add]
      calc
        ∑ c : C,
            |(st.basis.repr
                (Submodule.Quotient.mk (Pi.single a 1) +
                  Submodule.Quotient.mk (Pi.single b 1))) (Sum.inl c)|
            ≤ ∑ c : C,
                (|st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| +
                 |st.basis.repr (Submodule.Quotient.mk (Pi.single b 1)) (Sum.inl c)|) := by
              apply Finset.sum_le_sum
              intro c hc
              rw [map_add, Finsupp.add_apply]
              exact abs_add_le _ _
        _ = (∑ c : C,
                |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)|) +
              ∑ c : C,
                |st.basis.repr (Submodule.Quotient.mk (Pi.single b 1)) (Sum.inl c)| := by
              rw [Finset.sum_add_distrib]
        _ ≤ M + M := add_le_add (hM a) (hM b)
        _ = 2 * M := by ring

/-- Equation (4.1), quantitatively: the core-supported error in every raw departing
row has norm at most `4M` (in fact this holds for every collision row). -/
theorem projectedRow_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : C, |st.projectedRow t (Sum.inl c)| ≤ 4 * M := by
  classical
  change ∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inl c)| ≤ _
  rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]
  calc
    ∑ c : C,
        |(st.basis.repr
            (Submodule.Quotient.mk (uvec t) -
              Submodule.Quotient.mk (uvec (P.μ t)))) (Sum.inl c)|
        ≤ ∑ c : C,
            (|st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)| +
             |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inl c)|) := by
          apply Finset.sum_le_sum
          intro c hc
          rw [map_sub, Finsupp.sub_apply]
          exact abs_sub _ _
    _ = (∑ c : C, |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inl c)|) +
          ∑ c : C, |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inl c)| := by
          rw [Finset.sum_add_distrib]
    _ ≤ 2 * M + 2 * M := add_le_add (st.core_norm_uvec_le hM t)
      (st.core_norm_uvec_le hM (P.μ t))
    _ = 4 * M := by ring

theorem live_coord_uvec (st : CompressionState S P C V) (t : Sym2 (Fin n)) (v : V) :
    st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v) =
      ((liveLabels st.blocks t).count v : ℤ) := by
  induction t using Sym2.inductionOn with
  | hf a b =>
      rw [uvec_mk]
      rw [Submodule.Quotient.mk_add, map_add, Finsupp.add_apply]
      simp only [liveLabels_mk]
      rcases ha : st.blocks.owner a with _ | x <;>
        rcases hb : st.blocks.owner b with _ | y
      all_goals
        rw [st.live_coord a v, st.live_coord b v]
        simp [ha, hb, Multiset.count_add, Multiset.count_cons,
          Multiset.count_singleton, eq_comm, add_comm]

/-- The live part of an incidence vector has `ℓ1`-norm at most two, even when
one or both physical endpoints already belong to the core. -/
theorem live_norm_uvec_le (st : CompressionState S P C V) (t : Sym2 (Fin n)) :
    ∑ v : V, |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)| ≤ 2 := by
  classical
  simp_rw [st.live_coord_uvec]
  have hsum : ∑ v : V, (liveLabels st.blocks t).count v =
      (liveLabels st.blocks t).card := by
    exact Multiset.sum_count_eq_card (by simp)
  have hcard := liveLabels_card_le_two st.blocks t
  have habs : ∀ v : V, |((liveLabels st.blocks t).count v : ℤ)| =
      ((liveLabels st.blocks t).count v : ℤ) := by
    intro v
    exact abs_of_nonneg (by positivity)
  simp_rw [habs]
  exact_mod_cast hsum.symm ▸ hcard

/-- Every collision row has live `ℓ1`-norm at most four. -/
theorem projectedRow_live_norm_le (st : CompressionState S P C V)
    (t : Sym2 (Fin n)) :
    ∑ v : V, |st.projectedRow t (Sum.inr v)| ≤ 4 := by
  classical
  change ∑ v : V,
      |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| ≤ 4
  rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]
  calc
    ∑ v : V,
        |(st.basis.repr
          (Submodule.Quotient.mk (uvec t) - Submodule.Quotient.mk (uvec (P.μ t))))
            (Sum.inr v)|
      ≤ ∑ v : V,
          (|st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)| +
           |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inr v)|) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [map_sub, Finsupp.sub_apply]
        exact abs_sub _ _
    _ = (∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (uvec t)) (Sum.inr v)|) +
        ∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (uvec (P.μ t))) (Sum.inr v)| := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 + 2 := add_le_add (st.live_norm_uvec_le t) (st.live_norm_uvec_le (P.μ t))
    _ = 4 := by norm_num

theorem projectedRow_live (st : CompressionState S P C V) {i j : V}
    (hij : i ≠ j) {t : Sym2 (Fin n)}
    (ht : t ∈ MinimalNUS.rectangle (st.blocks.block i) (st.blocks.block j)) :
    (fun v => st.projectedRow t (Sum.inr v)) =
      departingLive i j (liveLabels st.blocks (P.μ t)) := by
  have hsrc := liveLabels_source_pair st.blocks ht
  ext v
  change st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v) = _
  rw [show Submodule.Quotient.mk (S.rho P t) =
      Submodule.Quotient.mk (uvec t) - Submodule.Quotient.mk (uvec (P.μ t)) by
        rw [MinimalNUS.rho, Submodule.Quotient.mk_sub]]
  rw [map_sub, Finsupp.sub_apply, st.live_coord_uvec, st.live_coord_uvec]
  rw [hsrc, count_pair_apply]
  rfl

theorem projected_departing_classification (st : CompressionState S P C V)
    {i j : V} (hij : i ≠ j) {t : Sym2 (Fin n)}
    (ht : t ∈ MinimalNUS.rectangle (st.blocks.block i) (st.blocks.block j))
    (hout : P.μ t ∉ MinimalNUS.rectangle (st.blocks.block i) (st.blocks.block j)) :
    IsUnitRelation (fun v => st.projectedRow t (Sum.inr v)) ∨
      IsEasyDeparture i j (liveLabels st.blocks (P.μ t)) ∨
      IsProperDeparture i j (liveLabels st.blocks (P.μ t)) := by
  rw [st.projectedRow_live hij ht]
  apply departing_classification
  · exact liveLabels_card_le_two st.blocks _
  · exact liveLabels_departing_ne st.blocks hij hout

end CompressionState

def initialLiveBlocks (n : ℕ) : LiveBlocks n (Fin n) where
  block i := {i}
  owner a := some a
  mem_block_iff a i := by simp
  nonempty i := ⟨i, by simp⟩

/-- The stage at round zero: no relations, no core coordinates, and singleton live
blocks. -/
noncomputable def initialCompressionState {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : CompressionState S P Empty (Fin n) := by
  let e : (Fin n → ℤ) ≃ₗ[ℤ] ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    LinearEquiv.ofBijective (⊥ : Submodule ℤ (Fin n → ℤ)).mkQ
      ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ], Submodule.mkQ_surjective _⟩
  let b₀ : Module.Basis (Fin n) ℤ ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    (Pi.basisFun ℤ (Fin n)).map e
  let b : Module.Basis (Sum Empty (Fin n)) ℤ
      ((Fin n → ℤ) ⧸ (⊥ : Submodule ℤ (Fin n → ℤ))) :=
    b₀.reindex (Equiv.emptySum Empty (Fin n)).symm
  refine
    { Q := ⊥
      le_colLat := bot_le
      primitive := ?_
      basis := b
      blocks := initialLiveBlocks n
      live_coord := ?_ }
  · intro v c hc hcv
    simpa only [Submodule.mem_bot] using (smul_eq_zero.mp hcv).resolve_left hc
  · intro a v
    have he : e.symm (Submodule.Quotient.mk (Pi.single a 1)) = Pi.single a 1 := by
      rw [e.symm_apply_eq]
      rfl
    simp only [b, Module.Basis.repr_reindex_apply, Equiv.emptySum_symm_apply,
      b₀, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, he,
      initialLiveBlocks]
    simp [Pi.single_apply, eq_comm]

theorem initialCompressionState_coreBound {p n : ℕ} (S : MinimalNUS p n)
    (P : S.Pairing) : (initialCompressionState S P).CoreBound 0 := by
  intro a
  simp [CompressionState.CoreBound]

/-! ### Reclassifying live representatives as core coordinates -/

/-- Remove the promoted values of `T` from an optional live owner. -/
def promoteOwner {V : Type*} [DecidableEq V] (T : Finset V) :
    Option V → Option {v : V // v ∉ T}
  | none => none
  | some v => if hv : v ∈ T then none else some ⟨v, hv⟩

@[simp] theorem promoteOwner_eq_some_iff {V : Type*} [DecidableEq V]
    (T : Finset V) (o : Option V) (v : {v : V // v ∉ T}) :
    promoteOwner T o = some v ↔ o = some v.1 := by
  rcases o with _ | w
  · simp [promoteOwner]
  · by_cases hw : w ∈ T
    · have hwv : w ≠ v.1 := by
        intro h
        subst w
        exact v.2 hw
      simp [promoteOwner, hw, hwv]
    · simp [promoteOwner, hw, Subtype.ext_iff]

/-- The remaining block system after the labels in `T` are promoted. -/
def LiveBlocks.promote {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) (T : Finset V) : LiveBlocks n {v : V // v ∉ T} where
  block v := B.block v.1
  owner a := promoteOwner T (B.owner a)
  mem_block_iff a v := by
    rw [B.mem_block_iff, promoteOwner_eq_some_iff]
  nonempty v := B.nonempty v.1

theorem LiveBlocks.promote_heavy_is_light {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ)
    (v : {v : V // v ∉ B.heavy L}) : ((B.promote (B.heavy L)).block v).card < L := by
  have hv : ¬L ≤ (B.block v.1).card := by
    simpa only [LiveBlocks.heavy, Finset.mem_filter, Finset.mem_univ, true_and] using v.2
  simpa [LiveBlocks.promote] using (Nat.lt_of_not_ge hv)

theorem LiveBlocks.heavy_card_mul_le {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ) :
    L * (B.heavy L).card ≤ B.mass := by
  classical
  have hsum : (∑ v ∈ B.heavy L, L) ≤
      ∑ v ∈ B.heavy L, (B.block v).card := by
    apply Finset.sum_le_sum
    intro v hv
    simpa only [LiveBlocks.heavy, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  calc
    L * (B.heavy L).card = ∑ v ∈ B.heavy L, L := by simp [mul_comm]
    _ ≤ ∑ v ∈ B.heavy L, (B.block v).card := hsum
    _ ≤ ∑ v : V, (B.block v).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      omega

theorem LiveBlocks.heavy_card_mul_le_removed {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (L : ℕ) :
    L * (B.heavy L).card ≤ ∑ v ∈ B.heavy L, (B.block v).card := by
  classical
  calc
    L * (B.heavy L).card = ∑ v ∈ B.heavy L, L := by simp [mul_comm]
    _ ≤ ∑ v ∈ B.heavy L, (B.block v).card := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [LiveBlocks.heavy, Finset.mem_filter, Finset.mem_univ, true_and]
        using hv

theorem LiveBlocks.mass_promote_add_removed {n : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (T : Finset V) :
    (B.promote T).mass + ∑ v ∈ T, (B.block v).card = B.mass := by
  classical
  let U := Finset.univ.filter fun v : V => v ∉ T
  have hnewdisj : (↑(Finset.univ : Finset {v : V // v ∉ T}) :
      Set {v : V // v ∉ T}).PairwiseDisjoint (B.promote T).block := by
    intro i hi j hj hij
    exact (B.promote T).disjoint hij
  have hUdisj : (↑U : Set V).PairwiseDisjoint B.block := by
    intro i hi j hj hij
    exact B.disjoint hij
  have hunion : Finset.univ.biUnion (B.promote T).block = U.biUnion B.block := by
    ext a
    constructor
    · intro ha
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp ha
      apply Finset.mem_biUnion.mpr
      exact ⟨v.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.2⟩, hav⟩
    · intro ha
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp ha
      have hvT := (Finset.mem_filter.mp hv).2
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨v, hvT⟩, Finset.mem_univ _, hav⟩
  have hmass : (B.promote T).mass = ∑ v ∈ U, (B.block v).card := by
    calc
      (B.promote T).mass =
          (Finset.univ.biUnion (B.promote T).block).card :=
        (Finset.card_biUnion hnewdisj).symm
      _ = (U.biUnion B.block).card := congrArg Finset.card hunion
      _ = ∑ v ∈ U, (B.block v).card := Finset.card_biUnion hUdisj
  rw [hmass]
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v : V => v ∈ T) (fun v => (B.block v).card)
  have hT : Finset.univ.filter (fun v : V => v ∈ T) = T := by ext v; simp
  have hU : Finset.univ.filter (fun v : V => ¬v ∈ T) = U := by ext v; simp [U]
  rw [hT, hU] at hpart
  simpa [LiveBlocks.mass, add_comm] using hpart

/-- Rebracket the old core/live basis after promoting `T`: old core coordinates and
promoted labels form the new core; precisely the labels outside `T` remain live. -/
def promoteIndexEquiv {C V : Type*} [DecidableEq V] (T : Finset V) :
    Sum (Sum C {v : V // v ∈ T}) {v : V // v ∉ T} ≃ Sum C V where
  toFun
    | Sum.inl (Sum.inl c) => Sum.inl c
    | Sum.inl (Sum.inr v) => Sum.inr v.1
    | Sum.inr v => Sum.inr v.1
  invFun
    | Sum.inl c => Sum.inl (Sum.inl c)
    | Sum.inr v => if hv : v ∈ T then Sum.inl (Sum.inr ⟨v, hv⟩) else Sum.inr ⟨v, hv⟩
  left_inv x := by
    rcases x with (c | v) | v
    · rfl
    · simp [v.2]
    · simp [v.2]
  right_inv x := by
    rcases x with c | v
    · rfl
    · by_cases hv : v ∈ T <;> simp [hv]

/-- Promotion changes no lattice or quotient; it only reindexes the basis and removes
the promoted physical blocks from the live block system. -/
noncomputable def CompressionState.promote {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (T : Finset V) :
    CompressionState S P (Sum C {v : V // v ∈ T}) {v : V // v ∉ T} where
  Q := st.Q
  le_colLat := st.le_colLat
  primitive := st.primitive
  basis := st.basis.reindex (promoteIndexEquiv T).symm
  blocks := st.blocks.promote T
  live_coord a v := by
    rw [Module.Basis.repr_reindex_apply]
    change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr (v : V)) = _
    rw [st.live_coord]
    have hp : (st.blocks.promote T).owner a = some v ↔
        st.blocks.owner a = some v.1 := promoteOwner_eq_some_iff T _ v
    by_cases h : st.blocks.owner a = some v.1
    · simp [h, hp.mpr h]
    · have h' : (st.blocks.promote T).owner a ≠ some v := fun h' => h (hp.mp h')
      simp [h, h']

@[simp] theorem CompressionState.promote_old_core_coord {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (a : Fin n) (c : C) :
    (st.promote T).basis.repr (Submodule.Quotient.mk (Pi.single a 1))
        (Sum.inl (Sum.inl c)) =
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_new_core_coord {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (a : Fin n) (v : {v : V // v ∈ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk (Pi.single a 1))
        (Sum.inl (Sum.inr v)) =
      if st.blocks.owner a = some v.1 then 1 else 0 := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr (v : V)) = _
  exact st.live_coord a v.1

/-- The coordinate formulas for promotion hold for every ambient row, not just the
original coordinate vectors.  These formulas let us carry the actual collision rows
chosen before a round through its promotion step. -/
@[simp] theorem CompressionState.promote_old_core_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ) (c : C) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r)
        (Sum.inl (Sum.inl c)) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_new_core_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ)
    (v : {v : V // v ∈ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r)
        (Sum.inl (Sum.inr v)) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

@[simp] theorem CompressionState.promote_live_coord_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ)
    (v : {v : V // v ∉ T}) :
    (st.promote T).basis.repr (Submodule.Quotient.mk r) (Sum.inr v) =
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1) := by
  rw [CompressionState.promote, Module.Basis.repr_reindex_apply]
  rfl

/-- Promotion splits the old live coordinates into new core and surviving live
coordinates, so the promoted core norm is the old core norm plus precisely the
absolute coefficients of the promoted labels. -/
theorem CompressionState.promote_core_norm_row {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) (r : Fin n → ℤ) :
    (∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) =
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) +
        ∑ v : {v : V // v ∈ T},
          |st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v.1)| := by
  rw [Fintype.sum_sum_type]
  simp

/-- A raw collision row remains quantitatively bounded after an arbitrary promotion:
at most four old live coefficients can have moved into the core. -/
theorem CompressionState.promote_projectedRow_core_norm_le {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) {M : ℤ}
    (hM : st.CoreBound M) (t : Sym2 (Fin n)) :
    ∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk (S.rho P t))
          (Sum.inl c)| ≤ 4 * M + 4 := by
  rw [st.promote_core_norm_row T (S.rho P t)]
  apply add_le_add (st.projectedRow_core_norm_le hM t)
  calc
    ∑ v : {v : V // v ∈ T},
        |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v.1)|
      ≤ ∑ v : V,
          |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
        calc
          _ = ∑ v ∈ T,
              |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
                rw [← Finset.attach_eq_univ]
                exact Finset.sum_attach T (fun v =>
                  |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)|)
          _ ≤ ∑ v ∈ (Finset.univ : Finset V),
              |st.basis.repr (Submodule.Quotient.mk (S.rho P t)) (Sum.inr v)| := by
                exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
                  (fun v hv hnot => abs_nonneg _)
          _ = _ := by simp
    _ ≤ 4 := st.projectedRow_live_norm_le t

/-- In the round invariant `M ≥ 1`, the preceding estimate is at most `8M`, and
hence comfortably within the paper's uniform `12M` budget for forest rows. -/
theorem CompressionState.promote_projectedRow_core_norm_le_eight_mul {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (T : Finset V) {M : ℤ}
    (hM : st.CoreBound M) (hM1 : 1 ≤ M) (t : Sym2 (Fin n)) :
    ∑ c : Sum C {v : V // v ∈ T},
        |(st.promote T).basis.repr (Submodule.Quotient.mk (S.rho P t))
          (Sum.inl c)| ≤ 8 * M := by
  refine le_trans (st.promote_projectedRow_core_norm_le T hM t) ?_
  linarith

/-- Promoting any collection of live representatives raises the core bound by at
most one, since an original coordinate belongs to at most one live block. -/
theorem CompressionState.promote_coreBound {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (T : Finset V)
    {M : ℤ} (hM : st.CoreBound M) : (st.promote T).CoreBound (M + 1) := by
  classical
  intro a
  rw [Fintype.sum_sum_type]
  simp_rw [st.promote_old_core_coord, st.promote_new_core_coord]
  have hnew : (∑ v : {v : V // v ∈ T},
      |if st.blocks.owner a = some v.1 then (1 : ℤ) else 0|) ≤ 1 := by
    rcases h : st.blocks.owner a with _ | w
    · simp [h]
    · by_cases hw : w ∈ T
      · let wT : {v : V // v ∈ T} := ⟨w, hw⟩
        rw [Finset.sum_eq_single wT]
        · simp [h, wT]
        · intro v hv hvw
          have hvw' : v.1 ≠ w := by
            intro he
            apply hvw
            exact Subtype.ext he
          simp [h, hvw'.symm]
        · simp
      · have hne : ∀ v : {v : V // v ∈ T}, w ≠ v.1 := by
          intro v he
          subst w
          exact (hw v.2).elim
        simp [h, hne]
  exact add_le_add (hM a) hnew

/-! ### A single integral unit pivot -/

/-- Eliminate coordinate `v` using a relation `y` whose `v`-coefficient is one.
The remaining coordinates are exactly the old vector minus its `v`-coefficient
times `y`, with the now-zero pivot coordinate omitted. -/
def unitElim {C V : Type*} [DecidableEq V] (v : V) (y : Sum C V → ℤ) :
    (Sum C V → ℤ) →ₗ[ℤ] (Sum C {u : V // u ≠ v} → ℤ) where
  toFun z
    | Sum.inl c => z (Sum.inl c) - z (Sum.inr v) * y (Sum.inl c)
    | Sum.inr u => z (Sum.inr u.1) - z (Sum.inr v) * y (Sum.inr u.1)
  map_add' z z' := by
    funext i
    rcases i with c | u <;> simp <;> ring
  map_smul' k z := by
    funext i
    rcases i with c | u <;> simp [smul_eq_mul] <;> ring

@[simp] theorem unitElim_apply_left {C V : Type*} [DecidableEq V]
    (v : V) (y z : Sum C V → ℤ) (c : C) :
    unitElim v y z (Sum.inl c) =
      z (Sum.inl c) - z (Sum.inr v) * y (Sum.inl c) := rfl

@[simp] theorem unitElim_apply_right {C V : Type*} [DecidableEq V]
    (v : V) (y z : Sum C V → ℤ) (u : {u : V // u ≠ v}) :
    unitElim v y z (Sum.inr u) =
      z (Sum.inr u.1) - z (Sum.inr v) * y (Sum.inr u.1) := rfl

/-- A unit elimination is onto: prescribe all surviving coordinates and set the
pivot coordinate to zero. -/
theorem unitElim_surjective {C V : Type*} [DecidableEq V] (v : V)
    (y : Sum C V → ℤ) : Function.Surjective (unitElim v y) := by
  intro x
  let z : Sum C V → ℤ := fun i => match i with
    | Sum.inl c => x (Sum.inl c)
    | Sum.inr u => if h : u = v then 0 else x (Sum.inr ⟨u, h⟩)
  refine ⟨z, ?_⟩
  funext i
  rcases i with c | u
  · simp [unitElim, z]
  · simp [unitElim, z, u.2]

/-- If the pivot coefficient of `y` is one, the kernel of elimination is precisely
the cyclic submodule generated by `y`.  This is the algebraic reason every selected
forest row is a primitive pivot. -/
theorem ker_unitElim {C V : Type*} [DecidableEq V] (v : V) (y : Sum C V → ℤ)
    (hy : y (Sum.inr v) = 1) :
    LinearMap.ker (unitElim v y) = Submodule.span ℤ {y} := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    rw [Submodule.mem_span_singleton]
    refine ⟨z (Sum.inr v), ?_⟩
    funext i
    rcases i with c | u
    · have h := congrFun hz (Sum.inl c)
      simp only [unitElim_apply_left, Pi.zero_apply] at h
      change z (Sum.inr v) * y (Sum.inl c) = z (Sum.inl c)
      linarith
    · by_cases huv : u = v
      · subst u
        simp [hy, Pi.smul_apply, smul_eq_mul]
      · have h := congrFun hz (Sum.inr (⟨u, huv⟩ : {u : V // u ≠ v}))
        simp only [unitElim_apply_right, Pi.zero_apply] at h
        change z (Sum.inr v) * y (Sum.inr u) = z (Sum.inr u)
        linarith
  · rw [Submodule.mem_span_singleton]
    rintro ⟨k, rfl⟩
    rw [LinearMap.mem_ker]
    funext i
    rcases i with c | u <;>
      simp [unitElim, hy, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Kernels of maps to a free integral coordinate module are primitive. -/
theorem ker_primitive {M ι : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] (ι → ℤ)) :
    ∀ (x : M) (c : ℤ), c ≠ 0 → c • x ∈ LinearMap.ker f → x ∈ LinearMap.ker f := by
  intro x c hc hcx
  rw [LinearMap.mem_ker] at hcx ⊢
  funext i
  have h := congrFun hcx i
  rw [map_zsmul, Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hc

/-- Update an optional block owner after eliminating `v`; indices formerly owned by
`v` move to `parent`, and every other live owner is restricted to `V \ {v}`. -/
def contractOwner {V : Type*} [DecidableEq V] (v : V)
    (parent : Option {u : V // u ≠ v}) : Option V → Option {u : V // u ≠ v}
  | none => none
  | some u => if h : u = v then parent else some ⟨u, h⟩

@[simp] theorem contractOwner_eq_some_iff {V : Type*} [DecidableEq V] (v : V)
    (parent : Option {u : V // u ≠ v}) (o : Option V) (u : {u : V // u ≠ v}) :
    contractOwner v parent o = some u ↔
      o = some u.1 ∨ (o = some v ∧ parent = some u) := by
  rcases o with _ | w
  · simp [contractOwner]
  · by_cases hwv : w = v
    · subst w
      have hvu : v ≠ u.1 := Ne.symm u.2
      simp [contractOwner, hvu]
    · simp [contractOwner, hwv, Subtype.ext_iff]

theorem contractOwner_indicator {V : Type*} [DecidableEq V] (v : V)
    (parent : Option {u : V // u ≠ v}) (o : Option V) (u : {u : V // u ≠ v}) :
    (if o = some u.1 then (1 : ℤ) else 0) -
        (if o = some v then (1 : ℤ) else 0) *
          (if parent = some u then (-1 : ℤ) else 0) =
      if contractOwner v parent o = some u then 1 else 0 := by
  rcases o with _ | w
  · simp [contractOwner]
  · by_cases hwv : w = v
    · subst w
      have hvu : v ≠ u.1 := Ne.symm u.2
      by_cases hp : parent = some u <;> simp [contractOwner, hvu, hp]
    · by_cases hwu : w = u.1
      · subst w
        simp [contractOwner, u.2]
      · simp [contractOwner, hwv, hwu, Subtype.ext_iff]

/-- Merge the physical block of an eliminated representative into its parent block;
for a root pivot (`parent = none`) its physical block becomes nonlive. -/
def LiveBlocks.contract {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (B : LiveBlocks n V) (v : V) (parent : Option {u : V // u ≠ v}) :
    LiveBlocks n {u : V // u ≠ v} where
  block u := if parent = some u then B.block u.1 ∪ B.block v else B.block u.1
  owner a := contractOwner v parent (B.owner a)
  mem_block_iff a u := by
    rw [contractOwner_eq_some_iff]
    by_cases hp : parent = some u
    · simp only [hp, if_pos, Finset.mem_union]
      rw [B.mem_block_iff, B.mem_block_iff]
      simp [hp, and_comm]
    · simp only [if_neg hp]
      rw [B.mem_block_iff]
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, hpu⟩)
        · exact h
        · exact absurd hpu hp
  nonempty u := by
    obtain ⟨a, ha⟩ := B.nonempty u.1
    refine ⟨a, ?_⟩
    by_cases hp : parent = some u
    · simp [hp, ha]
    · simp [hp, ha]

/-- The ambient quotient map for one unit pivot. -/
noncomputable def CompressionState.pivotMap {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (v : V) (y : Sum C V → ℤ) :
    (Fin n → ℤ) →ₗ[ℤ] (Sum C {u : V // u ≠ v} → ℤ) :=
  (unitElim v y).comp
    (st.basis.equivFun.toLinearMap.comp (st.Q.mkQ : (Fin n → ℤ) →ₗ[ℤ] _))

theorem CompressionState.pivotMap_surjective {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (v : V) (y : Sum C V → ℤ) : Function.Surjective (st.pivotMap v y) := by
  intro z
  obtain ⟨w, hw⟩ := unitElim_surjective v y z
  obtain ⟨q, hq⟩ := st.basis.equivFun.surjective w
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective st.Q q
  refine ⟨x, ?_⟩
  change unitElim v y (st.basis.equivFun (st.Q.mkQ x)) = z
  rw [hx, hq, hw]

/-- Contract one root/live unit row.  The new subgroup is the kernel of the explicit
elimination map, hence primitive; its quotient basis is the surviving coordinate
basis, and its physical blocks are merged exactly along the pivot edge. -/
noncomputable def CompressionState.pivot {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0) :
    CompressionState S P C {u : V // u ≠ v} := by
  let y : Sum C V → ℤ := st.basis.equivFun (Submodule.Quotient.mk r)
  let f := st.pivotMap v y
  have hf : Function.Surjective f := st.pivotMap_surjective v y
  let e : ((Fin n → ℤ) ⧸ LinearMap.ker f) ≃ₗ[ℤ]
      (Sum C {u : V // u ≠ v} → ℤ) := f.quotKerEquivOfSurjective hf
  let b : Module.Basis (Sum C {u : V // u ≠ v}) ℤ
      ((Fin n → ℤ) ⧸ LinearMap.ker f) :=
    (Pi.basisFun ℤ (Sum C {u : V // u ≠ v})).map e.symm
  refine
    { Q := LinearMap.ker f
      le_colLat := ?_
      primitive := ker_primitive f
      basis := b
      blocks := st.blocks.contract v parent
      live_coord := ?_ }
  · intro x hx
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    have hz : st.basis.equivFun (Submodule.Quotient.mk x) ∈
        LinearMap.ker (unitElim v y) := by
      rw [LinearMap.mem_ker]
      exact hx0
    have hy' : y (Sum.inr v) = 1 := hy
    rw [ker_unitElim v y hy', Submodule.mem_span_singleton] at hz
    obtain ⟨k, hk⟩ := hz
    have hquot : (Submodule.Quotient.mk x : (Fin n → ℤ) ⧸ st.Q) =
        k • (Submodule.Quotient.mk r : (Fin n → ℤ) ⧸ st.Q) := by
      apply st.basis.equivFun.injective
      simpa [y] using hk.symm
    have hdiff : x - k • r ∈ st.Q := by
      have hker : x - k • r ∈ LinearMap.ker st.Q.mkQ := by
        have hquot' : st.Q.mkQ x = k • st.Q.mkQ r := hquot
        rw [LinearMap.mem_ker, map_sub, map_smul, hquot']
        exact sub_self _
      rw [Submodule.ker_mkQ] at hker
      exact hker
    have h1 : x - k • r ∈ S.colLat P := st.le_colLat hdiff
    have h2 : k • r ∈ S.colLat P := (S.colLat P).smul_mem k hr
    have hadd := (S.colLat P).add_mem h1 h2
    convert hadd using 1 <;> module
  · intro a u
    change b.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr u) = _
    simp only [b, Module.Basis.map_repr, LinearEquiv.trans_apply,
      Pi.basisFun_repr, e, LinearMap.quotKerEquivOfSurjective_apply_mk]
    change unitElim v y
      (st.basis.equivFun (Submodule.Quotient.mk (Pi.single a 1))) (Sum.inr u) = _
    rw [unitElim_apply_right]
    change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr u.1) -
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) = _
    rw [st.live_coord, st.live_coord]
    have hlu := hlive u
    change st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
      (if parent = some u then -1 else 0) at hlu
    rw [hlu]
    change _ = if contractOwner v parent (st.blocks.owner a) = some u then 1 else 0
    exact contractOwner_indicator v parent (st.blocks.owner a) u

theorem CompressionState.pivot_core_coord {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0)
    (a : Fin n) (c : C) :
    (st.pivot r hr v parent hy hlive).basis.repr
        (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) =
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) -
        (if st.blocks.owner a = some v then 1 else 0) *
          st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c) := by
  simp only [CompressionState.pivot, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Pi.basisFun_repr]
  change unitElim v (st.basis.equivFun (Submodule.Quotient.mk r))
      (st.basis.equivFun (Submodule.Quotient.mk (Pi.single a 1))) (Sum.inl c) = _
  rw [unitElim_apply_left]
  change st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) -
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c) = _
  rw [st.live_coord]

/-- Coordinate update for an arbitrary ambient row under a pivot. -/
theorem CompressionState.pivot_core_coord_row {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0)
    (q : Fin n → ℤ) (c : C) :
    (st.pivot r hr v parent hy hlive).basis.repr
        (Submodule.Quotient.mk q) (Sum.inl c) =
      st.basis.repr (Submodule.Quotient.mk q) (Sum.inl c) -
        st.basis.repr (Submodule.Quotient.mk q) (Sum.inr v) *
          st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c) := by
  simp only [CompressionState.pivot, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Pi.basisFun_repr]
  change unitElim v (st.basis.equivFun (Submodule.Quotient.mk r))
      (st.basis.equivFun (Submodule.Quotient.mk q)) (Sum.inl c) = _
  rw [unitElim_apply_left]
  rfl

theorem CompressionState.pivot_live_coord_row {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0)
    (q : Fin n → ℤ) (u : {u : V // u ≠ v}) :
    (st.pivot r hr v parent hy hlive).basis.repr
        (Submodule.Quotient.mk q) (Sum.inr u) =
      st.basis.repr (Submodule.Quotient.mk q) (Sum.inr u.1) -
        st.basis.repr (Submodule.Quotient.mk q) (Sum.inr v) *
          st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) := by
  simp only [CompressionState.pivot, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Pi.basisFun_repr]
  change unitElim v (st.basis.equivFun (Submodule.Quotient.mk r))
      (st.basis.equivFun (Submodule.Quotient.mk q)) (Sum.inr u) = _
  rw [unitElim_apply_right]
  rfl

/-- A row with zero coefficient at the eliminated leaf is unchanged in every
surviving coordinate. -/
theorem CompressionState.pivot_repr_eq_of_zero {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0)
    (q : Fin n → ℤ)
    (hqv : st.basis.repr (Submodule.Quotient.mk q) (Sum.inr v) = 0) :
    (∀ c : C, (st.pivot r hr v parent hy hlive).basis.repr
      (Submodule.Quotient.mk q) (Sum.inl c) =
        st.basis.repr (Submodule.Quotient.mk q) (Sum.inl c)) ∧
    ∀ u : {u : V // u ≠ v},
      (st.pivot r hr v parent hy hlive).basis.repr
        (Submodule.Quotient.mk q) (Sum.inr u) =
        st.basis.repr (Submodule.Quotient.mk q) (Sum.inr u.1) := by
  constructor
  · intro c
    rw [st.pivot_core_coord_row r hr v parent hy hlive q c, hqv, zero_mul, sub_zero]
  · intro u
    rw [st.pivot_live_coord_row r hr v parent hy hlive q u, hqv, zero_mul, sub_zero]

/-- One unit substitution adds at most the core norm of its pivot row. -/
theorem CompressionState.pivot_coreBound {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (hr : r ∈ S.colLat P) (v : V)
    (parent : Option {u : V // u ≠ v})
    (hy : st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr v) = 1)
    (hlive : ∀ u : {u : V // u ≠ v},
      st.basis.equivFun (Submodule.Quotient.mk r) (Sum.inr u.1) =
        if parent = some u then -1 else 0)
    {M R : ℤ} (hM : st.CoreBound M)
    (hR : ∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)| ≤ R) :
    (st.pivot r hr v parent hy hlive).CoreBound (M + R) := by
  classical
  intro a
  simp_rw [st.pivot_core_coord r hr v parent hy hlive]
  calc
    ∑ c : C,
        |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) -
          (if st.blocks.owner a = some v then 1 else 0) *
            st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|
      ≤ ∑ c : C,
          (|st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| +
           |(if st.blocks.owner a = some v then 1 else 0) *
             st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) := by
        apply Finset.sum_le_sum
        intro c hc
        exact abs_sub _ _
    _ ≤ (∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)|) +
        ∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)| := by
          rw [Finset.sum_add_distrib]
          apply add_le_add (le_refl _)
          · apply Finset.sum_le_sum
            intro c hc
            by_cases h : st.blocks.owner a = some v <;> simp [h]
    _ ≤ M + R := add_le_add (hM a) hR

/-- Every abstract unit row can be oriented as a pivot `x_v` or `x_v-x_parent`.
Negating the underlying lattice row handles the two negative cases without changing
its core norm. -/
theorem CompressionState.exists_oriented_unit_pivot {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (r : Fin n → ℤ) (hr : r ∈ S.colLat P)
    (hu : IsUnitRelation
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u))) :
    ∃ (r' : Fin n → ℤ) (_ : r' ∈ S.colLat P) (v : V)
        (parent : Option {u : V // u ≠ v}),
      st.basis.equivFun (Submodule.Quotient.mk r') (Sum.inr v) = 1 ∧
      (∀ u : {u : V // u ≠ v},
        st.basis.equivFun (Submodule.Quotient.mk r') (Sum.inr u.1) =
          if parent = some u then -1 else 0) ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r') (Sum.inl c)|) =
        ∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)| := by
  classical
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, habr⟩ | ⟨a, ha⟩ | ⟨a, b, hab, habr⟩
  · refine ⟨r, hr, a, none, ?_, ?_, rfl⟩
    · have h := congrFun ha a
      change st.basis.repr (Submodule.Quotient.mk r) (Sum.inr a) = 1
      simpa [Pi.single_apply] using h
    · intro u
      have h := congrFun ha u.1
      change st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) = _
      simpa [Pi.single_apply, u.2] using h
  · let b' : {u : V // u ≠ a} := ⟨b, Ne.symm hab⟩
    refine ⟨r, hr, a, some b', ?_, ?_, rfl⟩
    · have h := congrFun habr a
      change st.basis.repr (Submodule.Quotient.mk r) (Sum.inr a) = 1
      simp [Pi.single_apply, hab] at h ⊢
      exact h
    · intro u
      have h := congrFun habr u.1
      change st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) = _
      by_cases hub : u.1 = b
      · have hub' : b' = u := Subtype.ext hub.symm
        simp [hub', Pi.single_apply, u.2, hub, Ne.symm hab] at h ⊢
        exact h
      · have hbu : b' ≠ u := fun h' => hub (congrArg Subtype.val h').symm
        simp [hbu, Pi.single_apply, u.2, hub] at h ⊢
        exact h
  · refine ⟨-r, (S.colLat P).neg_mem hr, a, none, ?_, ?_, ?_⟩
    · have h := congrFun ha a
      change st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr a) = 1
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      simpa [Pi.single_apply] using congrArg Neg.neg h
    · intro u
      have h := congrFun ha u.1
      change st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u.1) = _
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      have hn := congrArg Neg.neg h
      simpa [Pi.single_apply, u.2] using hn
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply, abs_neg]
  · let b' : {u : V // u ≠ a} := ⟨b, Ne.symm hab⟩
    refine ⟨-r, (S.colLat P).neg_mem hr, a, some b', ?_, ?_, ?_⟩
    · have h := congrFun habr a
      change st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr a) = 1
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      have hn := congrArg Neg.neg h
      simp [Pi.single_apply, hab] at hn ⊢
      exact hn
    · intro u
      have h := congrFun habr u.1
      change st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u.1) = _
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      have hn := congrArg Neg.neg h
      by_cases hub : u.1 = b
      · have hub' : b' = u := Subtype.ext hub.symm
        simp [hub', Pi.single_apply, u.2, hub, Ne.symm hab] at hn ⊢
        exact hn
      · have hbu : b' ≠ u := fun h' => hub (congrArg Subtype.val h').symm
        simp [hbu, Pi.single_apply, u.2, hub] at hn ⊢
        exact hn
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply, abs_neg]

/-! ### Encoding easy anchors for the common-cut lemma -/

/-- An easy-label set of size at least two can itself be presented as a common-cut
family.  A derangement `π` of the labels sends `j` to the configuration
`(j,{i,π(j)})`.  Hitting such a configuration necessarily selects the easy label
`j`; the distinguished elements and types are both injective. -/
theorem exists_easy_configuration_family {V : Type*} [Fintype V] [DecidableEq V]
    (i : V) (E : Finset V) (hi : i ∉ E) (hE : 2 ≤ E.card) :
    ∃ F : Finset (Configuration V),
      F.card = E.card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j ∈ T, j ∈ E := by
  classical
  have hcard : 2 ≤ Fintype.card (↥E) := by simpa using hE
  obtain ⟨π, hπ⟩ := exists_derangement (↥E) hcard
  let cf : ↥E → Configuration V := fun j =>
    { j := j.1
      τ := s(i, (π j).1)
      not_mem := by
        rw [Sym2.mem_iff]
        push_neg
        constructor
        · intro hji
          apply hi
          simpa [hji] using j.2
        · intro hjπ
          apply hπ j
          exact Subtype.ext hjπ.symm }
  have hcf : Function.Injective cf := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Configuration.j hjk
  let F : Finset (Configuration V) := Finset.univ.map ⟨cf, hcf⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · simp [F]
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    apply Subtype.ext
    exact hcd
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    have ht : s(i, (π j).1) = s(i, (π k).1) := hcd
    rcases Sym2.eq_iff.mp ht with h | h
    · apply congrArg cf
      exact π.injective (Subtype.ext h.2)
    · exact absurd h.1 (by
        intro hik
        apply hi
        simpa [hik] using (π k).2)
  · intro T c hc hhit
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    exact ⟨j.1, hhit.1, j.2⟩

/-- The canonical configuration attached to a proper label and its two-element
type. -/
theorem mem_equivMultiset_iff {V : Type*} (u : V) (z : Sym2 V) :
    u ∈ ((Sym2.equivMultiset V) z : Multiset V) ↔ u ∈ z := by
  induction z using Sym2.inductionOn with
  | hf a b =>
      change u ∈ ({a, b} : Multiset V) ↔ u ∈ s(a, b)
      simp [Sym2.mem_iff]

noncomputable def properConfiguration {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) : Configuration V where
  j := j
  τ := (Sym2.equivMultiset V).symm ⟨ν, hν⟩
  not_mem := by
    intro h
    apply hj
    have hm : ((Sym2.equivMultiset V)
        ((Sym2.equivMultiset V).symm ⟨ν, hν⟩) : Multiset V) = ν := congrArg Subtype.val
      ((Sym2.equivMultiset V).apply_symm_apply ⟨ν, hν⟩)
    have h' : j ∈ ((Sym2.equivMultiset V)
        ((Sym2.equivMultiset V).symm ⟨ν, hν⟩) : Multiset V) :=
      (mem_equivMultiset_iff j _).mpr h
    rwa [hm] at h'

@[simp] theorem properConfiguration_j {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) :
    (properConfiguration j ν hj hν).j = j := rfl

theorem properConfiguration_multiset {V : Type*} [DecidableEq V]
    (j : V) (ν : Multiset V) (hj : j ∉ ν) (hν : ν.card = 2) :
    (Sym2.equivMultiset V) (properConfiguration j ν hj hν).τ = ⟨ν, hν⟩ := by
  exact (Sym2.equivMultiset V).apply_symm_apply _

/-- A selected collection of proper labels with distinct types gives exactly the
configuration family required by the common-cut lemma. -/
theorem exists_proper_configuration_family {V : Type*} [Fintype V] [DecidableEq V]
    (J : Finset V) (ν : V → Multiset V)
    (hproper : ∀ j ∈ J, j ∉ ν j ∧ (ν j).card = 2)
    (hinj : Set.InjOn ν (J : Set V)) :
    ∃ F : Finset (Configuration V),
      F.card = J.card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      (∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j ∈ J, j ∈ T ∧ ∃ u ∈ T, u ∈ ν j) := by
  classical
  let cf : ↥J → Configuration V := fun j =>
    properConfiguration j.1 (ν j.1) (hproper j.1 j.2).1 (hproper j.1 j.2).2
  have hcf : Function.Injective cf := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Configuration.j hjk
  let F : Finset (Configuration V) := Finset.univ.map ⟨cf, hcf⟩
  refine ⟨F, by simp [F], ?_, ?_, ?_⟩
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    exact Subtype.ext hcd
  · intro c hc d hd hcd
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    apply Subtype.ext
    apply hinj j.2 k.2
    have he := congrArg (Sym2.equivMultiset V) hcd
    have hj := properConfiguration_multiset j.1 (ν j.1)
      (hproper j.1 j.2).1 (hproper j.1 j.2).2
    have hk := properConfiguration_multiset k.1 (ν k.1)
      (hproper k.1 k.2).1 (hproper k.1 k.2).2
    exact congrArg Subtype.val (hj.symm.trans (he.trans hk))
  · intro T c hc hhit
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hc
    refine ⟨j.1, j.2, hhit.1, ?_⟩
    obtain ⟨u, huT, huτ⟩ := hhit.2
    refine ⟨u, huT, ?_⟩
    have hm := properConfiguration_multiset j.1 (ν j.1)
      (hproper j.1 j.2).1 (hproper j.1 j.2).2
    have hu' : u ∈ ((Sym2.equivMultiset V)
        (properConfiguration j.1 (ν j.1) (hproper j.1 j.2).1
          (hproper j.1 j.2).2).τ : Multiset V) :=
      (mem_equivMultiset_iff u _).mpr huτ
    rwa [congrArg Subtype.val hm] at hu'

/-! ### Departing systems for a round -/

abbrev OrderedDistinct (V : Type*) := {ij : V × V // ij.1 ≠ ij.2}

/-- One chosen departing rectangle pair for every ordered pair of live blocks. -/
structure DepartingSystem {p n : ℕ} {S : MinimalNUS p n} (P : S.Pairing)
    {V : Type*} [Fintype V] [DecidableEq V] (B : LiveBlocks n V) where
  t : OrderedDistinct V → Sym2 (Fin n)
  mem_rectangle : ∀ e,
    t e ∈ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2)
  leaves_rectangle : ∀ e,
    P.μ (t e) ∉ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2)

/-- Blocks below `⌊log₂ p / 3⌋` satisfy the clean-rectangle power hypothesis. -/
theorem light_blocks_power_lt {n p : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (B : LiveBlocks n V) (hp : 64 ≤ p)
    (hlight : ∀ v, (B.block v).card < Nat.log 2 p / 3) :
    ∀ e : OrderedDistinct V,
      2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) < p := by
  intro e
  let ell := Nat.log 2 p
  have hell : 6 ≤ ell := by
    have hmono := Nat.log_mono_right (b := 2) hp
    norm_num at hmono ⊢
    exact hmono
  have hexp : (B.block e.1.1).card + (B.block e.1.2).card - 2 < ell := by
    have h1 := hlight e.1.1
    have h2 := hlight e.1.2
    dsimp [ell] at h1 h2 ⊢
    omega
  have hpow : 2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) <
      2 ^ ell := Nat.pow_lt_pow_right (by norm_num) hexp
  exact hpow.trans_le (Nat.pow_log_le_self 2 (by omega))

/-- The clean-rectangle lemma supplies all departing rows used in one round. -/
noncomputable def exists_departingSystem {p n : ℕ} [Fact p.Prime]
    (S : MinimalNUS p n) (P : S.Pairing)
    {V : Type*} [Fintype V] [DecidableEq V] (B : LiveBlocks n V)
    (hlight : ∀ e : OrderedDistinct V,
      2 ^ ((B.block e.1.1).card + (B.block e.1.2).card - 2) < p) :
    Nonempty (DepartingSystem P B) := by
  have hex : ∀ e : OrderedDistinct V,
      ∃ t ∈ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2),
        P.μ t ∉ MinimalNUS.rectangle (B.block e.1.1) (B.block e.1.2) := by
    intro e
    apply exists_departing_pair S P
    · exact B.nonempty e.1.1
    · exact B.nonempty e.1.2
    · exact B.disjoint e.2
    · exact hlight e
  choose t ht hout using hex
  exact ⟨⟨t, ht, hout⟩⟩

namespace DepartingSystem

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {B : LiveBlocks n V}

def row (D : DepartingSystem P B) (e : OrderedDistinct V) : Fin n → ℤ :=
  S.rho P (D.t e)

def liveType (D : DepartingSystem P B) (e : OrderedDistinct V) : Multiset V :=
  liveLabels B (P.μ (D.t e))

theorem row_mem_colLat (D : DepartingSystem P B) (e : OrderedDistinct V) :
    D.row e ∈ S.colLat P :=
  Submodule.subset_span ⟨D.t e, rfl⟩

theorem row_classification (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V) :
    IsUnitRelation (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) ∨
      IsEasyDeparture e.1.1 e.1.2 (D.liveType e) ∨
      IsProperDeparture e.1.1 e.1.2 (D.liveType e) := by
  exact st.projected_departing_classification e.2
    (D.mem_rectangle e) (D.leaves_rectangle e)

theorem row_unit_of_mem_right (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) :
    IsUnitRelation (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  change IsUnitRelation (fun v => st.projectedRow (D.t e) (Sum.inr v))
  rw [st.projectedRow_live e.2 (D.mem_rectangle e)]
  exact departingLive_unit_of_mem_right e.1.1 e.1.2 (D.liveType e)
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem row_unit_of_mem_left (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.1 ∈ D.liveType e) :
    IsUnitRelation (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  change IsUnitRelation (fun v => st.projectedRow (D.t e) (Sum.inr v))
  rw [st.projectedRow_live e.2 (D.mem_rectangle e)]
  exact departingLive_unit_of_mem_left e.1.1 e.1.2 (D.liveType e)
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem row_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (D : DepartingSystem P st.blocks) (e : OrderedDistinct V) :
    ∑ c : C, |st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)| ≤
      4 * M :=
  st.projectedRow_core_norm_le hM (D.t e)

theorem row_sub_mem_colLat (D : DepartingSystem P B)
    (e e' : OrderedDistinct V) :
    D.row e - D.row e' ∈ S.colLat P :=
  (S.colLat P).sub_mem (D.row_mem_colLat e) (D.row_mem_colLat e')

/-- Same-type proper rows differ by exactly the unit vector between their labels. -/
theorem row_sub_live_eq (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e e' : OrderedDistinct V)
    (hanchor : e.1.1 = e'.1.1) (htype : D.liveType e = D.liveType e') :
    (fun v => st.basis.repr
      (Submodule.Quotient.mk (D.row e - D.row e')) (Sum.inr v)) =
      Pi.single e.1.2 1 - Pi.single e'.1.2 1 := by
  have he := st.projectedRow_live e.2 (D.mem_rectangle e)
  have he' := st.projectedRow_live e'.2 (D.mem_rectangle e')
  rw [Submodule.Quotient.mk_sub, map_sub]
  ext v
  simp only [Finsupp.sub_apply]
  change st.projectedRow (D.t e) (Sum.inr v) -
      st.projectedRow (D.t e') (Sum.inr v) = _
  rw [congrFun he v, congrFun he' v]
  change liveLabels st.blocks (P.μ (D.t e)) =
    liveLabels st.blocks (P.μ (D.t e')) at htype
  rw [hanchor, htype]
  exact congrFun (departingLive_sub_same_type e'.1.1 e.1.2 e'.1.2
    (D.liveType e')) v

/-- The core part of a same-type difference costs at most `8M`. -/
theorem row_sub_core_norm_le (st : CompressionState S P C V) {M : ℤ}
    (hM : st.CoreBound M) (D : DepartingSystem P st.blocks)
    (e e' : OrderedDistinct V) :
    ∑ c : C, |st.basis.repr
      (Submodule.Quotient.mk (D.row e - D.row e')) (Sum.inl c)| ≤ 8 * M := by
  classical
  rw [Submodule.Quotient.mk_sub, map_sub]
  calc
    ∑ c : C, |(st.basis.repr (Submodule.Quotient.mk (D.row e)) -
        st.basis.repr (Submodule.Quotient.mk (D.row e'))) (Sum.inl c)|
      ≤ ∑ c : C,
          (|st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)| +
           |st.basis.repr (Submodule.Quotient.mk (D.row e')) (Sum.inl c)|) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [Finsupp.sub_apply]
        exact abs_sub _ _
    _ = (∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)|) +
        ∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (D.row e')) (Sum.inl c)| := by
        rw [Finset.sum_add_distrib]
    _ ≤ 4 * M + 4 * M := add_le_add (D.row_core_norm_le st hM e)
      (D.row_core_norm_le st hM e')
    _ = 8 * M := by ring

/-- An easy departing row whose label is promoted is an actual unit row in the
promoted state, with the original collision vector retained as its witness. -/
theorem promoted_row_unit_of_easy (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (heasy : IsEasyDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hlive := st.projectedRow_live e.2 (D.mem_rectangle e)
  have hu := easy_after_promote_unit heasy T hiT hjT
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => departingLive e.1.1 e.1.2 (D.liveType e) v.1) by
    funext v
    rw [st.promote_live_coord_row]
    exact congrFun hlive v.1]
  exact hu

/-- A proper departing row from a configuration hit by the sample is an actual unit
row after promotion. -/
theorem promoted_row_unit_of_proper (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hproper : IsProperDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T)
    (hhit : ∃ u ∈ T, u ∈ D.liveType e) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hlive := st.projectedRow_live e.2 (D.mem_rectangle e)
  have hu := proper_after_promote_unit hproper T hiT hjT hhit
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => departingLive e.1.1 e.1.2 (D.liveType e) v.1) by
    funext v
    rw [st.promote_live_coord_row]
    exact congrFun hlive v.1]
  exact hu

/-- The promoted easy row also satisfies the round's uniform `8M` core budget. -/
theorem promoted_row_core_norm_le_eight_mul (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (T : Finset V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M) :
    ∑ c : Sum C {v : V // v ∈ T},
      |(st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inl c)|
        ≤ 8 * M := by
  exact st.promote_projectedRow_core_norm_le_eight_mul T hM hM1 (D.t e)

/-- A direct row remains a unit row after any promotion that leaves its anchor live. -/
theorem promoted_row_unit_of_mem_right (st : CompressionState S P C V)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) (T : Finset V) (hiT : e.1.1 ∉ T) :
    IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) := by
  have hu := D.row_unit_of_mem_right st e hmem
  have hi : st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr e.1.1) = 1 := by
    change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
    rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
    exact departingLive_anchor_of_mem_right e.1.1 e.1.2 (D.liveType e) e.2
      (liveLabels_card_le_two st.blocks _) hmem
      (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))
  have hr := unitRelation_restrict_at_one e.1.1 hu hi T hiT
  rw [show (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)) =
      (fun v => st.basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v.1)) by
        funext v
        exact st.promote_live_coord_row T (D.row e) v]
  exact hr

end DepartingSystem

/-! ### Anchor bookkeeping for a contraction round -/

abbrev OtherLabel {V : Type*} (i : V) := {j : V // j ≠ i}

def anchorPair {V : Type*} (i : V) (j : OtherLabel i) : OrderedDistinct V :=
  ⟨(i, j.1), Ne.symm j.2⟩

def DepartingSystem.IsDirectAnchor {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) : Prop :=
  ∃ j : OtherLabel i, j.1 ∈ D.liveType (anchorPair i j)

noncomputable def DepartingSystem.easyLabels {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (OtherLabel i) := by
  classical
  exact Finset.univ.filter fun j =>
    IsEasyDeparture i j.1 (D.liveType (anchorPair i j))

noncomputable def DepartingSystem.properLabels {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (OtherLabel i) := by
  classical
  exact Finset.univ.filter fun j =>
    IsProperDeparture i j.1 (D.liveType (anchorPair i j))

noncomputable def DepartingSystem.properTypes {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {V : Type*} [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    Finset (Multiset V) := by
  classical
  exact (D.properLabels i).image fun j => D.liveType (anchorPair i j)

/-- Easy labels of an anchor form a common-cut family whose hit selects an easy
label. -/
theorem DepartingSystem.exists_easy_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) (h2 : 2 ≤ (D.easyLabels i).card) :
    ∃ F : Finset (Configuration V),
      F.card = (D.easyLabels i).card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j : OtherLabel i, j ∈ D.easyLabels i ∧ j.1 ∈ T := by
  classical
  let E : Finset V := (D.easyLabels i).image Subtype.val
  have hEcard : E.card = (D.easyLabels i).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Subtype.ext hab
  have hiE : i ∉ E := by
    intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact j.2 hji
  obtain ⟨F, hcard, hjinj, hτinj, hhit⟩ :=
    exists_easy_configuration_family i E hiE (by simpa [hEcard] using h2)
  refine ⟨F, hcard.trans hEcard, hjinj, hτinj, ?_⟩
  intro T c hcF hcHit
  obtain ⟨v, hvT, hvE⟩ := hhit T c hcF hcHit
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvE
  exact ⟨j, hj, hvT⟩

/-- Choosing one proper label for every distinct type produces the proper-anchor
configuration family used by the common-cut lemma. -/
theorem DepartingSystem.exists_proper_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) :
    ∃ F : Finset (Configuration V),
      F.card = (D.properTypes i).card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        ∃ j : OtherLabel i, j ∈ D.properLabels i ∧ j.1 ∈ T ∧
          ∃ u ∈ T, u ∈ D.liveType (anchorPair i j) := by
  classical
  let Types := D.properTypes i
  have hex : ∀ t : ↥Types, ∃ j : OtherLabel i,
      j ∈ D.properLabels i ∧ D.liveType (anchorPair i j) = t.1 := by
    intro t
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp t.2
    exact ⟨j, hj, heq⟩
  choose sel hselP hsel using hex
  have hselinj : Function.Injective sel := by
    intro t u htu
    apply Subtype.ext
    rw [← hsel t, ← hsel u, htu]
  have hproper : ∀ t : ↥Types,
      IsProperDeparture i (sel t).1 (D.liveType (anchorPair i (sel t))) := by
    intro t
    simpa only [DepartingSystem.properLabels, Finset.mem_filter, Finset.mem_univ,
      true_and] using hselP t
  let cf : ↥Types → Configuration V := fun t =>
    properConfiguration (sel t).1 (D.liveType (anchorPair i (sel t)))
      (hproper t).2.1 (hproper t).2.2
  have hcfinj : Function.Injective cf := by
    intro t u htu
    apply hselinj
    apply Subtype.ext
    exact congrArg Configuration.j htu
  let F : Finset (Configuration V) := Finset.univ.map ⟨cf, hcfinj⟩
  refine ⟨F, by simp [F, Types], ?_, ?_, ?_⟩
  · intro c hc d hd hcd
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hd
    exact congrArg cf (hselinj (Subtype.ext hcd))
  · intro c hc d hd hcd
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hd
    apply congrArg cf
    apply Subtype.ext
    have he := congrArg (Sym2.equivMultiset V) hcd
    have ht := properConfiguration_multiset (sel t).1
      (D.liveType (anchorPair i (sel t))) (hproper t).2.1 (hproper t).2.2
    have hu := properConfiguration_multiset (sel u).1
      (D.liveType (anchorPair i (sel u))) (hproper u).2.1 (hproper u).2.2
    have hv := congrArg Subtype.val (ht.symm.trans (he.trans hu))
    simpa [hsel t, hsel u] using hv
  · intro T c hc hhit
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hc
    refine ⟨sel t, hselP t, hhit.1, ?_⟩
    obtain ⟨u, huT, huτ⟩ := hhit.2
    refine ⟨u, huT, ?_⟩
    have hm := properConfiguration_multiset (sel t).1
      (D.liveType (anchorPair i (sel t))) (hproper t).2.1 (hproper t).2.2
    have hu' : u ∈ ((Sym2.equivMultiset V) (cf t).τ : Multiset V) :=
      (mem_equivMultiset_iff u _).mpr huτ
    rwa [congrArg Subtype.val hm] at hu'

def DepartingSystem.SampleCoversAnchor {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {V : Type*} [Fintype V] [DecidableEq V]
    {B : LiveBlocks n V} (D : DepartingSystem P B) (i : V) (T : Finset V) : Prop :=
  (∃ j : OtherLabel i, j ∈ D.easyLabels i ∧ j.1 ∈ T) ∨
  ∃ j : OtherLabel i, j ∈ D.properLabels i ∧ j.1 ∈ T ∧
    ∃ u ∈ T, u ∈ D.liveType (anchorPair i j)

/-- Either large easy-label set or many proper types supplies a common-cut family of
density `1/8`; every hit of that family covers the anchor after promotion. -/
theorem DepartingSystem.exists_large_anchor_family {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {V : Type*}
    [Fintype V] [DecidableEq V] {B : LiveBlocks n V}
    (D : DepartingSystem P B) (i : V) (hm : 16 ≤ Fintype.card V)
    (hlarge : Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
      Fintype.card V ≤ 8 * (D.properTypes i).card) :
    ∃ F : Finset (Configuration V),
      (1 / 8 : ℝ) * Fintype.card V ≤ F.card ∧
      Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
      Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
      ∀ (T : Finset V) (c : Configuration V), c ∈ F → Hits T c →
        D.SampleCoversAnchor i T := by
  classical
  rcases hlarge with heasy | hproper
  · have h2 : 2 ≤ (D.easyLabels i).card := by omega
    obtain ⟨F, hcard, hj, hτ, hhit⟩ := D.exists_easy_anchor_family i h2
    refine ⟨F, ?_, hj, hτ, ?_⟩
    · rw [hcard]
      have he : (Fintype.card V : ℝ) ≤ 8 * ((D.easyLabels i).card : ℝ) := by
        exact_mod_cast heasy
      norm_num at ⊢
      linarith
    · intro T c hc hh
      exact Or.inl (hhit T c hc hh)
  · obtain ⟨F, hcard, hj, hτ, hhit⟩ := D.exists_proper_anchor_family i
    refine ⟨F, ?_, hj, hτ, ?_⟩
    · rw [hcard]
      have hp : (Fintype.card V : ℝ) ≤ 8 * ((D.properTypes i).card : ℝ) := by
        exact_mod_cast hproper
      norm_num at ⊢
      linarith
    · intro T c hc hh
      exact Or.inr (hhit T c hc hh)

/-! ### The proof-relevant unit graph -/

/-- A lattice row realizes the oriented edge `x → y` when its live part is the
corresponding unit vector or unit difference. -/
def CompressionState.IsEdgeRow {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (r : Fin n → ℤ) : Option V → Option V → Prop
  | none, none => False
  | none, some b =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) = Pi.single b 1
  | some a, none =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) = -(Pi.single a 1)
  | some a, some b =>
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) =
        Pi.single a 1 - Pi.single b 1

theorem CompressionState.isEdgeRow_symm {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V)
    (r : Fin n → ℤ) (x y : Option V) :
    st.IsEdgeRow r x y → st.IsEdgeRow (-r) y x := by
  rcases x with _ | a <;> rcases y with _ | b
  · simp [CompressionState.IsEdgeRow]
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.neg_apply, Pi.single_apply,
      Pi.sub_apply] at hu ⊢
    rw [hu]
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.neg_apply, Pi.single_apply] at hu ⊢
    rw [hu]
    split <;> ring
  · intro h
    change (fun u => st.basis.repr (Submodule.Quotient.mk (-r)) (Sum.inr u)) = _
    rw [Submodule.Quotient.mk_neg, map_neg]
    ext u
    have hu := congrFun h u
    simp only [Finsupp.neg_apply, Pi.neg_apply, Pi.single_apply,
      Pi.sub_apply] at hu ⊢
    rw [hu]
    ring

/-- The graph of all unit rows whose core norm is at most `R`.  Defining it by
existence retains an actual row witness for every edge chosen by Lemma 3.2. -/
noncomputable def CompressionState.unitGraph {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) (R : ℤ) :
    SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun x y => ∃ r : Fin n → ℤ,
    r ∈ S.colLat P ∧
    (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R ∧
    st.IsEdgeRow r x y

theorem CompressionState.unitGraph_adj_of_row {p n : ℕ} {S : MinimalNUS p n}
    {P : S.Pairing} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (st : CompressionState S P C V) {R : ℤ}
    {r : Fin n → ℤ} (hr : r ∈ S.colLat P)
    (hR : (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R)
    {x y : Option V} (hxy : x ≠ y) (hedge : st.IsEdgeRow r x y) :
    (st.unitGraph R).Adj x y := by
  rw [CompressionState.unitGraph, SimpleGraph.fromRel_adj]
  exact ⟨hxy, Or.inl ⟨r, hr, hR, hedge⟩⟩

theorem CompressionState.exists_row_of_unitGraph_adj {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} {x y : Option V}
    (hxy : (st.unitGraph R).Adj x y) :
    ∃ r : Fin n → ℤ, r ∈ S.colLat P ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R ∧
      st.IsEdgeRow r x y := by
  rw [CompressionState.unitGraph, SimpleGraph.fromRel_adj] at hxy
  rcases hxy.2 with ⟨r, hr, hR, he⟩ | ⟨r, hr, hR, he⟩
  · exact ⟨r, hr, hR, he⟩
  · refine ⟨-r, (S.colLat P).neg_mem hr, ?_, st.isEdgeRow_symm r y x he⟩
    simpa only [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply, abs_neg] using hR

/-- An edge directed from a live child supplies exactly the oriented integral pivot
data expected by `CompressionState.pivot`.  A root edge is negated when necessary;
a live edge is directed toward its parent. -/
theorem CompressionState.exists_pivot_of_unitGraph_adj {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} (v : V) (y : Option V)
    (hvy : (st.unitGraph R).Adj (some v) y) :
    ∃ (r : Fin n → ℤ) (hr : r ∈ S.colLat P)
        (parent : Option {u : V // u ≠ v}),
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
      (∀ u : {u : V // u ≠ v},
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
          if parent = some u then -1 else 0) ∧
      Option.map Subtype.val parent = y ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R := by
  classical
  obtain ⟨q, hq, hqR, hedge⟩ := st.exists_row_of_unitGraph_adj hvy
  rcases y with _ | w
  · refine ⟨-q, (S.colLat P).neg_mem hq, none, ?_, ?_, rfl, ?_⟩
    · have h := congrFun hedge v
      change st.basis.repr (Submodule.Quotient.mk (-q)) (Sum.inr v) = 1
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      simpa [CompressionState.IsEdgeRow, Pi.single_apply] using congrArg Neg.neg h
    · intro u
      have h := congrFun hedge u.1
      change st.basis.repr (Submodule.Quotient.mk (-q)) (Sum.inr u.1) = _
      rw [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply]
      have hn := congrArg Neg.neg h
      simpa [CompressionState.IsEdgeRow, Pi.single_apply, u.2] using hn
    · simpa only [Submodule.Quotient.mk_neg, map_neg, Finsupp.neg_apply,
        abs_neg] using hqR
  · have hvw : v ≠ w := by
      intro e
      subst w
      exact hvy.ne rfl
    let w' : {u : V // u ≠ v} := ⟨w, Ne.symm hvw⟩
    refine ⟨q, hq, some w', ?_, ?_, rfl, hqR⟩
    · have h := congrFun hedge v
      simpa [CompressionState.IsEdgeRow, Pi.single_apply, hvw] using h
    · intro u
      have h := congrFun hedge u.1
      by_cases huw : u.1 = w
      · have huw' : u = w' := Subtype.ext huw
        subst u
        simpa [CompressionState.IsEdgeRow, Pi.single_apply, hvw, w'] using h
      · have hune : some w' ≠ some u := by
          intro e
          exact huw (congrArg Subtype.val (Option.some.inj e)).symm
        simpa [CompressionState.IsEdgeRow, Pi.single_apply, u.2, huw, hune] using h

/-- Each abstract unit relation supplies an edge of the proof-relevant unit graph. -/
theorem CompressionState.exists_unitGraph_neighbor {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} (r : Fin n → ℤ)
    (hr : r ∈ S.colLat P)
    (hR : (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R)
    (hu : IsUnitRelation
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u))) :
    ∃ x y : Option V, (st.unitGraph R).Adj x y := by
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, habr⟩ | ⟨a, ha⟩ | ⟨a, b, hab, habr⟩
  · exact ⟨none, some a, st.unitGraph_adj_of_row hr hR (by simp)
      (by simpa [CompressionState.IsEdgeRow] using ha)⟩
  · exact ⟨some a, some b, st.unitGraph_adj_of_row hr hR (by simp [hab])
      (by simpa [CompressionState.IsEdgeRow] using habr)⟩
  · exact ⟨some a, none, st.unitGraph_adj_of_row hr hR (by simp)
      (by simpa [CompressionState.IsEdgeRow] using ha)⟩
  · exact ⟨some b, some a, st.unitGraph_adj_of_row hr hR
      (by
        intro hba
        exact (Ne.symm hab) (Option.some.inj hba))
      (by
        change (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) =
          Pi.single b 1 - Pi.single a 1
        rw [habr]
        ext u
        simp only [Pi.neg_apply, Pi.sub_apply]
        ring)⟩

/-- If a bounded unit row has coefficient `1` at a specified live coordinate, the
corresponding unit-graph edge is incident with that coordinate. -/
theorem CompressionState.exists_unitGraph_neighbor_at {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {R : ℤ} (r : Fin n → ℤ)
    (hr : r ∈ S.colLat P)
    (hR : (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R)
    (i : V)
    (hu : IsUnitRelation
      (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)))
    (hi : st.basis.repr (Submodule.Quotient.mk r) (Sum.inr i) = 1) :
    ∃ y : Option V, (st.unitGraph R).Adj (some i) y := by
  let w : V → ℤ := fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)
  change w i = 1 at hi
  rcases hu with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
  · have hai : a = i := by
      by_contra h
      have := congrFun ha i
      simp [w, Pi.single_apply, h] at this hi
      omega
    subst a
    exact ⟨none, (st.unitGraph_adj_of_row hr hR (by simp)
      (by simpa [CompressionState.IsEdgeRow, w] using ha)).symm⟩
  · have hai : a = i := by
      by_contra hia
      have hbi : b ≠ i := by
        intro hbi
        subst b
        have hv := congrFun ha i
        simp [w, Pi.single_apply, hia] at hv hi
        omega
      have hv := congrFun ha i
      simp [w, Pi.single_apply, hia, hbi] at hv hi
      omega
    subst a
    exact ⟨some b, st.unitGraph_adj_of_row hr hR (by simp [hab])
      (by simpa [CompressionState.IsEdgeRow, w] using ha)⟩
  · have hv := congrFun ha i
    exfalso
    by_cases hai : a = i <;> simp [w, Pi.single_apply, hai] at hv hi <;> omega
  · have hbi : b = i := by
      by_contra hbi
      have hai : a ≠ i := by
        intro hai
        subst a
        have hv := congrFun ha i
        simp [w, Pi.single_apply, hbi] at hv hi
        omega
      have hv := congrFun ha i
      simp [w, Pi.single_apply, hai, hbi] at hv hi
      omega
    subst b
    exact ⟨some a, st.unitGraph_adj_of_row hr hR
      (by intro e; exact hab (Option.some.inj e).symm)
      (by
        change (fun u => st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u)) =
          Pi.single i 1 - Pi.single a 1
        rw [ha]
        ext u
        simp only [Pi.neg_apply, Pi.sub_apply]
        ring)⟩

/-- Immediate cancellation at the label gives a bounded unit edge incident with the
anchor. -/
theorem DepartingSystem.unitGraph_neighbor_anchor_of_mem_right {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) :
    ∃ y, (st.unitGraph (8 * M)).Adj (some e.1.1) y := by
  apply st.exists_unitGraph_neighbor_at (D.row e) (D.row_mem_colLat e)
    (le_trans (D.row_core_norm_le st hM e) (by
      have hM0 := st.coreBound_nonneg hM
      linarith)) e.1.1 (D.row_unit_of_mem_right st e hmem)
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_mem_right e.1.1 e.1.2 (D.liveType e) e.2
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

/-- Immediate cancellation at the anchor gives a bounded unit edge incident with the
label. -/
theorem DepartingSystem.unitGraph_neighbor_label_of_mem_left {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.1 ∈ D.liveType e) :
    ∃ y, (st.unitGraph (8 * M)).Adj (some e.1.2) y := by
  apply st.exists_unitGraph_neighbor_at (D.row e) (D.row_mem_colLat e)
    (le_trans (D.row_core_norm_le st hM e) (by
      have hM0 := st.coreBound_nonneg hM
      linarith)) e.1.2 (D.row_unit_of_mem_left st e hmem)
  change st.projectedRow (D.t e) (Sum.inr e.1.2) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.2]
  exact departingLive_label_of_mem_left e.1.1 e.1.2 (D.liveType e) e.2
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

/-- A promoted bounded unit row with coefficient one at `i` produces an edge incident
with `i` in the promoted unit graph. -/
theorem DepartingSystem.promoted_unitGraph_neighbor_at {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V) (T : Finset V)
    (i : {v : V // v ∉ T})
    (hu : IsUnitRelation (fun v : {v : V // v ∉ T} =>
      (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e)) (Sum.inr v)))
    (hi : (st.promote T).basis.repr (Submodule.Quotient.mk (D.row e))
      (Sum.inr i) = 1) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some i) y := by
  exact (st.promote T).exists_unitGraph_neighbor_at (D.row e) (D.row_mem_colLat e)
    (D.promoted_row_core_norm_le_eight_mul st e T hM hM1) i hu hi

theorem DepartingSystem.promoted_neighbor_of_direct {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hmem : e.1.2 ∈ D.liveType e) (T : Finset V) (hiT : e.1.1 ∉ T) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_mem_right st e hmem T hiT)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_mem_right e.1.1 e.1.2 (D.liveType e) e.2
    (liveLabels_card_le_two st.blocks _) hmem
    (liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e))

theorem DepartingSystem.promoted_neighbor_of_easy {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (heasy : IsEasyDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_easy st e heasy T hiT hjT)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_not_mem e.1.1 e.1.2 (D.liveType e) e.2 heasy.1

theorem DepartingSystem.promoted_neighbor_of_proper {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (D : DepartingSystem P st.blocks) (e : OrderedDistinct V)
    (hproper : IsProperDeparture e.1.1 e.1.2 (D.liveType e))
    (T : Finset V) (hiT : e.1.1 ∉ T) (hjT : e.1.2 ∈ T)
    (hhit : ∃ u ∈ T, u ∈ D.liveType e) :
    ∃ y, ((st.promote T).unitGraph (8 * M)).Adj (some ⟨e.1.1, hiT⟩) y := by
  apply D.promoted_unitGraph_neighbor_at st hM hM1 e T ⟨e.1.1, hiT⟩
    (D.promoted_row_unit_of_proper st e hproper T hiT hjT hhit)
  rw [st.promote_live_coord_row]
  change st.projectedRow (D.t e) (Sum.inr e.1.1) = 1
  rw [congrFun (st.projectedRow_live e.2 (D.mem_rectangle e)) e.1.1]
  exact departingLive_anchor_of_not_mem e.1.1 e.1.2 (D.liveType e) e.2 hproper.1

/-- The complementary branch of the anchor dichotomy admits one common sample of
size `O(√m)` after which at most `m/8` remaining vertices are isolated. -/
noncomputable def CompressionState.isolatedLive {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w, ¬(st.unitGraph R).Adj (some v) w

theorem exists_high_anchor_sample :
    ∃ (D₀ : ℝ) (m₀ : ℕ), 0 < D₀ ∧
      ∀ {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} {C V : Type}
        [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
        (st : CompressionState S P C V) {M : ℤ}, st.CoreBound M → 1 ≤ M →
        (D : DepartingSystem P st.blocks) →
        max m₀ 16 ≤ Fintype.card V →
        (∀ i, ¬D.IsDirectAnchor i →
          Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
          Fintype.card V ≤ 8 * (D.properTypes i).card) →
        ∃ T : Finset V, (T.card : ℝ) ≤ D₀ * Real.sqrt (Fintype.card V) ∧
          8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V := by
  classical
  obtain ⟨D₀, m₀, hD₀, hcut⟩ := common_cut (1 / 8 : ℝ) (by norm_num)
  refine ⟨D₀, m₀, hD₀, ?_⟩
  intro p n S P C V _ _ _ _ st M hM hM1 D hm hall
  have hm0 : m₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hm
  have hm16 : 16 ≤ Fintype.card V := le_trans (le_max_right _ _) hm
  by_cases hndex : ∃ i : V, ¬D.IsDirectAnchor i
  · obtain ⟨i₀, hi₀⟩ := hndex
    obtain ⟨F₀, hF₀card, hF₀j, hF₀τ, hF₀hit⟩ :=
      D.exists_large_anchor_family i₀ hm16 (hall i₀ hi₀)
    have hfamilies : ∀ i : V, ∃ F : Finset (Configuration V),
        (1 / 8 : ℝ) * Fintype.card V ≤ F.card ∧
        Set.InjOn Configuration.j (F : Set (Configuration V)) ∧
        Set.InjOn Configuration.τ (F : Set (Configuration V)) ∧
        (¬D.IsDirectAnchor i → ∀ T c, c ∈ F → Hits T c →
          D.SampleCoversAnchor i T) := by
      intro i
      by_cases hdi : D.IsDirectAnchor i
      · exact ⟨F₀, hF₀card, hF₀j, hF₀τ, fun h => (h hdi).elim⟩
      · obtain ⟨F, hc, hj, hτ, hhit⟩ :=
          D.exists_large_anchor_family i hm16 (hall i hdi)
        exact ⟨F, hc, hj, hτ, fun _ => hhit⟩
    choose Fam hFam using hfamilies
    let ev : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let 𝓕 : Fin (Fintype.card V) → Finset (Configuration V) :=
      fun k => Fam (ev.symm k)
    obtain ⟨T, hTcard, Bad, hBad, hhit⟩ :=
      hcut V inferInstance inferInstance (Fintype.card V) 𝓕 hm0 (le_refl _)
        (fun k => (hFam (ev.symm k)).1)
        (fun k => (hFam (ev.symm k)).2.1)
        (fun k => (hFam (ev.symm k)).2.2.1)
    refine ⟨T, hTcard, ?_⟩
    let Iso := (st.promote T).isolatedLive (8 * M)
    let emb : {v : V // v ∉ T} ↪ Fin (Fintype.card V) :=
      ⟨fun v => ev v.1, fun a b h => Subtype.ext (ev.injective h)⟩
    have hsub : Iso.image emb ⊆ Bad := by
      intro k hk
      obtain ⟨v, hvIso, rfl⟩ := Finset.mem_image.mp hk
      by_contra hkBad
      let i : V := v.1
      have hviso : ∀ y, ¬((st.promote T).unitGraph (8 * M)).Adj (some v) y := by
        simpa [Iso, CompressionState.isolatedLive] using hvIso
      by_cases hdi : D.IsDirectAnchor i
      · obtain ⟨j, hj⟩ := hdi
        obtain ⟨y, hy⟩ := D.promoted_neighbor_of_direct st hM hM1
          (anchorPair i j) hj T v.2
        exact hviso y hy
      · have hfamilyHit := hhit (ev i) hkBad
        obtain ⟨c, hcF, hcHit⟩ := hfamilyHit
        have hcF' : c ∈ Fam i := by simpa [𝓕] using hcF
        have hcover := (hFam i).2.2.2 hdi T c hcF' hcHit
        rcases hcover with ⟨j, hjEasy, hjT⟩ | ⟨j, hjProper, hjT, hu, huT, huν⟩
        · have heasy : IsEasyDeparture i j.1
              (D.liveType (anchorPair i j)) := by
            simpa only [DepartingSystem.easyLabels, Finset.mem_filter,
              Finset.mem_univ, true_and] using hjEasy
          obtain ⟨y, hy⟩ := D.promoted_neighbor_of_easy st hM hM1
            (anchorPair i j) heasy T v.2 hjT
          exact hviso y hy
        · have hproper : IsProperDeparture i j.1
              (D.liveType (anchorPair i j)) := by
            simpa only [DepartingSystem.properLabels, Finset.mem_filter,
              Finset.mem_univ, true_and] using hjProper
          obtain ⟨y, hy⟩ := D.promoted_neighbor_of_proper st hM hM1
            (anchorPair i j) hproper T v.2 hjT ⟨hu, huT, huν⟩
          exact hviso y hy
    have hcardImage : (Iso.image emb).card = Iso.card := by
      exact Finset.card_image_of_injective _ emb.injective
    have hle := Finset.card_le_card hsub
    rw [hcardImage] at hle
    exact le_trans (Nat.mul_le_mul_left 8 hle) hBad
  · push_neg at hndex
    refine ⟨∅, ?_, ?_⟩
    · simp
      positivity
    · have hzero : ((st.promote (∅ : Finset V)).isolatedLive (8 * M)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v
        intro hv
        have hviso : ∀ y,
            ¬((st.promote (∅ : Finset V)).unitGraph (8 * M)).Adj (some v) y := by
          simpa [CompressionState.isolatedLive] using hv
        obtain ⟨j, hj⟩ := hndex v.1
        obtain ⟨y, hy⟩ := D.promoted_neighbor_of_direct st hM hM1
          (anchorPair v.1 j) hj ∅ v.2
        exact hviso y hy
      rw [hzero]
      simp

/-- Relative to a nondirect anchor, every other isolated label is easy or proper.
The two immediate-cancellation alternatives would instead cover the label or make
the anchor direct. -/
theorem DepartingSystem.isolated_mem_easy_or_proper {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i)
    (j : OtherLabel i) (hjiso : j.1 ∈ st.isolatedLive (8 * M)) :
    j ∈ D.easyLabels i ∨ j ∈ D.properLabels i := by
  classical
  let e : OrderedDistinct V := anchorPair i j
  let ν : Multiset V := D.liveType e
  have hcard : ν.card ≤ 2 := liveLabels_card_le_two st.blocks _
  have hne : ν ≠ {i, j.1} :=
    liveLabels_departing_ne st.blocks e.2 (D.leaves_rectangle e)
  have hni : i ∉ ν := by
    intro hi
    obtain ⟨y, hy⟩ := D.unitGraph_neighbor_label_of_mem_left st hM e hi
    have hiso : ∀ w, ¬(st.unitGraph (8 * M)).Adj (some j.1) w := by
      simpa [CompressionState.isolatedLive] using hjiso
    exact hiso y hy
  have hnj : j.1 ∉ ν := by
    intro hj
    apply hnd
    exact ⟨j, hj⟩
  by_cases hsmall : ν.card ≤ 1
  · left
    simp only [DepartingSystem.easyLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [e, ν] using (show IsEasyDeparture i j.1 ν from ⟨hni, hnj, hsmall⟩)
  · right
    have htwo : ν.card = 2 := by omega
    simp only [DepartingSystem.properLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [e, ν] using (show IsProperDeparture i j.1 ν from ⟨hni, hnj, htwo⟩)

/-- The proper-type star construction gives a concrete edge between any two
distinct labels of the same type, witnessed by the difference of their collision
rows and carrying the `8M` bound from the paper. -/
theorem DepartingSystem.unitGraph_adj_of_same_type {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (e e' : OrderedDistinct V)
    (hanchor : e.1.1 = e'.1.1) (htype : D.liveType e = D.liveType e')
    (hlabel : e.1.2 ≠ e'.1.2) :
    (st.unitGraph (8 * M)).Adj (some e.1.2) (some e'.1.2) := by
  apply st.unitGraph_adj_of_row (D.row_sub_mem_colLat e e')
    (D.row_sub_core_norm_le st hM e e')
  · intro heq
    exact hlabel (Option.some.inj heq)
  · exact D.row_sub_live_eq st e e' hanchor htype

/-- Among isolated proper labels for one anchor, the proper type is injective: two
distinct labels of one type are joined by the proper-type star edge. -/
theorem DepartingSystem.isolated_proper_type_injective {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) :
    Set.InjOn (fun j : OtherLabel i => D.liveType (anchorPair i j))
      {j | j ∈ D.properLabels i ∧ j.1 ∈ st.isolatedLive (8 * M)} := by
  intro j hj k hk htype
  apply Subtype.ext
  by_contra hjk
  have hadj := D.unitGraph_adj_of_same_type st hM (anchorPair i j) (anchorPair i k)
    rfl htype hjk
  have hkiso : ∀ w, ¬(st.unitGraph (8 * M)).Adj (some k.1) w := by
    simpa [CompressionState.isolatedLive] using hk.2
  exact hkiso (some j.1) hadj.symm

/-- The low-easy/low-type anchor estimate from Section 4: for a nondirect anchor,
the isolated vertices consist of the anchor itself, its easy labels, and at most one
proper label of each type. -/
theorem DepartingSystem.isolatedLive_card_le_anchor {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i) :
    (st.isolatedLive (8 * M)).card ≤
      1 + (D.easyLabels i).card + (D.properTypes i).card := by
  classical
  let Iso := st.isolatedLive (8 * M)
  let I : Finset (OtherLabel i) := Finset.univ.filter fun j => j.1 ∈ Iso
  let A : Finset (OtherLabel i) := I.filter fun j => j ∈ D.easyLabels i
  let B : Finset (OtherLabel i) := I.filter fun j => j ∉ D.easyLabels i
  let τ : OtherLabel i → Multiset V := fun j => D.liveType (anchorPair i j)
  have hIcard : Iso.card ≤ I.card + 1 := by
    have hIeq : I = Iso.subtype fun v => v ≠ i := by
      ext j
      simp [I]
    have hfilter : (Iso.filter fun v => v ≠ i) = Iso.erase i := by
      ext v
      simp [ne_eq, and_comm]
    rw [hIeq, Finset.card_subtype, hfilter]
    by_cases hi : i ∈ Iso
    · have he := Finset.card_erase_add_one hi
      omega
    · rw [Finset.erase_eq_self.mpr hi]
      omega
  have hsplit : A.card + B.card = I.card := by
    simpa [A, B] using I.card_filter_add_card_filter_not
      (fun j : OtherLabel i => j ∈ D.easyLabels i)
  have hA : A.card ≤ (D.easyLabels i).card := by
    apply Finset.card_le_card
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hBproper : B ⊆ D.properLabels i := by
    intro j hj
    have hjI := (Finset.mem_filter.mp hj).1
    have hjne := (Finset.mem_filter.mp hj).2
    have hjiso : j.1 ∈ st.isolatedLive (8 * M) := by
      simpa [I, Iso] using hjI
    rcases D.isolated_mem_easy_or_proper st hM i hnd j hjiso with he | hp
    · exact absurd he hjne
    · exact hp
  have hτinj : Set.InjOn τ (B : Set (OtherLabel i)) := by
    intro j hj k hk heq
    apply D.isolated_proper_type_injective st hM i
    · exact ⟨hBproper (Finset.mem_coe.mp hj), by
        have hjI := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
        simpa [I, Iso] using hjI⟩
    · exact ⟨hBproper (Finset.mem_coe.mp hk), by
        have hkI := (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1
        simpa [I, Iso] using hkI⟩
    · exact heq
  have hBimage : (B.image τ).card = B.card := by
    apply Finset.card_image_of_injOn
    intro j hj k hk heq
    exact hτinj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hk) heq
  have himage : B.image τ ⊆ D.properTypes i := by
    intro ν hν
    obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hν
    rw [DepartingSystem.properTypes]
    exact Finset.mem_image.mpr ⟨j, hBproper hjB, rfl⟩
  have hB : B.card ≤ (D.properTypes i).card := by
    rw [← hBimage]
    exact Finset.card_le_card himage
  change Iso.card ≤ 1 + (D.easyLabels i).card + (D.properTypes i).card
  omega

/-! ### Turning the contraction forest into an integral pivot plan -/

/-- Algebraic data attached to a rooted forest.  `parent v = none` means that `v`
is retained as the representative of an unrooted component; `some none` means that
it is eliminated into the core; and `some (some w)` means that it is eliminated
toward the live parent `w`. -/
structure ForestPivotPlan {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ) where
  parent : V → Option (Option V)
  rank : Option V → ℕ
  decreases : ∀ v y, parent v = some y → rank y < rank (some v)
  rank_le_three : ∀ v : V, rank (some v) ≤ 3
  pivotData : ∀ v y, parent v = some y →
    ∃ (r : Fin n → ℤ) (hr : r ∈ S.colLat P)
        (pivParent : Option {u : V // u ≠ v}),
      st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
      (∀ u : {u : V // u ≠ v},
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
          if pivParent = some u then -1 else 0) ∧
      Option.map Subtype.val pivParent = y ∧
      (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R

/-- Lemma 3.2 applied to the proof-relevant unit graph supplies both the quantitative
component bound and a leaf-to-root plan containing actual bounded lattice rows. -/
theorem CompressionState.exists_forestPivotPlan {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) (R : ℤ)
    [DecidableRel (st.unitGraph R).Adj] (f : ℕ)
    (hf : (Finset.univ.filter fun v : V =>
      ∀ w, ¬(st.unitGraph R).Adj (some v) w).card ≤ f) :
    ∃ F : SimpleGraph (Option V), F ≤ st.unitGraph R ∧ F.IsAcyclic ∧
      2 * Nat.card {c : F.ConnectedComponent // (none : Option V) ∉ c.supp} ≤
        Fintype.card V + f ∧
      ∃ plan : ForestPivotPlan st R,
        2 * Fintype.card {v : V // plan.parent v = none} ≤ Fintype.card V + f := by
  classical
  obtain ⟨F, hFG, hacyc, hdiam, hroot, hcount, hdata⟩ :=
    bounded_radius_contraction (st.unitGraph R) f hf
  obtain ⟨par, rk, hadj, hdec, hrank, hrootcount⟩ := hdata
  let liveParent : V → Option (Option V) := fun v => par (some v)
  have hpivot : ∀ v y, liveParent v = some y →
      ∃ (r : Fin n → ℤ) (hr : r ∈ S.colLat P)
          (pivParent : Option {u : V // u ≠ v}),
        st.basis.repr (Submodule.Quotient.mk r) (Sum.inr v) = 1 ∧
        (∀ u : {u : V // u ≠ v},
          st.basis.repr (Submodule.Quotient.mk r) (Sum.inr u.1) =
            if pivParent = some u then -1 else 0) ∧
        Option.map Subtype.val pivParent = y ∧
        (∑ c : C, |st.basis.repr (Submodule.Quotient.mk r) (Sum.inl c)|) ≤ R := by
    intro v y hpar
    have hne : some v ≠ y := by
      intro e
      have hd := hdec (some v) y hpar
      rw [e] at hd
      exact (Nat.lt_irrefl _ hd)
    have hFy : F.Adj (some v) y := (hadj (some v) y).mpr ⟨hne, Or.inl hpar⟩
    exact st.exists_pivot_of_unitGraph_adj v y (hFG hFy)
  let plan : ForestPivotPlan st R :=
    { parent := liveParent
      rank := rk
      decreases := fun v y h => hdec (some v) y h
      rank_le_three := hrank
      pivotData := hpivot }
  refine ⟨F, hFG, hacyc, hcount, plan, ?_⟩
  rw [Fintype.card_subtype]
  simpa [plan, liveParent] using hrootcount

namespace ForestPivotPlan

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {st : CompressionState S P C V} {R : ℤ}

/-- Unless the plan is already terminal, it has an active vertex of maximal rank. -/
theorem exists_maximal_active (plan : ForestPivotPlan st R)
    (hactive : ∃ v, plan.parent v ≠ none) :
    ∃ v y, plan.parent v = some y ∧
      ∀ u z, plan.parent u = some z →
        plan.rank (some u) ≤ plan.rank (some v) := by
  classical
  let A := Finset.univ.filter fun v : V => plan.parent v ≠ none
  have hA : A.Nonempty := by
    obtain ⟨v, hv⟩ := hactive
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨v, hvA, hvmax⟩ := Finset.exists_max_image A (fun u => plan.rank (some u)) hA
  obtain ⟨y, hy⟩ : ∃ y, plan.parent v = some y := Option.ne_none_iff_exists'.mp
    (Finset.mem_filter.mp hvA).2
  refine ⟨v, y, hy, ?_⟩
  intro u z huz
  apply hvmax
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [huz]; simp⟩

/-- A maximal active vertex is a leaf: no remaining pivot points toward it. -/
theorem no_child_of_maximal (plan : ForestPivotPlan st R) {w : V}
    (hv : ∀ u z, plan.parent u = some z →
      plan.rank (some u) ≤ plan.rank (some w)) (u : V) :
    plan.parent u ≠ some (some w) := by
  intro hu
  have hlt := plan.decreases u (some w) hu
  have hle := hv u (some w) hu
  omega

/-- The retained live representatives are exactly the vertices with no parent. -/
abbrev Roots (plan : ForestPivotPlan st R) := {v : V // plan.parent v = none}

/-- Vertices carrying a selected pivot row. -/
abbrev Active (plan : ForestPivotPlan st R) := {v : V // plan.parent v ≠ none}

noncomputable def activeParent (plan : ForestPivotPlan st R)
    (v : plan.Active) : Option V :=
  Classical.choose (Option.ne_none_iff_exists'.mp v.2)

theorem parent_activeParent (plan : ForestPivotPlan st R) (v : plan.Active) :
    plan.parent v.1 = some (plan.activeParent v) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp v.2)

/-- Follow the strictly decreasing parent chain.  An unrooted component ends at a
retained representative; a component attached to the auxiliary root ends in the
core and returns `none`. -/
def terminalRoot (plan : ForestPivotPlan st R) (v : V) : Option plan.Roots :=
  match h : plan.parent v with
  | none => some ⟨v, h⟩
  | some none => none
  | some (some w) => terminalRoot plan w
termination_by plan.rank (some v)
decreasing_by exact plan.decreases v (some w) h

@[simp] theorem terminalRoot_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.terminalRoot v.1 = some v := by
  rw [terminalRoot]
  split <;> rename_i hpar
  · apply congrArg some
    exact Subtype.ext rfl
  · rw [v.2] at hpar
    contradiction
  · rw [v.2] at hpar
    contradiction

theorem terminalRoot_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    plan.terminalRoot v = plan.terminalRoot w := by
  rw [terminalRoot]
  split <;> simp_all

theorem terminalRoot_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.terminalRoot v = none := by
  rw [terminalRoot]
  split <;> simp_all

/-- A canonical choice of the lattice row attached to an active parent edge. -/
noncomputable def chosenRow (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) : Fin n → ℤ :=
  Classical.choose (plan.pivotData v y h)

theorem chosenRow_mem (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) : plan.chosenRow h ∈ S.colLat P :=
  Classical.choose (Classical.choose_spec (plan.pivotData v y h))

noncomputable def chosenPivotParent (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    Option {u : V // u ≠ v} :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (plan.pivotData v y h)))

theorem chosenRow_spec (plan : ForestPivotPlan st R) {v : V} {y : Option V}
    (h : plan.parent v = some y) :
    st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr v) = 1 ∧
    (∀ u : {u : V // u ≠ v},
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u.1) =
        if plan.chosenPivotParent h = some u then -1 else 0) ∧
    Option.map Subtype.val (plan.chosenPivotParent h) = y ∧
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)|) ≤ R := by
  exact Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (plan.pivotData v y h)))

theorem chosenRow_core_norm_le (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)|) ≤ R :=
  (plan.chosenRow_spec h).2.2.2

noncomputable def activeRow (plan : ForestPivotPlan st R)
    (v : plan.Active) : Fin n → ℤ :=
  plan.chosenRow (plan.parent_activeParent v)

theorem activeRow_mem (plan : ForestPivotPlan st R) (v : plan.Active) :
    plan.activeRow v ∈ S.colLat P :=
  plan.chosenRow_mem (plan.parent_activeParent v)

/-- The square matrix of active live coefficients of the selected rows. -/
noncomputable def pivotMatrix (plan : ForestPivotPlan st R) :
    Matrix plan.Active plan.Active ℤ := fun v u =>
  st.basis.repr (Submodule.Quotient.mk (plan.activeRow v)) (Sum.inr u.1)

@[simp] theorem pivotMatrix_diag (plan : ForestPivotPlan st R)
    (v : plan.Active) : plan.pivotMatrix v v = 1 := by
  exact (plan.chosenRow_spec (plan.parent_activeParent v)).1

/-- A nonzero off-diagonal active coefficient can occur only at the live parent,
whose rank is strictly smaller. -/
theorem rank_lt_of_pivotMatrix_ne_zero (plan : ForestPivotPlan st R)
    {v u : plan.Active} (hvu : plan.pivotMatrix v u ≠ 0) :
    u = v ∨ plan.rank (some u.1) < plan.rank (some v.1) := by
  classical
  let hp := plan.parent_activeParent v
  have hs := plan.chosenRow_spec hp
  change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow hp))
    (Sum.inr u.1) ≠ 0 at hvu
  by_cases huv : u.1 = v.1
  · exact Or.inl (Subtype.ext huv)
  · let u' : {x : V // x ≠ v.1} := ⟨u.1, huv⟩
    have hu := hs.2.1 u'
    by_cases hpu : plan.chosenPivotParent hp = some u'
    · have hy : plan.activeParent v = some u.1 := by
        have hm := hs.2.2.1
        simpa [hpu, u'] using hm.symm
      right
      have hp' : plan.parent v.1 = some (some u.1) := hp.trans (congrArg some hy)
      exact plan.decreases v.1 (some u.1) hp'
    · rw [if_neg hpu] at hu
      exact absurd hu hvu

/-- The active-row matrix is integrally invertible.  A tie-breaker refines the parent
rank to a linear order; all possible parent entries lie strictly below the diagonal. -/
theorem pivotMatrix_det_eq_one (plan : ForestPivotPlan st R) :
    (plan.pivotMatrix).det = 1 := by
  classical
  let e : plan.Active ≃ Fin (Fintype.card plan.Active) := Fintype.equivFin plan.Active
  let key : plan.Active → (ℕ ×ₗ Fin (Fintype.card plan.Active)) := fun v =>
    toLex (plan.rank (some v.1), e v)
  letI : LinearOrder plan.Active := LinearOrder.lift' key (by
    intro u v huv
    apply e.injective
    exact congrArg (fun z => (ofLex z).2) huv)
  have htri : (plan.pivotMatrix).BlockTriangular OrderDual.toDual := by
    intro i j hij
    by_contra hn
    rcases plan.rank_lt_of_pivotMatrix_ne_zero hn with hji | hrank
    · subst j
      exact (lt_irrefl _ hij)
    · have hij' : i < j := by exact hij
      change key i < key j at hij'
      have hrle : plan.rank (some i.1) ≤ plan.rank (some j.1) :=
        (Prod.Lex.lt_iff'.mp hij').1
      omega
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp

theorem pivotMatrix_isUnit (plan : ForestPivotPlan st R) :
    IsUnit (plan.pivotMatrix).det := by
  rw [plan.pivotMatrix_det_eq_one]
  exact isUnit_one

theorem chosenPivotParent_eq_none (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.chosenPivotParent h = none := by
  have hm := (plan.chosenRow_spec h).2.2.1
  cases hp : plan.chosenPivotParent h with
  | none => rfl
  | some u =>
      rw [hp] at hm
      simp at hm

theorem chosenPivotParent_of_live (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    ∃ (hwv : w ≠ v), plan.chosenPivotParent h = some ⟨w, hwv⟩ := by
  have hm := (plan.chosenRow_spec h).2.2.1
  cases hp : plan.chosenPivotParent h with
  | none =>
      rw [hp] at hm
      simp at hm
  | some u =>
      have huw : u.1 = w := by
        simpa [hp] using hm
      subst w
      exact ⟨u.2, congrArg some (Subtype.ext rfl)⟩

/-- Exact live-coordinate vector of a row pointing to the auxiliary root. -/
theorem chosenRow_live_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) :
    (fun u => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
      (Sum.inr u)) = Pi.single v 1 := by
  have hs := plan.chosenRow_spec h
  have hp := plan.chosenPivotParent_eq_none h
  funext u
  by_cases huv : u = v
  · subst u
    simpa [Pi.single_apply] using hs.1
  · let u' : {u : V // u ≠ v} := ⟨u, huv⟩
    have hu := hs.2.1 u'
    simp [hp, Pi.single_apply, huv, u'] at hu ⊢
    exact hu

/-- Exact live-coordinate vector of a row pointing to a live parent. -/
theorem chosenRow_live_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    (fun u => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
      (Sum.inr u)) = Pi.single v 1 - Pi.single w 1 := by
  obtain ⟨hwv, hp⟩ := plan.chosenPivotParent_of_live h
  have hs := plan.chosenRow_spec h
  funext u
  by_cases huv : u = v
  · subst u
    simpa [Pi.single_apply, Ne.symm hwv] using hs.1
  · let u' : {u : V // u ≠ v} := ⟨u, huv⟩
    have hu := hs.2.1 u'
    by_cases huw : u = w
    · subst u
      have heq : (⟨w, hwv⟩ : {u : V // u ≠ v}) = u' := Subtype.ext rfl
      simp [hp, heq, Pi.single_apply, hwv, u'] at hu ⊢
      exact hu
    · have hne : some ⟨w, hwv⟩ ≠ some u' := by
        intro e
        exact huw (congrArg Subtype.val (Option.some.inj e)).symm
      simp [hp, hne, Pi.single_apply, huv, huw, u'] at hu ⊢
      exact hu

/-- Coefficients of the retained live representative reached from `v`. -/
def rootImage (plan : ForestPivotPlan st R) (v : V) : plan.Roots → ℤ :=
  match plan.terminalRoot v with
  | none => 0
  | some w => Pi.single w 1

/-- The accumulated core correction obtained by substituting from `v` toward its
retained representative or toward the auxiliary root. -/
noncomputable def coreImage (plan : ForestPivotPlan st R) (v : V) : C → ℤ :=
  match h : plan.parent v with
  | none => 0
  | some none => fun c =>
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)
  | some (some w) => fun c => plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c)
termination_by plan.rank (some v)
decreasing_by exact plan.decreases v (some w) h

@[simp] theorem rootImage_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.rootImage v.1 = Pi.single v 1 := by
  simp [rootImage]

@[simp] theorem coreImage_of_root (plan : ForestPivotPlan st R)
    (v : plan.Roots) : plan.coreImage v.1 = 0 := by
  rw [coreImage]
  split <;> rename_i hpar
  · rfl
  · rw [v.2] at hpar
    contradiction
  · rw [v.2] at hpar
    contradiction

theorem rootImage_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) : plan.rootImage v = 0 := by
  simp [rootImage, plan.terminalRoot_of_core_parent h]

theorem rootImage_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) :
    plan.rootImage v = plan.rootImage w := by
  simp [rootImage, plan.terminalRoot_of_live_parent h]

theorem coreImage_of_core_parent (plan : ForestPivotPlan st R) {v : V}
    (h : plan.parent v = some none) (c : C) :
    plan.coreImage v c =
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
  have hf : plan.coreImage v = fun c =>
      -st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
    rw [coreImage]
    split
    · rename_i heq
      simp [h] at heq
    · rfl
    · rename_i w' heq
      simp [h] at heq
  exact congrFun hf c

theorem coreImage_of_live_parent (plan : ForestPivotPlan st R) {v w : V}
    (h : plan.parent v = some (some w)) (c : C) :
    plan.coreImage v c = plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
  have hf : plan.coreImage v = fun c => plan.coreImage w c -
      st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) := by
    rw [coreImage]
    split
    · rename_i heq
      simp [h] at heq
    · rename_i heq
      simp [h] at heq
    · rename_i w' heq
      have hw : w = w' := by simpa [h] using heq
      subst w'
      rfl
  exact congrFun hf c

/-- The accumulated core correction along a parent chain costs at most one selected
row per rank level.  This is the quantitative content of the radius-three forest
construction. -/
theorem coreImage_norm_le_rank_mul (plan : ForestPivotPlan st R) (hR : 0 ≤ R)
    (v : V) :
    (∑ c : C, |plan.coreImage v c|) ≤ (plan.rank (some v) : ℤ) * R := by
  classical
  generalize hk : plan.rank (some v) = k
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
      subst k
      cases hpar : plan.parent v with
      | none =>
          let vr : plan.Roots := ⟨v, hpar⟩
          have hc := plan.coreImage_of_root vr
          have hcv : plan.coreImage v = 0 := by simpa [vr] using hc
          simp [hcv]
          exact mul_nonneg (Int.ofNat_nonneg _) hR
      | some y =>
          cases y with
          | none =>
              have hlt := plan.decreases v none hpar
              have hone : (1 : ℤ) ≤ (plan.rank (some v) : ℤ) := by
                exact_mod_cast (show 1 ≤ plan.rank (some v) by omega)
              calc
                (∑ c : C, |plan.coreImage v c|) =
                    ∑ c : C, |st.basis.repr
                      (Submodule.Quotient.mk (plan.chosenRow hpar)) (Sum.inl c)| := by
                        apply Finset.sum_congr rfl
                        intro c hc
                        rw [plan.coreImage_of_core_parent hpar c]
                        simp
                _ ≤ R := plan.chosenRow_core_norm_le hpar
                _ = (1 : ℤ) * R := by ring
                _ ≤ (plan.rank (some v) : ℤ) * R :=
                  mul_le_mul_of_nonneg_right hone hR
          | some w =>
              have hlt := plan.decreases v (some w) hpar
              have hi := ih (plan.rank (some w)) (by omega) w rfl
              have hrank : (plan.rank (some w) : ℤ) + 1 ≤
                  (plan.rank (some v) : ℤ) := by
                exact_mod_cast (show plan.rank (some w) + 1 ≤ plan.rank (some v) by omega)
              calc
                (∑ c : C, |plan.coreImage v c|) ≤
                    ∑ c : C, (|plan.coreImage w c| +
                      |st.basis.repr (Submodule.Quotient.mk
                        (plan.chosenRow hpar)) (Sum.inl c)|) := by
                          apply Finset.sum_le_sum
                          intro c hc
                          rw [plan.coreImage_of_live_parent hpar c]
                          exact abs_sub _ _
                _ = (∑ c : C, |plan.coreImage w c|) +
                    ∑ c : C, |st.basis.repr (Submodule.Quotient.mk
                      (plan.chosenRow hpar)) (Sum.inl c)| := by
                        rw [Finset.sum_add_distrib]
                _ ≤ (plan.rank (some w) : ℤ) * R + R :=
                  add_le_add hi (plan.chosenRow_core_norm_le hpar)
                _ = ((plan.rank (some w) : ℤ) + 1) * R := by ring
                _ ≤ (plan.rank (some v) : ℤ) * R :=
                  mul_le_mul_of_nonneg_right hrank hR

/-- Every forest substitution changes the core by at most three row norms. -/
theorem coreImage_norm_le_three_mul (plan : ForestPivotPlan st R) (hR : 0 ≤ R)
    (v : V) : (∑ c : C, |plan.coreImage v c|) ≤ 3 * R := by
  calc
    (∑ c : C, |plan.coreImage v c|) ≤ (plan.rank (some v) : ℤ) * R :=
      plan.coreImage_norm_le_rank_mul hR v
    _ ≤ 3 * R := mul_le_mul_of_nonneg_right (by exact_mod_cast plan.rank_le_three v) hR

/-- The simultaneous forest-elimination map on quotient coordinates.  Core basis
vectors remain fixed; every live basis vector is replaced by its accumulated core
correction plus, in an unrooted component, its retained representative. -/
noncomputable def forestMap (plan : ForestPivotPlan st R) :
    (Sum C V → ℤ) →ₗ[ℤ] (Sum C plan.Roots → ℤ) where
  toFun z
    | Sum.inl c => z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c
    | Sum.inr w => ∑ v : V, z (Sum.inr v) * plan.rootImage v w
  map_add' z z' := by
    funext i
    rcases i with c | w
    · simp only [Pi.add_apply]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring
    · simp only [Pi.add_apply]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
  map_smul' k z := by
    funext i
    rcases i with c | w
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        k * z (Sum.inl c) + ∑ v : V,
            k * z (Sum.inr v) * plan.coreImage v c =
          k * z (Sum.inl c) + ∑ v : V,
            k * (z (Sum.inr v) * plan.coreImage v c) := by
              apply congrArg (fun x => k * z (Sum.inl c) + x)
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = k * z (Sum.inl c) + k * ∑ v : V,
            z (Sum.inr v) * plan.coreImage v c := by rw [Finset.mul_sum]
        _ = k * (z (Sum.inl c) + ∑ v : V,
            z (Sum.inr v) * plan.coreImage v c) := by ring
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        (∑ v : V, k * z (Sum.inr v) * plan.rootImage v w) =
            ∑ v : V, k * (z (Sum.inr v) * plan.rootImage v w) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = k * ∑ v : V, z (Sum.inr v) * plan.rootImage v w := by
              rw [Finset.mul_sum]

/-- The simultaneous elimination map is onto: prescribe the core coordinates and
the coordinates at retained roots, setting every nonroot live input to zero. -/
theorem forestMap_surjective (plan : ForestPivotPlan st R) :
    Function.Surjective plan.forestMap := by
  classical
  intro x
  let z : Sum C V → ℤ
    | Sum.inl c => x (Sum.inl c)
    | Sum.inr v => if h : plan.parent v = none then x (Sum.inr ⟨v, h⟩) else 0
  refine ⟨z, ?_⟩
  funext i
  rcases i with c | w
  · change z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c =
      x (Sum.inl c)
    have hzero : ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      by_cases hroot : plan.parent v = none
      · let vr : plan.Roots := ⟨v, hroot⟩
        have hc := congrFun (plan.coreImage_of_root vr) c
        simp [z, hroot, vr, hc]
      · simp [z, hroot]
    rw [hzero, add_zero]
  · change (∑ v : V, z (Sum.inr v) * plan.rootImage v w) = x (Sum.inr w)
    rw [Finset.sum_eq_single w.1]
    · have hw := plan.rootImage_of_root w
      simp [z, w.2, hw, Pi.single_apply]
    · intro v hv hvw
      by_cases hroot : plan.parent v = none
      · let vr : plan.Roots := ⟨v, hroot⟩
        have hvrw : vr ≠ w := by
          intro e
          exact hvw (congrArg Subtype.val e)
        have hr := plan.rootImage_of_root vr
        simp [z, hroot, vr, hr, Pi.single_apply, hvrw]
      · simp [z, hroot]
    · simp

private theorem sum_single_mul (a : V) (f : V → ℤ) :
    ∑ x : V, (Pi.single a (1 : ℤ) : V → ℤ) x * f x = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro b hb hba
    simp [Pi.single_apply, hba]
  · simp

private theorem sum_single_sub_mul (a b : V) (f : V → ℤ) :
    ∑ x : V, ((Pi.single a (1 : ℤ) : V → ℤ) -
      (Pi.single b (1 : ℤ) : V → ℤ)) x * f x = f a - f b := by
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib, sum_single_mul, sum_single_mul]

/-- Every selected forest row is killed by the simultaneous elimination map. -/
theorem chosenRow_mem_ker_forestMap (plan : ForestPivotPlan st R)
    {v : V} {y : Option V} (h : plan.parent v = some y) :
    (fun i => st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) i) ∈
      LinearMap.ker plan.forestMap := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  rcases y with _ | w
  · have hlive := plan.chosenRow_live_core_parent h
    rcases i with c | q
    · change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) +
          ∑ u : V, st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
            (Sum.inr u) * plan.coreImage u c = 0
      simp_rw [congrFun hlive]
      rw [sum_single_mul, plan.coreImage_of_core_parent h c]
      ring
    · change (∑ u : V, st.basis.repr
          (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u) *
            plan.rootImage u q) = 0
      simp_rw [congrFun hlive]
      rw [sum_single_mul, plan.rootImage_of_core_parent h]
      rfl
  · have hlive := plan.chosenRow_live_live_parent h
    rcases i with c | q
    · change st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inl c) +
          ∑ u : V, st.basis.repr (Submodule.Quotient.mk (plan.chosenRow h))
            (Sum.inr u) * plan.coreImage u c = 0
      simp_rw [congrFun hlive]
      rw [sum_single_sub_mul, plan.coreImage_of_live_parent h c]
      ring
    · change (∑ u : V, st.basis.repr
          (Submodule.Quotient.mk (plan.chosenRow h)) (Sum.inr u) *
            plan.rootImage u q) = 0
      simp_rw [congrFun hlive]
      rw [sum_single_sub_mul, plan.rootImage_of_live_parent h]
      ring

/-- On the kernel of forest elimination, the active live coordinates determine the
whole vector.  If they vanish, the retained-root outputs and then the core outputs
force every remaining coordinate to vanish. -/
theorem eq_zero_of_mem_ker_of_active_zero (plan : ForestPivotPlan st R)
    (z : Sum C V → ℤ) (hz : z ∈ LinearMap.ker plan.forestMap)
    (hactive : ∀ v : plan.Active, z (Sum.inr v.1) = 0) : z = 0 := by
  classical
  have hmap : plan.forestMap z = 0 := LinearMap.mem_ker.mp hz
  have hlive : ∀ v : V, z (Sum.inr v) = 0 := by
    intro v
    by_cases hv : plan.parent v = none
    · let vr : plan.Roots := ⟨v, hv⟩
      have hout := congrFun hmap (Sum.inr vr)
      change (∑ u : V, z (Sum.inr u) * plan.rootImage u vr) = 0 at hout
      have hsum : (∑ u : V, z (Sum.inr u) * plan.rootImage u vr) =
          z (Sum.inr v) := by
        rw [Finset.sum_eq_single v]
        · have hr := plan.rootImage_of_root vr
          simp [vr, hr, Pi.single_apply]
        · intro u hu huv
          by_cases huA : plan.parent u ≠ none
          · have hzA := hactive ⟨u, huA⟩
            simp [hzA]
          · have huR : plan.parent u = none := not_ne_iff.mp huA
            let ur : plan.Roots := ⟨u, huR⟩
            have hurne : ur ≠ vr := by
              intro e
              exact huv (congrArg Subtype.val e)
            have hr := plan.rootImage_of_root ur
            simp [ur, hr, Pi.single_apply, hurne]
        · simp
      linarith
    · exact hactive ⟨v, hv⟩
  funext i
  rcases i with c | v
  · have hout := congrFun hmap (Sum.inl c)
    change z (Sum.inl c) + ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 at hout
    have hsum : ∑ v : V, z (Sum.inr v) * plan.coreImage v c = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hlive v, zero_mul]
    rw [hsum, add_zero] at hout
    simpa using hout
  · simpa [hlive v]

noncomputable def activeRowCoords (plan : ForestPivotPlan st R)
    (v : plan.Active) : Sum C V → ℤ := fun i =>
  st.basis.repr (Submodule.Quotient.mk (plan.activeRow v)) i

theorem activeRowCoords_mem_ker (plan : ForestPivotPlan st R)
    (v : plan.Active) : plan.activeRowCoords v ∈ LinearMap.ker plan.forestMap := by
  exact plan.chosenRow_mem_ker_forestMap (plan.parent_activeParent v)

/-- Exact triangular generation of the forest kernel by the selected lattice rows. -/
theorem ker_forestMap_eq_span_activeRows (plan : ForestPivotPlan st R) :
    LinearMap.ker plan.forestMap =
      Submodule.span ℤ (Set.range plan.activeRowCoords) := by
  classical
  apply le_antisymm
  · intro z hz
    have hunit : IsUnit plan.pivotMatrix :=
      (Matrix.isUnit_iff_isUnit_det plan.pivotMatrix).mpr plan.pivotMatrix_isUnit
    let target : plan.Active → ℤ := fun u => z (Sum.inr u.1)
    obtain ⟨k, hk⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hunit) target
    let q : Sum C V → ℤ := ∑ v : plan.Active, k v • plan.activeRowCoords v
    have hqspan : q ∈ Submodule.span ℤ (Set.range plan.activeRowCoords) := by
      apply Submodule.sum_mem
      intro v hv
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self v))
    have hqker : q ∈ LinearMap.ker plan.forestMap := by
      apply Submodule.sum_mem
      intro v hv
      exact Submodule.smul_mem _ _ (plan.activeRowCoords_mem_ker v)
    have hqactive : ∀ u : plan.Active, q (Sum.inr u.1) = target u := by
      intro u
      have hku := congrFun hk u
      change (∑ v : plan.Active, k v * plan.pivotMatrix v u) = target u at hku
      change (∑ v : plan.Active, k v • plan.activeRowCoords v) (Sum.inr u.1) = target u
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, activeRowCoords,
        pivotMatrix, activeRow] using hku
    let d : Sum C V → ℤ := z - q
    have hdker : d ∈ LinearMap.ker plan.forestMap :=
      (LinearMap.ker plan.forestMap).sub_mem hz hqker
    have hdactive : ∀ u : plan.Active, d (Sum.inr u.1) = 0 := by
      intro u
      change z (Sum.inr u.1) - q (Sum.inr u.1) = 0
      rw [hqactive u]
      simp [target]
    have hd0 : d = 0 := plan.eq_zero_of_mem_ker_of_active_zero d hdker hdactive
    have hzq : z = q := sub_eq_zero.mp hd0
    rw [hzq]
    exact hqspan
  · rw [Submodule.span_le]
    rintro z ⟨v, rfl⟩
    exact plan.activeRowCoords_mem_ker v

/-- Constructive form of the kernel equality: every kernel vector is an integral
linear combination of the selected row-coordinate vectors. -/
theorem exists_activeRowCoords_sum (plan : ForestPivotPlan st R)
    (z : Sum C V → ℤ) (hz : z ∈ LinearMap.ker plan.forestMap) :
    ∃ k : plan.Active → ℤ,
      z = ∑ v : plan.Active, k v • plan.activeRowCoords v := by
  classical
  have hunit : IsUnit plan.pivotMatrix :=
    (Matrix.isUnit_iff_isUnit_det plan.pivotMatrix).mpr plan.pivotMatrix_isUnit
  let target : plan.Active → ℤ := fun u => z (Sum.inr u.1)
  obtain ⟨k, hk⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hunit) target
  let q : Sum C V → ℤ := ∑ v : plan.Active, k v • plan.activeRowCoords v
  have hqker : q ∈ LinearMap.ker plan.forestMap := by
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (plan.activeRowCoords_mem_ker v)
  have hqactive : ∀ u : plan.Active, q (Sum.inr u.1) = target u := by
    intro u
    have hku := congrFun hk u
    change (∑ v : plan.Active, k v * plan.pivotMatrix v u) = target u at hku
    change (∑ v : plan.Active, k v • plan.activeRowCoords v) (Sum.inr u.1) = target u
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, activeRowCoords,
      pivotMatrix, activeRow] using hku
  have hdker : z - q ∈ LinearMap.ker plan.forestMap :=
    (LinearMap.ker plan.forestMap).sub_mem hz hqker
  have hdactive : ∀ u : plan.Active, (z - q) (Sum.inr u.1) = 0 := by
    intro u
    change z (Sum.inr u.1) - q (Sum.inr u.1) = 0
    rw [hqactive u]
    simp [target]
  have hd0 := plan.eq_zero_of_mem_ker_of_active_zero (z - q) hdker hdactive
  refine ⟨k, ?_⟩
  exact sub_eq_zero.mp hd0

/-- Physical blocks after simultaneous contraction are the unions of all old blocks
whose parent chains end at the same retained representative. -/
def contractedBlocks (plan : ForestPivotPlan st R) : LiveBlocks n plan.Roots where
  block w := Finset.univ.filter fun a =>
    st.blocks.owner a >>= plan.terminalRoot = some w
  owner a := st.blocks.owner a >>= plan.terminalRoot
  mem_block_iff a w := by simp
  nonempty w := by
    obtain ⟨a, ha⟩ := st.blocks.nonempty w.1
    refine ⟨a, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [(st.blocks.mem_block_iff a w.1).mp ha]
    simp

theorem contractedBlocks_mass_le (plan : ForestPivotPlan st R) :
    plan.contractedBlocks.mass ≤ st.blocks.mass := by
  classical
  have hnewdisj : (↑(Finset.univ : Finset plan.Roots) : Set plan.Roots).PairwiseDisjoint
      plan.contractedBlocks.block := by
    intro i hi j hj hij
    exact plan.contractedBlocks.disjoint hij
  have holddisj : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint
      st.blocks.block := by
    intro i hi j hj hij
    exact st.blocks.disjoint hij
  have hsub : Finset.univ.biUnion plan.contractedBlocks.block ⊆
      Finset.univ.biUnion st.blocks.block := by
    intro a ha
    obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
    have hterm := (Finset.mem_filter.mp haw).2
    cases howner : st.blocks.owner a with
    | none =>
        simp [howner] at hterm
    | some v =>
        apply Finset.mem_biUnion.mpr
        refine ⟨v, Finset.mem_univ _, ?_⟩
        exact (st.blocks.mem_block_iff a v).mpr howner
  calc
    plan.contractedBlocks.mass =
        (Finset.univ.biUnion plan.contractedBlocks.block).card :=
      (Finset.card_biUnion hnewdisj).symm
    _ ≤ (Finset.univ.biUnion st.blocks.block).card := Finset.card_le_card hsub
    _ = st.blocks.mass := Finset.card_biUnion holddisj

/-- Compose the old quotient-coordinate map with simultaneous forest elimination. -/
noncomputable def ambientForestMap (plan : ForestPivotPlan st R) :
    (Fin n → ℤ) →ₗ[ℤ] (Sum C plan.Roots → ℤ) :=
  plan.forestMap.comp
    (st.basis.equivFun.toLinearMap.comp (st.Q.mkQ : (Fin n → ℤ) →ₗ[ℤ] _))

theorem ambientForestMap_surjective (plan : ForestPivotPlan st R) :
    Function.Surjective plan.ambientForestMap := by
  intro z
  obtain ⟨w, hw⟩ := plan.forestMap_surjective z
  obtain ⟨q, hq⟩ := st.basis.equivFun.surjective w
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective st.Q q
  refine ⟨x, ?_⟩
  change plan.forestMap (st.basis.equivFun (st.Q.mkQ x)) = z
  rw [hx, hq, hw]

/-- Simultaneously impose all rows of a bounded-radius forest.  The quotient remains
free with basis `core ⊕ retained roots`; the new subgroup is primitive and is still
contained in the collision lattice because the forest kernel is generated integrally
by the chosen collision rows. -/
noncomputable def contract (plan : ForestPivotPlan st R) :
    CompressionState S P C plan.Roots := by
  let f := plan.ambientForestMap
  have hf : Function.Surjective f := plan.ambientForestMap_surjective
  let e : ((Fin n → ℤ) ⧸ LinearMap.ker f) ≃ₗ[ℤ]
      (Sum C plan.Roots → ℤ) := f.quotKerEquivOfSurjective hf
  let b : Module.Basis (Sum C plan.Roots) ℤ
      ((Fin n → ℤ) ⧸ LinearMap.ker f) :=
    (Pi.basisFun ℤ (Sum C plan.Roots)).map e.symm
  refine
    { Q := LinearMap.ker f
      le_colLat := ?_
      primitive := ker_primitive f
      basis := b
      blocks := plan.contractedBlocks
      live_coord := ?_ }
  · intro x hx
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    let z : Sum C V → ℤ := st.basis.equivFun (Submodule.Quotient.mk x)
    have hz : z ∈ LinearMap.ker plan.forestMap := by
      rw [LinearMap.mem_ker]
      exact hx0
    obtain ⟨k, hk⟩ := plan.exists_activeRowCoords_sum z hz
    let q : Fin n → ℤ := ∑ v : plan.Active, k v • plan.activeRow v
    have hqmem : q ∈ S.colLat P := by
      apply Submodule.sum_mem
      intro v hv
      exact (S.colLat P).smul_mem _ (plan.activeRow_mem v)
    have hqcoord : st.basis.equivFun (Submodule.Quotient.mk q) =
        ∑ v : plan.Active, k v • plan.activeRowCoords v := by
      change st.basis.equivFun (st.Q.mkQ
        (∑ v : plan.Active, k v • plan.activeRow v)) = _
      rw [map_sum]
      simp_rw [map_smul]
      ext i
      simp [Finset.sum_apply, activeRowCoords, activeRow, Finsupp.smul_apply,
        Pi.smul_apply, smul_eq_mul]
    have hquot : (Submodule.Quotient.mk x : (Fin n → ℤ) ⧸ st.Q) =
        Submodule.Quotient.mk q := by
      apply st.basis.equivFun.injective
      rw [hqcoord]
      exact hk
    have hdiff : x - q ∈ st.Q := by
      have hquot' : st.Q.mkQ x = st.Q.mkQ q := hquot
      rw [← Submodule.ker_mkQ st.Q, LinearMap.mem_ker, map_sub, hquot', sub_self]
    have hdiff' := st.le_colLat hdiff
    have hadd := (S.colLat P).add_mem hdiff' hqmem
    convert hadd using 1 <;> module
  · intro a w
    change b.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr w) = _
    simp only [b, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr,
      e, LinearMap.quotKerEquivOfSurjective_apply_mk]
    change (∑ v : V,
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
        plan.rootImage v w) = _
    rcases howner : st.blocks.owner a with _ | v
    · have hzero : ∑ v : V,
          st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
            plan.rootImage v w = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [st.live_coord]
        simp [howner]
      rw [hzero]
      simp [contractedBlocks, howner]
    · rw [Finset.sum_eq_single v]
      · rw [st.live_coord]
        by_cases hr : plan.terminalRoot v = some w
        · have hri : plan.rootImage v w = 1 := by
            simp [rootImage, hr, Pi.single_apply]
          simp [contractedBlocks, howner, hr, hri]
        · have hri : plan.rootImage v w = 0 := by
            rcases htr : plan.terminalRoot v with _ | q
            · simp [rootImage, htr]
            · have hqw : q ≠ w := by
                intro e
                apply hr
                rw [htr, e]
              simp [rootImage, htr, Pi.single_apply, hqw]
          simp [contractedBlocks, howner, hr, hri]
      · intro u hu huv
        rw [st.live_coord]
        simp [howner, Ne.symm huv]
      · simp

/-- Core coordinates after simultaneous contraction are obtained by applying the
forest substitution to the old quotient coordinates. -/
theorem contract_core_coord (plan : ForestPivotPlan st R) (a : Fin n) (c : C) :
    (plan.contract).basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) =
      st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) +
        ∑ v : V, st.basis.repr (Submodule.Quotient.mk (Pi.single a 1))
          (Sum.inr v) * plan.coreImage v c := by
  simp only [contract, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- Simultaneous radius-three contraction preserves the core invariant, increasing
its bound by at most three times the selected-row bound. -/
theorem contract_coreBound (plan : ForestPivotPlan st R) {M : ℤ}
    (hM : st.CoreBound M) (hR : 0 ≤ R) :
    plan.contract.CoreBound (M + 3 * R) := by
  classical
  intro a
  simp_rw [plan.contract_core_coord a]
  have hcorr :
      (∑ c : C, |∑ v : V,
        st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
          plan.coreImage v c|) ≤ 3 * R := by
    cases howner : st.blocks.owner a with
    | none =>
        have hz : ∀ v : V,
            st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) = 0 := by
          intro v
          rw [st.live_coord]
          simp [howner]
        simp_rw [hz]
        simpa using (mul_nonneg (show (0 : ℤ) ≤ 3 by norm_num) hR)
    | some w =>
        have hsum : ∀ c : C,
            (∑ v : V,
              st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
                plan.coreImage v c) = plan.coreImage w c := by
          intro c
          rw [Finset.sum_eq_single w]
          · rw [st.live_coord]
            simp [howner]
          · intro v hv hvw
            rw [st.live_coord]
            simp [howner, Ne.symm hvw]
          · simp
        simp_rw [hsum]
        exact plan.coreImage_norm_le_three_mul hR w
  calc
    (∑ c : C,
      |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c) +
        ∑ v : V, st.basis.repr (Submodule.Quotient.mk (Pi.single a 1))
          (Sum.inr v) * plan.coreImage v c|) ≤
        (∑ c : C,
          |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)|) +
        ∑ c : C, |∑ v : V,
          st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inr v) *
            plan.coreImage v c| := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro c hc
              exact abs_add_le _ _
    _ ≤ M + 3 * R := add_le_add (hM a) hcorr

/-- Promote every newly heavy contracted block.  The remaining blocks are precisely
the light blocks eligible for the next clean-rectangle round. -/
noncomputable def finishRound (plan : ForestPivotPlan st R) (L : ℕ) :=
  plan.contract.promote (plan.contract.blocks.heavy L)

theorem finishRound_coreBound (plan : ForestPivotPlan st R) (L : ℕ) {M : ℤ}
    (hM : plan.contract.CoreBound M) : plan.finishRound L |>.CoreBound (M + 1) := by
  exact plan.contract.promote_coreBound _ hM

theorem finishRound_blocks_light (plan : ForestPivotPlan st R) (L : ℕ)
    (v : {v : plan.Roots // v ∉ plan.contract.blocks.heavy L}) :
    ((plan.finishRound L).blocks.block v).card < L := by
  exact plan.contract.blocks.promote_heavy_is_light L v

theorem finishRound_mass_add_heavy_le (plan : ForestPivotPlan st R) (L : ℕ) :
    (plan.finishRound L).blocks.mass +
        L * (plan.contract.blocks.heavy L).card ≤ st.blocks.mass := by
  have hremoved := plan.contract.blocks.heavy_card_mul_le_removed L
  have hsplit := plan.contract.blocks.mass_promote_add_removed
    (plan.contract.blocks.heavy L)
  have hcontract := plan.contractedBlocks_mass_le
  calc
    (plan.finishRound L).blocks.mass +
        L * (plan.contract.blocks.heavy L).card ≤
      (plan.finishRound L).blocks.mass +
        ∑ v ∈ plan.contract.blocks.heavy L,
          (plan.contract.blocks.block v).card := Nat.add_le_add_left hremoved _
    _ = plan.contract.blocks.mass := hsplit
    _ ≤ st.blocks.mass := hcontract

end ForestPivotPlan

/-- A quantitative one-shot interface to forest contraction.  Once all but `f` live
vertices have a unit-graph neighbour, it returns an explicit next compression state
with the paper's retained-vertex and coefficient bounds. -/
theorem CompressionState.exists_bounded_forest_contract {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M R : ℤ} (hM : st.CoreBound M)
    (hR : 0 ≤ R) (f : ℕ)
    (hf : (st.isolatedLive R).card ≤ f) :
    ∃ plan : ForestPivotPlan st R,
      2 * Fintype.card plan.Roots ≤ Fintype.card V + f ∧
      plan.contract.CoreBound (M + 3 * R) := by
  classical
  letI : DecidableRel (st.unitGraph R).Adj := Classical.decRel _
  have hf' : (Finset.univ.filter fun v : V =>
      ∀ w, ¬(st.unitGraph R).Adj (some v) w).card ≤ f := by
    simpa [CompressionState.isolatedLive] using hf
  obtain ⟨F, hFG, hacyc, hcount, plan, hroots⟩ :=
    st.exists_forestPivotPlan R f hf'
  exact ⟨plan, hroots, plan.contract_coreBound hM hR⟩

/-- Contract a promoted state after a common sample has reduced the isolated count to
`m/8`.  The live count falls by `2/3` and the round core bound grows by at most `26`. -/
theorem CompressionState.exists_contract_after_sample {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M) (hM1 : 1 ≤ M)
    (T : Finset V)
    (hiso : 8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V) :
    ∃ plan : ForestPivotPlan (st.promote T) (8 * M),
      3 * Fintype.card plan.Roots ≤ 2 * Fintype.card V ∧
      plan.contract.CoreBound (26 * M) := by
  classical
  let f := Fintype.card V / 8
  have hf : ((st.promote T).isolatedLive (8 * M)).card ≤ f := by
    have hle : ((st.promote T).isolatedLive (8 * M)).card ≤ f := by
      dsimp [f]
      omega
    exact hle
  have hpM : (st.promote T).CoreBound (M + 1) := st.promote_coreBound T hM
  have hR : (0 : ℤ) ≤ 8 * M := by
    have hM0 : (0 : ℤ) ≤ M := le_trans (by norm_num) hM1
    positivity
  obtain ⟨plan, hcard, hcore⟩ :=
    (st.promote T).exists_bounded_forest_contract hpM hR f hf
  refine ⟨plan, ?_, ?_⟩
  · have hsub : Fintype.card {v : V // v ∉ T} ≤ Fintype.card V :=
      Fintype.card_subtype_le _
    dsimp [f] at hcard
    omega
  · intro a
    exact le_trans (hcore a) (by nlinarith)

/-- The first branch of the round dichotomy.  A nondirect anchor with fewer than
`m/8` easy labels and fewer than `m/8` proper types already yields a contraction by
a factor `2/3`, with no sampling or promotion. -/
theorem DepartingSystem.exists_low_anchor_contract {p n : ℕ}
    {S : MinimalNUS p n} {P : S.Pairing} {C V : Type*}
    [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (D : DepartingSystem P st.blocks) (i : V) (hnd : ¬D.IsDirectAnchor i)
    (heasy : 8 * (D.easyLabels i).card < Fintype.card V)
    (htypes : 8 * (D.properTypes i).card < Fintype.card V)
    (hm : 12 ≤ Fintype.card V) :
    ∃ plan : ForestPivotPlan st (8 * M),
      3 * Fintype.card plan.Roots ≤ 2 * Fintype.card V ∧
      plan.contract.CoreBound (25 * M) := by
  classical
  let f := Fintype.card V / 4 + 1
  have hiso : (st.isolatedLive (8 * M)).card ≤ f := by
    have h := D.isolatedLive_card_le_anchor st hM i hnd
    dsimp [f]
    omega
  have hf : (st.isolatedLive (8 * M)).card ≤ f := hiso
  have hR : (0 : ℤ) ≤ 8 * M := by
    have hM0 := st.coreBound_nonneg hM
    positivity
  obtain ⟨plan, hcard, hcore⟩ :=
    st.exists_bounded_forest_contract hM hR f hf
  refine ⟨plan, ?_, ?_⟩
  · dsimp [f] at hcard
    omega
  · convert hcore using 1 <;> ring

/-- A compression state with its changing core and live index types existentially
packed, so the round construction can be iterated. -/
structure PackedCompressionState {p n : ℕ} (S : MinimalNUS p n) (P : S.Pairing) where
  C : Type
  V : Type
  fintypeC : Fintype C
  decEqC : DecidableEq C
  fintypeV : Fintype V
  decEqV : DecidableEq V
  st : @CompressionState p n S P C V fintypeC decEqC fintypeV decEqV

attribute [instance] PackedCompressionState.fintypeC PackedCompressionState.decEqC
  PackedCompressionState.fintypeV PackedCompressionState.decEqV

namespace PackedCompressionState

variable {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing}

private theorem sqrt_le_five_six_of_shrink {a b : ℕ} (h : 3 * a ≤ 2 * b) :
    Real.sqrt a ≤ (5 / 6 : ℝ) * Real.sqrt b := by
  have ha0 : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) ≤ Real.sqrt b := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt a) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : (Real.sqrt b) ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have hr : (3 : ℝ) * a ≤ 2 * b := by exact_mod_cast h
  nlinarith

private theorem sqrt_le_two_thirds_of_two_shrinks {a b c : ℕ}
    (h₁ : 3 * b ≤ 2 * a) (h₂ : 3 * c ≤ 2 * b) :
    Real.sqrt c ≤ (2 / 3 : ℝ) * Real.sqrt a := by
  have ha0 : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hc0 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt a) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hc2 : (Real.sqrt c) ^ 2 = (c : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : (3 : ℝ) * b ≤ 2 * a := by exact_mod_cast h₁
  have hr₂ : (3 : ℝ) * c ≤ 2 * b := by exact_mod_cast h₂
  nlinarith

def coreCard (X : PackedCompressionState S P) : ℕ := @Fintype.card X.C X.fintypeC
def liveCard (X : PackedCompressionState S P) : ℕ := @Fintype.card X.V X.fintypeV
def mass (X : PackedCompressionState S P) : ℕ := @LiveBlocks.mass n X.V X.fintypeV X.st.blocks

noncomputable def initial (S : MinimalNUS p n) (P : S.Pairing) :
    PackedCompressionState S P where
  C := Empty
  V := Fin n
  fintypeC := inferInstance
  decEqC := inferInstance
  fintypeV := inferInstance
  decEqV := inferInstance
  st := initialCompressionState S P

structure RoundResult (X : PackedCompressionState S P) (M : ℤ) (L : ℕ) (D₀ : ℝ) where
  next : PackedCompressionState S P
  sampleCost : ℕ
  heavyCost : ℕ
  coreCard_eq : next.coreCard = X.coreCard + sampleCost + heavyCost
  live_shrink : 3 * next.liveCard ≤ 2 * X.liveCard
  sample_bound : (sampleCost : ℝ) ≤ D₀ * Real.sqrt X.liveCard
  coreBound : next.st.CoreBound (30 * M)
  light : ∀ v, (next.st.blocks.block v).card < L
  mass_charge : next.mass + L * heavyCost ≤ X.mass

structure IterationResult (X : PackedCompressionState S P) (M : ℤ)
    (L mstar : ℕ) (D₀ : ℝ) where
  final : PackedCompressionState S P
  rounds : ℕ
  sampleCost : ℕ
  heavyCost : ℕ
  terminal : final.liveCard < mstar
  coreCard_eq : final.coreCard = X.coreCard + sampleCost + heavyCost
  sample_bound : (sampleCost : ℝ) ≤ 12 * D₀ * Real.sqrt X.liveCard
  mass_charge : final.mass + L * heavyCost ≤ X.mass
  coreBound : final.st.CoreBound (30 ^ rounds * M)
  light : ∀ v, (final.st.blocks.block v).card < L
  rounds_le : rounds ≤ 2 * Nat.log 2 X.liveCard + 2

/-- One complete nonterminal round of Section 4, including the anchor dichotomy,
common sampling when needed, forest contraction, and promotion of newly heavy blocks. -/
theorem exists_round_result (D₀ : ℝ) (m₀ : ℕ) (hD₀ : 0 < D₀)
    (hhigh : ∀ {p n : ℕ} {S : MinimalNUS p n} {P : S.Pairing} {C V : Type}
      [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
      (st : CompressionState S P C V) {M : ℤ}, st.CoreBound M → 1 ≤ M →
      (D : DepartingSystem P st.blocks) → max m₀ 16 ≤ Fintype.card V →
      (∀ i, ¬D.IsDirectAnchor i →
        Fintype.card V ≤ 8 * (D.easyLabels i).card ∨
        Fintype.card V ≤ 8 * (D.properTypes i).card) →
      ∃ T : Finset V, (T.card : ℝ) ≤ D₀ * Real.sqrt (Fintype.card V) ∧
        8 * ((st.promote T).isolatedLive (8 * M)).card ≤ Fintype.card V)
    [Fact p.Prime] (X : PackedCompressionState S P) (M : ℤ) (hM : X.st.CoreBound M)
    (hM1 : 1 ≤ M) (hp : 64 ≤ p)
    (L : ℕ) (hL : L = Nat.log 2 p / 3)
    (hlight : ∀ v, (X.st.blocks.block v).card < L)
    (hm : max m₀ 16 ≤ X.liveCard) : Nonempty (RoundResult X M L D₀) := by
  classical
  letI : Fintype X.C := X.fintypeC
  letI : DecidableEq X.C := X.decEqC
  letI : Fintype X.V := X.fintypeV
  letI : DecidableEq X.V := X.decEqV
  have hpower : ∀ e : OrderedDistinct X.V,
      2 ^ ((X.st.blocks.block e.1.1).card + (X.st.blocks.block e.1.2).card - 2) < p := by
    apply light_blocks_power_lt X.st.blocks hp
    simpa [hL] using hlight
  let D : DepartingSystem P X.st.blocks := Classical.choice
    (exists_departingSystem S P X.st.blocks hpower)
  by_cases hlow : ∃ i : X.V, ¬D.IsDirectAnchor i ∧
      8 * (D.easyLabels i).card < Fintype.card X.V ∧
      8 * (D.properTypes i).card < Fintype.card X.V
  · obtain ⟨i, hnd, heasy, htypes⟩ := hlow
    obtain ⟨plan, hshrink, hcore⟩ := D.exists_low_anchor_contract X.st hM i hnd
      heasy htypes (by
        change 12 ≤ X.liveCard
        exact le_trans (by omega) hm)
    let H := plan.contract.blocks.heavy L
    let Y : PackedCompressionState S P :=
      { C := Sum X.C {v : plan.Roots // v ∈ H}
        V := {v : plan.Roots // v ∉ H}
        fintypeC := inferInstance
        decEqC := inferInstance
        fintypeV := inferInstance
        decEqV := inferInstance
        st := plan.finishRound L }
    refine ⟨⟨Y, 0, H.card, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [Y, coreCard]
      rw [Fintype.card_sum, Fintype.card_subtype]
      simp [H]
    · have hsub : Fintype.card {v : plan.Roots // v ∉ H} ≤
          Fintype.card plan.Roots := Fintype.card_subtype_le _
      dsimp [Y, liveCard]
      omega
    · simp
      positivity
    · have hc := plan.finishRound_coreBound L hcore
      intro a
      exact le_trans (hc a) (by nlinarith)
    · exact plan.finishRound_blocks_light L
    · exact plan.finishRound_mass_add_heavy_le L
  · have hall : ∀ i : X.V, ¬D.IsDirectAnchor i →
        Fintype.card X.V ≤ 8 * (D.easyLabels i).card ∨
        Fintype.card X.V ≤ 8 * (D.properTypes i).card := by
      intro i hnd
      have hn : ¬(8 * (D.easyLabels i).card < Fintype.card X.V ∧
          8 * (D.properTypes i).card < Fintype.card X.V) := by
        intro hb
        exact hlow ⟨i, hnd, hb.1, hb.2⟩
      omega
    obtain ⟨T, hT, hiso⟩ := hhigh X.st hM hM1 D (by simpa [liveCard] using hm) hall
    obtain ⟨plan, hshrink, hcore⟩ := X.st.exists_contract_after_sample hM hM1 T hiso
    let H := plan.contract.blocks.heavy L
    let Y : PackedCompressionState S P :=
      { C := Sum (Sum X.C {v : X.V // v ∈ T}) {v : plan.Roots // v ∈ H}
        V := {v : plan.Roots // v ∉ H}
        fintypeC := inferInstance
        decEqC := inferInstance
        fintypeV := inferInstance
        decEqV := inferInstance
        st := plan.finishRound L }
    refine ⟨⟨Y, T.card, H.card, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [Y, coreCard]
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_subtype,
        Fintype.card_subtype]
      simp [H]
    · have hsub : Fintype.card {v : plan.Roots // v ∉ H} ≤
          Fintype.card plan.Roots := Fintype.card_subtype_le _
      dsimp [Y, liveCard]
      omega
    · simpa [PackedCompressionState.liveCard] using hT
    · have hc := plan.finishRound_coreBound L hcore
      intro a
      exact le_trans (hc a) (by nlinarith)
    · exact plan.finishRound_blocks_light L
    · have hplan := plan.finishRound_mass_add_heavy_le L
      have hpromEq := X.st.blocks.mass_promote_add_removed T
      have hprom : (X.st.promote T).blocks.mass ≤ X.st.blocks.mass :=
        Nat.le.intro hpromEq
      exact le_trans hplan hprom

/-- Iterate the verified round interface two rounds at a time.  Two successive
`2/3` contractions at least halve the live count, giving the logarithmic round bound;
the geometric square-root sum is bounded by `12√m`. -/
theorem iterate_round_results (D₀ : ℝ) (hD₀ : 0 < D₀) (L mstar : ℕ)
    (hmstar16 : 16 ≤ mstar)
    (hstep : ∀ (X : PackedCompressionState S P) (M : ℤ),
      X.st.CoreBound M → 1 ≤ M →
      (∀ v, (X.st.blocks.block v).card < L) →
      mstar ≤ X.liveCard → Nonempty (RoundResult X M L D₀))
    (X : PackedCompressionState S P) (M : ℤ) (hM : X.st.CoreBound M)
    (hM1 : 1 ≤ M) (hlight : ∀ v, (X.st.blocks.block v).card < L) :
    Nonempty (IterationResult X M L mstar D₀) := by
  classical
  generalize hk : Nat.log 2 X.liveCard = k
  induction k using Nat.strong_induction_on generalizing X M with
  | h k ih =>
      subst k
      by_cases hterm : X.liveCard < mstar
      · refine ⟨
          { final := X
            rounds := 0
            sampleCost := 0
            heavyCost := 0
            terminal := hterm
            coreCard_eq := by simp
            sample_bound := by simp; positivity
            mass_charge := by simp
            coreBound := by simpa using hM
            light := hlight
            rounds_le := by omega }⟩
      · have hmstar : mstar ≤ X.liveCard := Nat.le_of_not_gt hterm
        let r₁ := Classical.choice (hstep X M hM hM1 hlight hmstar)
        by_cases hterm₁ : r₁.next.liveCard < mstar
        · refine ⟨
            { final := r₁.next
              rounds := 1
              sampleCost := r₁.sampleCost
              heavyCost := r₁.heavyCost
              terminal := hterm₁
              coreCard_eq := r₁.coreCard_eq
              sample_bound := by
                have hs := r₁.sample_bound
                have hsqrt : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                nlinarith
              mass_charge := r₁.mass_charge
              coreBound := by
                convert r₁.coreBound using 1 <;> norm_num
              light := r₁.light
              rounds_le := by omega }⟩
        · have hmstar₁ : mstar ≤ r₁.next.liveCard := Nat.le_of_not_gt hterm₁
          have hM₁ : 1 ≤ 30 * M := by nlinarith
          let r₂ := Classical.choice
            (hstep r₁.next (30 * M) r₁.coreBound hM₁ r₁.light hmstar₁)
          by_cases hterm₂ : r₂.next.liveCard < mstar
          · refine ⟨
              { final := r₂.next
                rounds := 2
                sampleCost := r₁.sampleCost + r₂.sampleCost
                heavyCost := r₁.heavyCost + r₂.heavyCost
                terminal := hterm₂
                coreCard_eq := by
                  rw [r₂.coreCard_eq, r₁.coreCard_eq]
                  omega
                sample_bound := by
                  have hs₁ := r₁.sample_bound
                  have hs₂ := r₂.sample_bound
                  have hsqrt := sqrt_le_five_six_of_shrink r₁.live_shrink
                  have hsqrtD := mul_le_mul_of_nonneg_left hsqrt hD₀.le
                  have hroot : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                  norm_cast at hs₁ hs₂
                  norm_num [Nat.cast_add] at ⊢
                  nlinarith
                mass_charge := by
                  have h₁ := r₁.mass_charge
                  have h₂ := r₂.mass_charge
                  rw [Nat.mul_add]
                  omega
                coreBound := by
                  convert r₂.coreBound using 1 <;> norm_num <;> ring
                light := r₂.light
                rounds_le := by omega }⟩
          · have hmstar₂ : mstar ≤ r₂.next.liveCard := Nat.le_of_not_gt hterm₂
            have hm₂pos : r₂.next.liveCard ≠ 0 := by omega
            have hhalf : 2 * r₂.next.liveCard ≤ X.liveCard := by
              have h₁ := r₁.live_shrink
              have h₂ := r₂.live_shrink
              omega
            have hpow : 2 ^ (Nat.log 2 r₂.next.liveCard + 1) ≤ X.liveCard := by
              rw [pow_succ]
              have hp := Nat.pow_log_le_self 2 hm₂pos
              omega
            have hlog : Nat.log 2 r₂.next.liveCard < Nat.log 2 X.liveCard := by
              have hl := Nat.le_log_of_pow_le (by norm_num) hpow
              omega
            let fut := Classical.choice
              (ih (Nat.log 2 r₂.next.liveCard) hlog r₂.next (30 * (30 * M))
                r₂.coreBound (by nlinarith) r₂.light rfl)
            refine ⟨
              { final := fut.final
                rounds := fut.rounds + 2
                sampleCost := r₁.sampleCost + r₂.sampleCost + fut.sampleCost
                heavyCost := r₁.heavyCost + r₂.heavyCost + fut.heavyCost
                terminal := fut.terminal
                coreCard_eq := by
                  rw [fut.coreCard_eq, r₂.coreCard_eq, r₁.coreCard_eq]
                  omega
                sample_bound := by
                  have hs₁ := r₁.sample_bound
                  have hs₂ := r₂.sample_bound
                  have hsf := fut.sample_bound
                  have hsqrt₁ := sqrt_le_five_six_of_shrink r₁.live_shrink
                  have hsqrt₂ := sqrt_le_two_thirds_of_two_shrinks
                    r₁.live_shrink r₂.live_shrink
                  have hsqrtD₁ := mul_le_mul_of_nonneg_left hsqrt₁ hD₀.le
                  have hsqrtD₂ := mul_le_mul_of_nonneg_left hsqrt₂ hD₀.le
                  have hroot : 0 ≤ Real.sqrt X.liveCard := Real.sqrt_nonneg _
                  norm_cast at hs₁ hs₂ hsf
                  norm_num [Nat.cast_add] at ⊢
                  nlinarith
                mass_charge := by
                  have h₁ := r₁.mass_charge
                  have h₂ := r₂.mass_charge
                  have hf := fut.mass_charge
                  rw [Nat.mul_add, Nat.mul_add]
                  omega
                coreBound := by
                  have hc := fut.coreBound
                  convert hc using 1
                  rw [pow_add]
                  ring
                light := fut.light
                rounds_le := by
                  have hr := fut.rounds_le
                  omega }⟩

end PackedCompressionState

/-! ### Reading off a terminal state -/

/-- Read off an arbitrary final state by retaining both its core and its boundedly
many remaining live representatives. -/
theorem CompressionState.finish_any {p n E : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
    (st : CompressionState S P C V) {M : ℤ} (hM : st.CoreBound M)
    (hcard : (((Fintype.card C + Fintype.card V : ℕ) : ℝ)) ≤
      E * (Real.sqrt n + n / Real.log p))
    (hnorm : M + 1 ≤ (n : ℤ) ^ E) :
    ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
      Q ≤ S.colLat P ∧
      (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
      Module.finrank ℤ Q = n - K ∧
      ((K : ℝ) ≤ E * (Real.sqrt n + n / Real.log p)) ∧
      ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
        ∀ i : Fin n,
          ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤
            (n : ℤ) ^ E := by
  classical
  let b : Module.Basis (Fin (Fintype.card (Sum C V))) ℤ ((Fin n → ℤ) ⧸ st.Q) :=
    st.basis.reindex (Fintype.equivFin (Sum C V))
  refine ⟨Fintype.card (Sum C V), st.Q, st.le_colLat, st.primitive, ?_, ?_, b, ?_⟩
  · have hr := st.Q.finrank_quotient_add_finrank
    have hq : Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) = Fintype.card (Sum C V) := by
      simpa using Module.finrank_eq_card_basis st.basis
    have ha : Module.finrank ℤ (Fin n → ℤ) = n := by
      simpa using Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
    have hr' : Fintype.card (Sum C V) + Module.finrank ℤ st.Q = n := by
      calc
        Fintype.card (Sum C V) + Module.finrank ℤ st.Q =
            Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) + Module.finrank ℤ st.Q := by rw [hq]
        _ = Module.finrank ℤ (Fin n → ℤ) := hr
        _ = n := ha
    omega
  · simpa using hcard
  · intro i
    have hlive : (∑ v : V,
        |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inr v)|) ≤ 1 := by
      rcases howner : st.blocks.owner i with _ | w
      · simp_rw [st.live_coord]
        simp [howner]
      · rw [Finset.sum_eq_single w]
        · rw [st.live_coord]
          simp [howner]
        · intro v hv hvw
          rw [st.live_coord]
          simp [howner, Ne.symm hvw]
        · simp
    calc
      ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| =
          ∑ q : Sum C V,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) q| := by
              simp only [b, Module.Basis.repr_reindex_apply]
              rw [← (Fintype.equivFin (Sum C V)).sum_comp]
              simp
      _ = (∑ c : C,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inl c)|) +
          ∑ v : V,
            |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inr v)| := by
              rw [Fintype.sum_sum_type]
      _ ≤ M + 1 := add_le_add (hM i) hlive
      _ ≤ (n : ℤ) ^ E := hnorm

/-- Once no live representative remains, a compression state is exactly the subgroup
and bounded quotient basis required by Proposition 4.1. -/
theorem CompressionState.finish {p n E : ℕ} {S : MinimalNUS p n} {P : S.Pairing}
    {C : Type*} [Fintype C] [DecidableEq C]
    (st : CompressionState S P C Empty)
    (hcard : ((Fintype.card C : ℕ) : ℝ) ≤
      E * (Real.sqrt n + n / Real.log p))
    (hnorm : ∀ a : Fin n,
      ∑ c : C,
        |st.basis.repr (Submodule.Quotient.mk (Pi.single a 1)) (Sum.inl c)| ≤
          (n : ℤ) ^ E) :
    ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
      Q ≤ S.colLat P ∧
      (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
      Module.finrank ℤ Q = n - K ∧
      ((K : ℝ) ≤ E * (Real.sqrt n + n / Real.log p)) ∧
      ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
        ∀ i : Fin n,
          ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤
            (n : ℤ) ^ E := by
  classical
  let bC : Module.Basis C ℤ ((Fin n → ℤ) ⧸ st.Q) :=
    st.basis.reindex (Equiv.sumEmpty C Empty)
  let b : Module.Basis (Fin (Fintype.card C)) ℤ ((Fin n → ℤ) ⧸ st.Q) :=
    bC.reindex (Fintype.equivFin C)
  refine ⟨Fintype.card C, st.Q, st.le_colLat, st.primitive, ?_, hcard, b, ?_⟩
  · have hr := st.Q.finrank_quotient_add_finrank
    have hq : Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) = Fintype.card C := by
      simpa using Module.finrank_eq_card_basis st.basis
    have ha : Module.finrank ℤ (Fin n → ℤ) = n := by
      simpa using Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
    have hr' : Fintype.card C + Module.finrank ℤ st.Q = n := by
      calc
        Fintype.card C + Module.finrank ℤ st.Q =
            Module.finrank ℤ ((Fin n → ℤ) ⧸ st.Q) + Module.finrank ℤ st.Q := by
              rw [hq]
        _ = Module.finrank ℤ (Fin n → ℤ) := hr
        _ = n := ha
    omega
  · intro i
    calc
      ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k|
          = ∑ c : C,
              |st.basis.repr (Submodule.Quotient.mk (Pi.single i 1)) (Sum.inl c)| := by
            simp only [b, bC, Module.Basis.repr_reindex_apply]
            rw [← (Fintype.equivFin C).sum_comp]
            simp
      _ ≤ (n : ℤ) ^ E := hnorm i

private theorem log_le_six_logThird (p : ℕ) (hp : 64 ≤ p) :
    Real.log p ≤ 6 * (Nat.log 2 p / 3 : ℕ) := by
  let ell := Nat.log 2 p
  let L := ell / 3
  have hell : 6 ≤ ell := by
    have hmono := Nat.log_mono_right (b := 2) hp
    norm_num at hmono ⊢
    exact hmono
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hpPowN : p ≤ 2 ^ (ell + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) p)
  have hpPowR : (p : ℝ) ≤ (2 : ℝ) ^ (ell + 1) := by exact_mod_cast hpPowN
  have hp0 : (0 : ℝ) < p := by positivity
  have hlog := Real.log_le_log hp0 hpPowR
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hellL : ell + 1 ≤ 6 * L := by
    dsimp [L]
    omega
  have hcast : ((ell + 1 : ℕ) : ℝ) ≤ 6 * L := by exact_mod_cast hellL
  dsimp [ell, L] at hlog ⊢
  have hn : (0 : ℝ) ≤ ell + 1 := by positivity
  nlinarith

private theorem coefficient_growth_le {n r : ℕ} (hn : 2 ≤ n)
    (hr : r ≤ 2 * Nat.log 2 n + 2) :
    (30 : ℤ) ^ r + 1 ≤ (n : ℤ) ^ 22 := by
  have h30 : 30 ≤ 2 ^ 5 := by norm_num
  have hbase : 30 ^ r ≤ (2 ^ 5) ^ r := Nat.pow_le_pow_left h30 r
  have hexp : 5 * r ≤ 10 * Nat.log 2 n + 10 := by omega
  have hpowexp : 2 ^ (5 * r) ≤ 2 ^ (10 * Nat.log 2 n + 10) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hlogpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hten : (2 ^ Nat.log 2 n) ^ 10 ≤ n ^ 10 := Nat.pow_le_pow_left hlogpow 10
  have hn10 : 2 ^ 10 ≤ n ^ 10 := by
    have := Nat.pow_le_pow_left hn 10
    simpa using this
  have hmain : 30 ^ r ≤ n ^ 20 := by
    calc
      30 ^ r ≤ (2 ^ 5) ^ r := hbase
      _ = 2 ^ (5 * r) := by rw [← pow_mul]
      _ ≤ 2 ^ (10 * Nat.log 2 n + 10) := hpowexp
      _ = 2 ^ 10 * (2 ^ Nat.log 2 n) ^ 10 := by ring
      _ ≤ n ^ 10 * n ^ 10 := Nat.mul_le_mul hn10 hten
      _ = n ^ 20 := by rw [← pow_add]
  have hn20 : 1 ≤ n ^ 20 := one_le_pow₀ (by omega)
  have hnat : 30 ^ r + 1 ≤ n ^ 22 := by
    calc
      30 ^ r + 1 ≤ n ^ 20 + n ^ 20 := Nat.add_le_add hmain hn20
      _ ≤ n ^ 20 * n ^ 2 := by nlinarith [show 2 ≤ n ^ 2 by nlinarith]
      _ = n ^ 22 := by rw [← pow_add]
  exact_mod_cast hnat
/-- **Proposition 4.1 (Compression).**  There is an absolute constant `C` such that for
every prime `p ≥ 64` and every inclusion-minimal example with pairing, there exist
`K` and a primitive subgroup `Q ≤ Λ` of rank `n − K` with `K ≤ C(√n + n/log p)`, whose
quotient `ℤⁿ/Q` is free of rank `K` with a basis in which the image of every coordinate
vector `e_i` has `ℓ¹`-norm at most `n^C`. -/
theorem compression :
    ∃ C : ℕ, 0 < C ∧
      ∀ (p n : ℕ) (_ : Fact p.Prime) (S : MinimalNUS p n) (P : S.Pairing),
        64 ≤ p →
        ∃ (K : ℕ) (Q : Submodule ℤ (Fin n → ℤ)),
          Q ≤ S.colLat P ∧
          (∀ (v : Fin n → ℤ) (c : ℤ), c ≠ 0 → c • v ∈ Q → v ∈ Q) ∧
          Module.finrank ℤ Q = n - K ∧
          ((K : ℝ) ≤ C * (Real.sqrt n + n / Real.log p)) ∧
          ∃ b : Module.Basis (Fin K) ℤ ((Fin n → ℤ) ⧸ Q),
            ∀ i : Fin n,
              ∑ k, |b.repr (Submodule.Quotient.mk (Pi.single i 1)) k| ≤ (n : ℤ) ^ C := by
  classical
  obtain ⟨D₀, m₀, hD₀, hhigh⟩ := exists_high_anchor_sample
  let mstar := max m₀ 16
  obtain ⟨C, hC⟩ : ∃ C : ℕ,
      12 * D₀ + mstar + 6 + 22 ≤ (C : ℝ) := exists_nat_ge _
  have hCpos : 0 < C := by
    have hD : 0 < 12 * D₀ := by positivity
    exact_mod_cast (show (0 : ℝ) < C by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro p n hpFact S P hp64
  let L := Nat.log 2 p / 3
  have hlog6 : 6 ≤ Nat.log 2 p := by
    have hmono := Nat.log_mono_right (b := 2) hp64
    norm_num at hmono ⊢
    exact hmono
  have hL2 : 2 ≤ L := by dsimp [L]; omega
  let X₀ := PackedCompressionState.initial S P
  have hX₀bound : X₀.st.CoreBound 1 := by
    intro a
    have h0 := initialCompressionState_coreBound S P a
    exact le_trans h0 (by norm_num)
  have hX₀light : ∀ v, (X₀.st.blocks.block v).card < L := by
    change ∀ v : Fin n, ((initialCompressionState S P).blocks.block v).card < L
    intro v
    change ({v} : Finset (Fin n)).card < L
    simp
    omega
  have hstep : ∀ (X : PackedCompressionState S P) (M : ℤ),
      X.st.CoreBound M → 1 ≤ M →
      (∀ v, (X.st.blocks.block v).card < L) →
      mstar ≤ X.liveCard →
      Nonempty (PackedCompressionState.RoundResult X M L D₀) := by
    intro X M hM hM1 hlight hm
    exact PackedCompressionState.exists_round_result D₀ m₀ hD₀ hhigh X M hM hM1
      hp64 L rfl hlight (by simpa [mstar] using hm)
  let out := Classical.choice
    (PackedCompressionState.iterate_round_results D₀ hD₀ L mstar
      (by simp [mstar]) hstep X₀ 1 hX₀bound (by norm_num) hX₀light)
  have hmass0 : X₀.mass ≤ n := by
    exact X₀.st.blocks.mass_le
  have hheavyNat : L * out.heavyCost ≤ n := by
    have hm := out.mass_charge
    omega
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp64))
  have hlogL : Real.log p ≤ 6 * L := by
    simpa [L] using log_le_six_logThird p hp64
  have hheavy : (out.heavyCost : ℝ) ≤ 6 * (n : ℝ) / Real.log p := by
    have hnatR : (L : ℝ) * out.heavyCost ≤ n := by exact_mod_cast hheavyNat
    have hh0 : (0 : ℝ) ≤ out.heavyCost := by positivity
    have hmul : (out.heavyCost : ℝ) * Real.log p ≤ 6 * n := by
      calc
        (out.heavyCost : ℝ) * Real.log p ≤ out.heavyCost * (6 * L) :=
          mul_le_mul_of_nonneg_left hlogL hh0
        _ ≤ 6 * n := by nlinarith
    exact (le_div_iff₀ hlogp).mpr (by nlinarith)
  have hn1R : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) S.two_le)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1R
  have hlive : (out.final.liveCard : ℝ) ≤ mstar * Real.sqrt n := by
    have ht : out.final.liveCard ≤ mstar := Nat.le_of_lt out.terminal
    have htR : (out.final.liveCard : ℝ) ≤ mstar := by exact_mod_cast ht
    have hm0 : (0 : ℝ) ≤ mstar := by positivity
    nlinarith
  have hsample := out.sample_bound
  have hLive0 : X₀.liveCard = n := by
    simp [X₀, PackedCompressionState.liveCard, PackedCompressionState.initial]
  rw [hLive0] at hsample
  have hheavy' : (out.heavyCost : ℝ) ≤ 6 * (n / Real.log p) := by
    convert hheavy using 1 <;> ring
  have hCcoef : 12 * D₀ + mstar + 6 ≤ (C : ℝ) := by linarith
  have hA0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hB0 : (0 : ℝ) ≤ (n : ℝ) / Real.log p := by positivity
  have hcoefA : 12 * D₀ + mstar ≤ (C : ℝ) := by linarith
  have hcoefB : (6 : ℝ) ≤ C := by linarith
  have hmulA := mul_le_mul_of_nonneg_right hcoefA hA0
  have hmulB := mul_le_mul_of_nonneg_right hcoefB hB0
  have hcard : (((out.final.coreCard + out.final.liveCard : ℕ) : ℝ)) ≤
      C * (Real.sqrt n + n / Real.log p) := by
    rw [out.coreCard_eq]
    have hcore0 : X₀.coreCard = 0 := by simp [X₀, PackedCompressionState.coreCard,
      PackedCompressionState.initial]
    rw [hcore0]
    norm_num [Nat.cast_add]
    calc
      (out.sampleCost : ℝ) + out.heavyCost + out.final.liveCard ≤
          12 * D₀ * Real.sqrt n + 6 * (n / Real.log p) +
            mstar * Real.sqrt n := add_le_add (add_le_add hsample hheavy') hlive
      _ = (12 * D₀ + mstar) * Real.sqrt n +
          6 * (n / Real.log p) := by ring
      _ ≤ C * Real.sqrt n + C * (n / Real.log p) := add_le_add hmulA hmulB
      _ = C * (Real.sqrt n + n / Real.log p) := by ring
  have hC22 : 22 ≤ C := by exact_mod_cast (show (22 : ℝ) ≤ C by linarith)
  have hrounds : out.rounds ≤ 2 * Nat.log 2 n + 2 := by simpa [hLive0] using out.rounds_le
  have hgrowth := coefficient_growth_le S.two_le hrounds
  have hpowmono : (n : ℤ) ^ 22 ≤ (n : ℤ) ^ C := by
    exact pow_le_pow_right₀ (by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) S.two_le)) hC22
  have hnorm : (30 : ℤ) ^ out.rounds + 1 ≤ (n : ℤ) ^ C :=
    le_trans hgrowth hpowmono
  have hfinalBound : out.final.st.CoreBound ((30 : ℤ) ^ out.rounds) := by
    simpa using out.coreBound
  exact out.final.st.finish_any hfinalBound (by simpa [PackedCompressionState.coreCard,
    PackedCompressionState.liveCard] using hcard) hnorm

end NUS
