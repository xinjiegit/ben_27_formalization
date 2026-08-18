/-
# Bounded-radius contraction (Section 3, Lemma 3.2)

The combinatorial contraction lemma.  The vertex set is `Option V`: the vertices
`some v` are the live vertices and `none` is the (optional) root — if no root is
intended, simply take a graph with no edges at `none`.

The paper's proof takes a maximal matching `M` on the live subgraph; every unmatched
vertex with a live neighbour is assigned to a matching edge, producing disjoint
double-stars of diameter `≤ 3`; each double-star meeting the root contributes one root
edge, which bounds the distance to the root by `4` inside the rooted component; and the
retained-vertex count is `≤ (N + f)/2` since each unrooted double-star has at least two
live vertices.  The statement below is exactly what Proposition 4.1 consumes.
-/
import Mathlib

namespace NUS

open SimpleGraph

/-! ### Helpers: canonical endpoints of an unordered pair -/

private noncomputable def efst {α : Type*} (e : Sym2 α) : α := (Quot.out e).1

private noncomputable def esnd {α : Type*} (e : Sym2 α) : α := (Quot.out e).2

private lemma sym2_eq_mk {α : Type*} (e : Sym2 α) : e = s(efst e, esnd e) := by
  conv_lhs => rw [← Quot.out_eq e]
  rfl

private lemma efst_mem {α : Type*} (e : Sym2 α) : efst e ∈ e := Sym2.out_fst_mem e

private lemma esnd_mem {α : Type*} (e : Sym2 α) : esnd e ∈ e := Sym2.out_snd_mem e

private lemma mem_out_cases {α : Type*} {x : α} {e : Sym2 α} (h : x ∈ e) :
    x = efst e ∨ x = esnd e := by
  rw [sym2_eq_mk e, Sym2.mem_iff] at h
  exact h

/-! ### Helpers: the graph of a "parent" map -/

/-- The simple graph induced by a parent map: `x` and `y` are adjacent when one is the
parent of the other. -/
private def pgraph {α : Type*} (p : α → Option α) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => p x = some y

private lemma pgraph_adj {α : Type*} (p : α → Option α) (x y : α) :
    (pgraph p).Adj x y ↔ x ≠ y ∧ (p x = some y ∨ p y = some x) :=
  SimpleGraph.fromRel_adj _ x y

/-- A predicate preserved along edges is preserved along reachability. -/
private lemma reachable_invariant {α : Type*} {H : SimpleGraph α} {Q : α → Prop}
    (hQ : ∀ x y, H.Adj x y → Q x → Q y) :
    ∀ {x y : α}, H.Reachable x y → Q x → Q y := by
  have key : ∀ (x y : α), H.Walk x y → Q x → Q y := by
    intro x y W
    induction W with
    | nil => exact fun h => h
    | cons hadj tail ih => exact fun hq => ih (hQ _ _ hadj hq)
  intro x y h hx
  exact h.elim fun W => key x y W hx

/-- A parent map that strictly decreases a rank function yields an acyclic graph: the
vertex of maximal rank on a cycle would have to have two equal neighbours. -/
private lemma pgraph_isAcyclic {α : Type*} (p : α → Option α) (rk : α → ℕ)
    (hp : ∀ x y, p x = some y → rk y < rk x) : (pgraph p).IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c.support.toFinset rk
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hm' : m ∈ c.support := List.mem_toFinset.mp hm
  have hc' : (c.rotate m hm').IsCycle := hc.rotate hm'
  have hnil : ¬(c.rotate m hm').Nil := hc'.not_nil
  have h1 := (pgraph_adj p _ _).mp ((c.rotate m hm').adj_snd hnil)
  have h2 := (pgraph_adj p _ _).mp ((c.rotate m hm').adj_penultimate hnil)
  have hsnd : rk (c.rotate m hm').snd ≤ rk m := hmax _ (List.mem_toFinset.mpr
    ((Walk.mem_support_rotate_iff c m hm').mp ((c.rotate m hm').getVert_mem_support 1)))
  have hpen : rk (c.rotate m hm').penultimate ≤ rk m := hmax _ (List.mem_toFinset.mpr
    ((Walk.mem_support_rotate_iff c m hm').mp
      ((c.rotate m hm').getVert_mem_support ((c.rotate m hm').length - 1))))
  have e1 : p m = some (c.rotate m hm').snd := by
    rcases h1.2 with h | h
    · exact h
    · exact absurd (hp _ _ h) (by omega)
  have e2 : p m = some (c.rotate m hm').penultimate := by
    rcases h2.2 with h | h
    · exact absurd (hp _ _ h) (by omega)
    · exact h
  exact hc'.snd_ne_penultimate (Option.some.inj (e1.symm.trans e2))

/-- **Lemma 3.2 (Bounded-radius contraction).**  Let `G` be a graph on live vertices
`V` plus a root `none`, in which at most `f` live vertices are isolated (incident with
neither a live edge nor a root edge).  Then `G` contains a forest `F` such that
components of `F` avoiding the root have diameter at most `3`; every live vertex in the
root's component is at distance at most `4` from the root; and the number of components
avoiding the root — the retained live blocks — is at most `(N + f)/2`. -/
theorem bounded_radius_contraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph (Option V)) [DecidableRel G.Adj] (f : ℕ)
    (hf : (Finset.univ.filter fun v : V => ∀ w, ¬G.Adj (some v) w).card ≤ f) :
    ∃ F : SimpleGraph (Option V), F ≤ G ∧ F.IsAcyclic ∧
      (∀ u v : Option V, F.Reachable u v → ¬F.Reachable u none → F.dist u v ≤ 3) ∧
      (∀ v : V, F.Reachable (some v) none → F.dist (some v) none ≤ 4) ∧
      2 * Nat.card {c : F.ConnectedComponent // (none : Option V) ∉ c.supp} ≤
        Fintype.card V + f ∧
      ∃ (parent : Option V → Option (Option V)) (rk : Option V → ℕ),
        (∀ x y, F.Adj x y ↔
          x ≠ y ∧ (parent x = some y ∨ parent y = some x)) ∧
        (∀ x y, parent x = some y → rk y < rk x) ∧
        (∀ v : V, rk (some v) ≤ 3) ∧
        2 * (Finset.univ.filter fun v : V => parent (some v) = none).card ≤
          Fintype.card V + f := by
  set II := Finset.univ.filter fun v : V => ∀ w, ¬G.Adj (some v) w with hIIdef
  classical
  -- ### Step 1: a maximum-cardinality matching on the live part of `G`.
  have hexM : ∃ M : Finset (Sym2 V),
      (∀ e ∈ M, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e') ∧
      (∀ u w : V, G.Adj (some u) (some w) →
        (∃ e ∈ M, u ∈ e) ∨ (∃ e ∈ M, w ∈ e)) := by
    obtain ⟨M, hMmem, hMcard⟩ := Finset.exists_max_image
      ((Finset.univ : Finset (Finset (Sym2 V))).filter fun m =>
        (∀ e ∈ m, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
        (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e'))
      Finset.card ⟨∅, by simp⟩
    rw [Finset.mem_filter] at hMmem
    obtain ⟨-, hMedge, hMdisj⟩ := hMmem
    refine ⟨M, hMedge, hMdisj, ?_⟩
    intro u w huw
    by_contra hcon
    have hu : ∀ e ∈ M, u ∉ e := fun e he hue => hcon (Or.inl ⟨e, he, hue⟩)
    have hw : ∀ e ∈ M, w ∉ e := fun e he hwe => hcon (Or.inr ⟨e, he, hwe⟩)
    have hnew : s(u, w) ∉ M := fun hmem => hu _ hmem (Sym2.mem_mk_left u w)
    have hmem2 : insert s(u, w) M ∈
        ((Finset.univ : Finset (Finset (Sym2 V))).filter fun m =>
          (∀ e ∈ m, e ∈ (SimpleGraph.comap some G).edgeSet) ∧
          (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e')) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact huw
        · exact hMedge e he'
      · intro e he e' he' hee x hxe hxe'
        rcases Finset.mem_insert.mp he with rfl | he1
        · rcases Finset.mem_insert.mp he' with rfl | he2
          · exact hee rfl
          · rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact hu e' he2 hxe'
            · exact hw e' he2 hxe'
        · rcases Finset.mem_insert.mp he' with rfl | he2
          · rcases Sym2.mem_iff.mp hxe' with rfl | rfl
            · exact hu e he1 hxe
            · exact hw e he1 hxe
          · exact hMdisj e he1 e' he2 hee x hxe hxe'
    have hcard := hMcard _ hmem2
    rw [Finset.card_insert_of_notMem hnew] at hcard
    omega
  obtain ⟨M, hMedge, hMdisj, hMmax⟩ := hexM
  -- ### Step 2: basic facts about the matching.
  have hMout : ∀ e ∈ M, G.Adj (some (efst e)) (some (esnd e)) := by
    intro e he
    have h := hMedge e he
    rw [sym2_eq_mk e] at h
    exact h
  have hMne : ∀ e ∈ M, efst e ≠ esnd e := by
    intro e he h
    exact (hMout e he).ne (congrArg some h)
  have huniq : ∀ e, e ∈ M → ∀ e', e' ∈ M → ∀ x : V, x ∈ e → x ∈ e' → e = e' := by
    intro e he e' he' x hx hx'
    by_contra hne
    exact hMdisj e he e' he' hne x hx hx'
  have hmatched_hasnbr : ∀ e, e ∈ M → ∀ x, x ∈ e → ∃ w : V, G.Adj (some x) (some w) := by
    intro e he x hx
    rcases mem_out_cases hx with rfl | rfl
    · exact ⟨esnd e, hMout e he⟩
    · exact ⟨efst e, (hMout e he).symm⟩
  -- ### Step 3: pointwise choice of the parent map, rank and hub.
  have hex : ∀ x : Option V, ∃ (o : Option (Option V)) (r : ℕ) (hb : Option (Sym2 V)),
      (x = none ∧ o = none ∧ r = 0 ∧ hb = none) ∨
      (∃ v : V, x = some v ∧
        ((∃ e ∈ M, v ∈ e ∧ hb = some e ∧
            ((v = efst e ∧ o = none ∧ r = 1) ∨
             (v = esnd e ∧ o = some (some (efst e)) ∧ r = 2))) ∨
         ((∀ e ∈ M, v ∉ e) ∧ r = 3 ∧
            ((∃ w : V, (∃ e ∈ M, w ∈ e ∧ hb = some e) ∧ G.Adj (some v) (some w) ∧
                o = some (some w)) ∨
             ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none ∧
                o = some none ∧ hb = none) ∨
             ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ ¬G.Adj (some v) none ∧
                o = none ∧ hb = none))))) := by
    intro x
    rcases x with _ | v
    · exact ⟨none, 0, none, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · by_cases hm : ∃ e ∈ M, v ∈ e
      · obtain ⟨e, he, hv⟩ := hm
        rcases mem_out_cases hv with h1 | h2
        · exact ⟨none, 1, some e, Or.inr ⟨v, rfl, Or.inl ⟨e, he, hv, rfl,
            Or.inl ⟨h1, rfl, rfl⟩⟩⟩⟩
        · exact ⟨some (some (efst e)), 2, some e, Or.inr ⟨v, rfl, Or.inl ⟨e, he, hv, rfl,
            Or.inr ⟨h2, rfl, rfl⟩⟩⟩⟩
      · have hm' : ∀ e ∈ M, v ∉ e := fun e he hv => hm ⟨e, he, hv⟩
        by_cases hl : ∃ w : V, G.Adj (some v) (some w)
        · obtain ⟨w, hw⟩ := hl
          have hwm : ∃ e ∈ M, w ∈ e := by
            rcases hMmax v w hw with h | h
            · exact absurd h hm
            · exact h
          obtain ⟨e, he, hwe⟩ := hwm
          exact ⟨some (some w), 3, some e, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
            Or.inl ⟨w, ⟨e, he, hwe, rfl⟩, hw, rfl⟩⟩⟩⟩
        · have hl' : ∀ w : V, ¬G.Adj (some v) (some w) := fun w hw => hl ⟨w, hw⟩
          by_cases hr : G.Adj (some v) none
          · exact ⟨some none, 3, none, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
              Or.inr (Or.inl ⟨hl', hr, rfl, rfl⟩)⟩⟩⟩
          · exact ⟨none, 3, none, Or.inr ⟨v, rfl, Or.inr ⟨hm', rfl,
              Or.inr (Or.inr ⟨hl', hr, rfl, rfl⟩)⟩⟩⟩
  choose par rk hub hspec using hex
  have hparnone : par none = none := by
    rcases hspec none with ⟨-, h, -, -⟩ | ⟨v, hv, -⟩
    · exact h
    · exact absurd hv (by simp)
  have hrknone : rk none = 0 := by
    rcases hspec none with ⟨-, -, h, -⟩ | ⟨v, hv, -⟩
    · exact h
    · exact absurd hv (by simp)
  have hsome : ∀ v : V,
      (∃ e ∈ M, v ∈ e ∧ hub (some v) = some e ∧
        ((v = efst e ∧ par (some v) = none ∧ rk (some v) = 1) ∨
         (v = esnd e ∧ par (some v) = some (some (efst e)) ∧ rk (some v) = 2))) ∨
      ((∀ e ∈ M, v ∉ e) ∧ rk (some v) = 3 ∧
        ((∃ w : V, (∃ e ∈ M, w ∈ e ∧ hub (some v) = some e) ∧ G.Adj (some v) (some w) ∧
            par (some v) = some (some w)) ∨
         ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none ∧
            par (some v) = some none ∧ hub (some v) = none) ∨
         ((∀ w : V, ¬G.Adj (some v) (some w)) ∧ ¬G.Adj (some v) none ∧
            par (some v) = none ∧ hub (some v) = none))) := by
    intro v
    rcases hspec (some v) with ⟨h, -⟩ | ⟨v', hv', h⟩
    · exact absurd h (by simp)
    · obtain rfl : v = v' := Option.some.inj hv'
      exact h
  -- ### Step 4: rank decrease along the parent map; the forest `F`.
  have hdec : ∀ x y, par x = some y → rk y < rk x := by
    intro x y hxy
    rcases x with _ | v
    · rw [hparnone] at hxy
      exact absurd hxy (by simp)
    · rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨-, hpar, hrk2⟩⟩ | ⟨-, hrk3, hcase⟩
      · rw [hpar] at hxy
        exact absurd hxy (by simp)
      · rw [hpar] at hxy
        obtain rfl : some (efst e) = y := Option.some.inj hxy
        rcases hsome (efst e) with ⟨e', he', hv', -, ⟨-, -, hrk1⟩ | ⟨h2', -, -⟩⟩ |
          ⟨hunm', -, -⟩
        · omega
        · rw [huniq e' he' e he (efst e) hv' (efst_mem e)] at h2'
          exact absurd h2' (hMne e he)
        · exact absurd (efst_mem e) (hunm' e he)
      · rcases hcase with ⟨w, ⟨e, he, hwe, -⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
        · rw [hpar] at hxy
          obtain rfl : some w = y := Option.some.inj hxy
          rcases hsome w with ⟨e', he', hv', -, ⟨-, -, hrk'⟩ | ⟨-, -, hrk'⟩⟩ | ⟨hunm', -, -⟩
          · omega
          · omega
          · exact absurd hwe (hunm' e he)
        · rw [hpar] at hxy
          obtain rfl : (none : Option V) = y := Option.some.inj hxy
          omega
        · rw [hpar] at hxy
          exact absurd hxy (by simp)
  have hrkle3 : ∀ v : V, rk (some v) ≤ 3 := by
    intro v
    rcases hsome v with ⟨e, he, hv, hhub, hcase⟩ | ⟨hunm, hrk, hcase⟩
    · rcases hcase with ⟨hfst, hpar, hrk⟩ | ⟨hsnd, hpar, hrk⟩ <;> omega
    · omega
  have hFadj : ∀ x y, par x = some y → (pgraph par).Adj x y := by
    intro x y h
    rw [pgraph_adj]
    refine ⟨?_, Or.inl h⟩
    intro heq
    subst heq
    exact lt_irrefl _ (hdec x x h)
  -- ### Step 5: hub bookkeeping.
  have hhub_matched : ∀ (x : V) (e : Sym2 V), e ∈ M → x ∈ e → hub (some x) = some e := by
    intro x e he hx
    rcases hsome x with ⟨e', he', hv', hhb', -⟩ | ⟨hunm, -, -⟩
    · rwa [huniq e' he' e he x hv' hx] at hhb'
    · exact absurd hx (hunm e he)
  have hhub_M : ∀ (x : V) (e : Sym2 V), hub (some x) = some e → e ∈ M := by
    intro x e hx
    rcases hsome x with ⟨e', he', -, hhb', -⟩ | ⟨-, -, hcase⟩
    · rw [hhb'] at hx
      exact (Option.some.inj hx) ▸ he'
    · rcases hcase with ⟨w, ⟨e', he', -, hhb'⟩, -, -⟩ | ⟨-, -, -, hhb'⟩ | ⟨-, -, -, hhb'⟩
      · rw [hhb'] at hx
        exact (Option.some.inj hx) ▸ he'
      · rw [hhb'] at hx
        exact absurd hx (by simp)
      · rw [hhb'] at hx
        exact absurd hx (by simp)
  have hchild_matched : ∀ w v : V, par (some w) = some (some v) → ∃ e ∈ M, v ∈ e := by
    intro w v h
    rcases hsome w with ⟨e, he, hw, -, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      obtain rfl : efst e = v := Option.some.inj (Option.some.inj h)
      exact ⟨e, he, efst_mem e⟩
    · rcases hcase with ⟨w', ⟨e, he, hwe, -⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        obtain rfl : w' = v := Option.some.inj (Option.some.inj h)
        exact ⟨e, he, hwe⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · rw [hpar] at h
        exact absurd h (by simp)
  have hpar_live : ∀ v w : V, par (some v) = some (some w) →
      ∃ e ∈ M, hub (some v) = some e ∧ hub (some w) = some e := by
    intro v w h
    rcases hsome v with ⟨e, he, hv, hhb, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      obtain rfl : efst e = w := Option.some.inj (Option.some.inj h)
      exact ⟨e, he, hhb, hhub_matched _ e he (efst_mem e)⟩
    · rcases hcase with ⟨w', ⟨e, he, hwe, hhb⟩, -, hpar⟩ | ⟨-, -, hpar, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        obtain rfl : w' = w := Option.some.inj (Option.some.inj h)
        exact ⟨e, he, hhb, hhub_matched _ e he hwe⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · rw [hpar] at h
        exact absurd h (by simp)
  have hAdj_live : ∀ v w : V, (pgraph par).Adj (some v) (some w) →
      ∃ e ∈ M, hub (some v) = some e ∧ hub (some w) = some e := by
    intro v w h
    rw [pgraph_adj] at h
    rcases h.2 with h' | h'
    · exact hpar_live v w h'
    · obtain ⟨e, he, h1, h2⟩ := hpar_live w v h'
      exact ⟨e, he, h2, h1⟩
  have hAdj_root : ∀ x : Option V, (pgraph par).Adj x none →
      ∃ v : V, x = some v ∧ par (some v) = some none := by
    intro x h
    rw [pgraph_adj] at h
    rcases h.2 with h' | h'
    · rcases x with _ | v
      · exact absurd rfl h.1
      · exact ⟨v, rfl, h'⟩
    · rw [hparnone] at h'
      exact absurd h' (by simp)
  have hpar_root : ∀ v : V, par (some v) = some none →
      (∀ w : V, ¬G.Adj (some v) (some w)) ∧ G.Adj (some v) none := by
    intro v h
    rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨-, -, hcase⟩
    · rw [hpar] at h
      exact absurd h (by simp)
    · rw [hpar] at h
      exact absurd (Option.some.inj h) (by simp)
    · rcases hcase with ⟨w, -, -, hpar⟩ | ⟨hnl, hroot, -, -⟩ | ⟨-, -, hpar, -⟩
      · rw [hpar] at h
        exact absurd (Option.some.inj h) (by simp)
      · exact ⟨hnl, hroot⟩
      · rw [hpar] at h
        exact absurd h (by simp)
  -- ### Step 6: distance bookkeeping inside a double star.
  have hAdj_dist1 : ∀ x y, (pgraph par).Adj x y → (pgraph par).dist x y ≤ 1 := by
    intro x y h
    have := SimpleGraph.dist_le (Walk.cons h Walk.nil)
    simpa using this
  have hsum : ∀ (v : V) (e : Sym2 V), e ∈ M → hub (some v) = some e →
      (pgraph par).Reachable (some v) (some (efst e)) ∧
      (pgraph par).Reachable (some v) (some (esnd e)) ∧
      (pgraph par).dist (some v) (some (efst e)) +
        (pgraph par).dist (some v) (some (esnd e)) ≤ 3 := by
    intro v e he hhb
    have hedge : (pgraph par).Adj (some (esnd e)) (some (efst e)) := by
      rcases hsome (esnd e) with ⟨e', he', hv', -, ⟨h1, -, -⟩ | ⟨-, hpar, -⟩⟩ | ⟨hunm, -, -⟩
      · rw [huniq e' he' e he (esnd e) hv' (esnd_mem e)] at h1
        exact absurd h1.symm (hMne e he)
      · have he'e : e' = e := huniq e' he' e he (esnd e) hv' (esnd_mem e)
        subst he'e
        exact hFadj _ _ hpar
      · exact absurd (esnd_mem e) (hunm e he)
    rcases hsome v with ⟨e', he', hv', hhb', hbr⟩ | ⟨-, -, hcase⟩
    · have he'e : e' = e := by
        rw [hhb'] at hhb
        exact Option.some.inj hhb
      subst he'e
      rcases hbr with ⟨h1, -, -⟩ | ⟨h2, -, -⟩
      · subst h1
        have d0 : (pgraph par).dist (some (efst e')) (some (efst e')) = 0 :=
          SimpleGraph.dist_self
        have d1 : (pgraph par).dist (some (efst e')) (some (esnd e')) ≤ 1 := by
          have := hAdj_dist1 _ _ hedge
          have hcomm : (pgraph par).dist (some (esnd e')) (some (efst e')) =
              (pgraph par).dist (some (efst e')) (some (esnd e')) := SimpleGraph.dist_comm
          omega
        exact ⟨SimpleGraph.Reachable.refl _, hedge.symm.reachable, by omega⟩
      · subst h2
        have d0 : (pgraph par).dist (some (esnd e')) (some (esnd e')) = 0 :=
          SimpleGraph.dist_self
        have d1 : (pgraph par).dist (some (esnd e')) (some (efst e')) ≤ 1 :=
          hAdj_dist1 _ _ hedge
        exact ⟨hedge.reachable, SimpleGraph.Reachable.refl _, by omega⟩
    · rcases hcase with ⟨w, ⟨e', he', hwe, hhb'⟩, -, hpar⟩ | ⟨-, -, -, hhb'⟩ | ⟨-, -, -, hhb'⟩
      · have he'e : e' = e := by
          rw [hhb'] at hhb
          exact Option.some.inj hhb
        subst he'e
        have hvw : (pgraph par).Adj (some v) (some w) := hFadj _ _ hpar
        have dvw : (pgraph par).dist (some v) (some w) ≤ 1 := hAdj_dist1 _ _ hvw
        rcases mem_out_cases hwe with hw1 | hw2
        · subst hw1
          have r1 : (pgraph par).Reachable (some v) (some (efst e')) := hvw.reachable
          have r2 : (pgraph par).Reachable (some v) (some (esnd e')) :=
            r1.trans hedge.symm.reachable
          have tri := r1.dist_triangle_left (some (esnd e'))
          have d2 : (pgraph par).dist (some (efst e')) (some (esnd e')) ≤ 1 := by
            have := hAdj_dist1 _ _ hedge
            have hcomm : (pgraph par).dist (some (esnd e')) (some (efst e')) =
                (pgraph par).dist (some (efst e')) (some (esnd e')) := SimpleGraph.dist_comm
            omega
          exact ⟨r1, r2, by omega⟩
        · subst hw2
          have r2 : (pgraph par).Reachable (some v) (some (esnd e')) := hvw.reachable
          have r1 : (pgraph par).Reachable (some v) (some (efst e')) :=
            r2.trans hedge.reachable
          have tri := r2.dist_triangle_left (some (efst e'))
          have d2 : (pgraph par).dist (some (esnd e')) (some (efst e')) ≤ 1 :=
            hAdj_dist1 _ _ hedge
          exact ⟨r1, r2, by omega⟩
      · rw [hhb'] at hhb
        exact absurd hhb (by simp)
      · rw [hhb'] at hhb
        exact absurd hhb (by simp)
  -- ### Step 7: the root component is a star around the root.
  have hrootstar : ∀ x y, (pgraph par).Adj x y →
      (x = none ∨ ∃ w : V, x = some w ∧ par (some w) = some none) →
      (y = none ∨ ∃ w : V, y = some w ∧ par (some w) = some none) := by
    rintro x y hxy (rfl | ⟨w, rfl, hw⟩)
    · obtain ⟨v', hv', hpar'⟩ := hAdj_root _ hxy.symm
      exact Or.inr ⟨v', hv', hpar'⟩
    · rw [pgraph_adj] at hxy
      rcases hxy.2 with h' | h'
      · rw [hw] at h'
        exact Or.inl (Option.some.inj h').symm
      · rcases y with _ | wy
        · exact Or.inl rfl
        · obtain ⟨e, he, hwem⟩ := hchild_matched wy w h'
          obtain ⟨w', hw'⟩ := hmatched_hasnbr e he w hwem
          obtain ⟨hnl, -⟩ := hpar_root w hw
          exact absurd hw' (hnl w')
  -- ### Step 8: `F ≤ G`.
  have hle : pgraph par ≤ G := by
    have key : ∀ x y, par x = some y → G.Adj x y := by
      intro x y h
      rcases x with _ | v
      · rw [hparnone] at h
        exact absurd h (by simp)
      · rcases hsome v with ⟨e, he, hv, -, ⟨-, hpar, -⟩ | ⟨h2, hpar, -⟩⟩ | ⟨-, -, hcase⟩
        · rw [hpar] at h
          exact absurd h (by simp)
        · rw [hpar] at h
          obtain rfl : some (efst e) = y := Option.some.inj h
          rw [h2]
          exact (hMout e he).symm
        · rcases hcase with ⟨w, ⟨e, he, hwe, -⟩, hadj, hpar⟩ | ⟨-, hroot, hpar, -⟩ |
            ⟨-, -, hpar, -⟩
          · rw [hpar] at h
            obtain rfl : some w = y := Option.some.inj h
            exact hadj
          · rw [hpar] at h
            obtain rfl : (none : Option V) = y := Option.some.inj h
            exact hroot
          · rw [hpar] at h
            exact absurd h (by simp)
    intro x y hxy
    rw [pgraph_adj] at hxy
    rcases hxy.2 with h | h
    · exact key _ _ h
    · exact (key _ _ h).symm
  -- ### Step 9: unrooted components have diameter at most 3.
  have hdiam : ∀ u v : Option V, (pgraph par).Reachable u v →
      ¬(pgraph par).Reachable u none → (pgraph par).dist u v ≤ 3 := by
    intro u v hru hnr
    rcases u with _ | vu
    · exact absurd (SimpleGraph.Reachable.refl _) hnr
    rcases v with _ | vv
    · exact absurd hru hnr
    rcases hE : hub (some vu) with _ | e
    · rcases hsome vu with ⟨e, he, hv, hhb, -⟩ | ⟨hunm, -, hcase⟩
      · rw [hhb] at hE
        exact absurd hE (by simp)
      · rcases hcase with ⟨w, ⟨e, he, hwe, hhb⟩, -, -⟩ | ⟨hnl, hroot, hpar, -⟩ |
          ⟨hnl, hnr', hpar, -⟩
        · rw [hhb] at hE
          exact absurd hE (by simp)
        · exact absurd (hFadj _ _ hpar).reachable hnr
        · -- `vu` is fully isolated: its component is a singleton.
          have hnoadj : ∀ y, ¬(pgraph par).Adj (some vu) y := by
            intro y hy
            rw [pgraph_adj] at hy
            rcases hy.2 with h' | h'
            · rw [hpar] at h'
              exact absurd h' (by simp)
            · rcases y with _ | w
              · rw [hparnone] at h'
                exact absurd h' (by simp)
              · obtain ⟨e, he, hve⟩ := hchild_matched w vu h'
                obtain ⟨w', hw'⟩ := hmatched_hasnbr e he vu hve
                exact absurd hw' (hnl w')
          have hvv := reachable_invariant (Q := fun z => z = some vu)
            (fun x y hxy hx => absurd (hx ▸ hxy) (hnoadj y)) hru rfl
          obtain rfl : vv = vu := Option.some.inj hvv
          simp [SimpleGraph.dist_self]
    · -- `vu` lies in the double star of the matching edge `e`.
      have heM : e ∈ M := hhub_M vu e hE
      have hinv : ∀ x y, (pgraph par).Adj x y →
          (∃ vz : V, x = some vz ∧ hub (some vz) = some e) →
          (∃ vz : V, y = some vz ∧ hub (some vz) = some e) := by
        rintro x y hxy ⟨vx, rfl, hx⟩
        rcases y with _ | vy
        · obtain ⟨v', hv', hpar'⟩ := hAdj_root _ hxy
          obtain rfl : vx = v' := Option.some.inj hv'
          obtain ⟨hnl, -⟩ := hpar_root _ hpar'
          rcases hsome vx with ⟨e', he', hv'', -, -⟩ | ⟨-, -, hcase⟩
          · obtain ⟨w', hw'⟩ := hmatched_hasnbr e' he' vx hv''
            exact absurd hw' (hnl w')
          · rcases hcase with ⟨w, ⟨e', he', hwe, -⟩, hadj', -⟩ | ⟨-, -, -, hhb'⟩ |
              ⟨-, -, -, hhb'⟩
            · exact absurd hadj' (hnl w)
            · rw [hhb'] at hx
              exact absurd hx (by simp)
            · rw [hhb'] at hx
              exact absurd hx (by simp)
        · obtain ⟨e', he', h1, h2⟩ := hAdj_live vx vy hxy
          rw [hx] at h1
          obtain rfl : e = e' := Option.some.inj h1
          exact ⟨vy, rfl, h2⟩
      obtain ⟨vv', hvv', hEv⟩ := reachable_invariant hinv hru ⟨vu, rfl, hE⟩
      obtain rfl : vv = vv' := Option.some.inj hvv'
      obtain ⟨ru1, ru2, hdu⟩ := hsum vu e heM hE
      obtain ⟨rv1, rv2, hdv⟩ := hsum vv e heM hEv
      have t1 := ru1.dist_triangle_left (some vv)
      have t2 := ru2.dist_triangle_left (some vv)
      have c1 : (pgraph par).dist (some (efst e)) (some vv) =
          (pgraph par).dist (some vv) (some (efst e)) := SimpleGraph.dist_comm
      have c2 : (pgraph par).dist (some (esnd e)) (some vv) =
          (pgraph par).dist (some vv) (some (esnd e)) := SimpleGraph.dist_comm
      omega
  -- ### Step 10: live vertices in the rooted component are within distance 4.
  have hroot4 : ∀ v : V, (pgraph par).Reachable (some v) none →
      (pgraph par).dist (some v) none ≤ 4 := by
    intro v hrv
    rcases reachable_invariant hrootstar hrv.symm (Or.inl rfl) with h | ⟨w, hw, hpar'⟩
    · exact absurd h (by simp)
    · obtain rfl : v = w := Option.some.inj hw
      have h1 := hAdj_dist1 _ _ (hFadj _ _ hpar')
      omega
  -- ### Step 11: counting the components that avoid the root.
  have hIA : ∀ a : V, a ∈ M.image efst ∪ II →
      (none : Option V) ∉ ((pgraph par).connectedComponentMk (some a)).supp := by
    intro a ha hmem
    rw [ConnectedComponent.mem_supp_iff] at hmem
    have hreach : (pgraph par).Reachable none (some a) := ConnectedComponent.eq.mp hmem
    rcases reachable_invariant hrootstar hreach (Or.inl rfl) with h | ⟨w, hw, hpar'⟩
    · exact absurd h (by simp)
    · obtain rfl : a = w := Option.some.inj hw
      obtain ⟨hnl, hroot⟩ := hpar_root a hpar'
      rcases Finset.mem_union.mp ha with hA | hII
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (efst_mem e)
        exact absurd hw' (hnl w')
      · rw [hIIdef] at hII
        exact absurd hroot ((Finset.mem_filter.mp hII).2 none)
  have hsurj : Function.Surjective
      (fun a : {a : V // a ∈ M.image efst ∪ II} =>
        (⟨(pgraph par).connectedComponentMk (some a.1), hIA a.1 a.2⟩ :
          {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp})) := by
    rintro ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := c.exists_rep
    rcases x with _ | vx
    · exact absurd ((ConnectedComponent.mem_supp_iff _ _).mpr rfl) hc
    · rcases hsome vx with ⟨e, he, hv, hhb, -⟩ | ⟨-, -, hcase⟩
      · refine ⟨⟨efst e, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩, ?_⟩
        exact Subtype.ext (ConnectedComponent.sound (hsum vx e he hhb).1.symm)
      · rcases hcase with ⟨w, ⟨e, he, hwe, hhb⟩, -, -⟩ | ⟨-, -, hpar, -⟩ | ⟨hnl, hnr', -, -⟩
        · refine ⟨⟨efst e, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩, ?_⟩
          exact Subtype.ext (ConnectedComponent.sound (hsum vx e he hhb).1.symm)
        · have hreach : (pgraph par).Reachable (some vx) none := (hFadj _ _ hpar).reachable
          exact absurd ((ConnectedComponent.mem_supp_iff _ _).mpr
            (ConnectedComponent.sound hreach.symm)) hc
        · refine ⟨⟨vx, Finset.mem_union_right _ ?_⟩, ?_⟩
          · rw [hIIdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            intro w
            cases w with
            | none => exact hnr'
            | some w' => exact hnl w'
          · exact Subtype.ext rfl
  have hAcard : (M.image efst).card = M.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    exact huniq e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') (efst e) (efst_mem e)
      (by rw [h]; exact efst_mem e')
  have hBcard : (M.image esnd).card = M.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    exact huniq e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') (esnd e) (esnd_mem e)
      (by rw [h]; exact esnd_mem e')
  have hABdisj : Disjoint (M.image efst) (M.image esnd) := by
    rw [Finset.disjoint_left]
    intro a haA haB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨e', he', h2⟩ := Finset.mem_image.mp haB
    have he'e : e' = e := huniq e' he' e he (efst e) (by rw [← h2]; exact esnd_mem e')
      (efst_mem e)
    subst he'e
    exact hMne e' he (by rw [h2])
  have hAIdisj : Disjoint (M.image efst) II := by
    rw [Finset.disjoint_left]
    intro a haA haI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (efst_mem e)
    rw [hIIdef] at haI
    exact (Finset.mem_filter.mp haI).2 (some w') hw'
  have hBIdisj : Disjoint (M.image esnd) II := by
    rw [Finset.disjoint_left]
    intro a haA haI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp haA
    obtain ⟨w', hw'⟩ := hmatched_hasnbr e he _ (esnd_mem e)
    rw [hIIdef] at haI
    exact (Finset.mem_filter.mp haI).2 (some w') hw'
  have hcard2 : (M.image efst).card + (M.image esnd).card + II.card ≤ Fintype.card V := by
    have hd : Disjoint (M.image efst ∪ M.image esnd) II :=
      Finset.disjoint_union_left.mpr ⟨hAIdisj, hBIdisj⟩
    have h1 : (M.image efst ∪ M.image esnd ∪ II).card =
        (M.image efst).card + (M.image esnd).card + II.card := by
      rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hABdisj]
    exact h1 ▸ Finset.card_le_univ _
  have hcard1 : Nat.card {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp} ≤
      (M.image efst ∪ II).card := by
    calc Nat.card {c : (pgraph par).ConnectedComponent // (none : Option V) ∉ c.supp}
        ≤ Nat.card {a : V // a ∈ M.image efst ∪ II} :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = (M.image efst ∪ II).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcount : 2 * Nat.card {c : (pgraph par).ConnectedComponent //
      (none : Option V) ∉ c.supp} ≤ Fintype.card V + f := by
    have h3 : (M.image efst ∪ II).card ≤ (M.image efst).card + II.card :=
      Finset.card_union_le _ _
    have h4 : II.card ≤ f := hf
    omega
  have hrootsub : (Finset.univ.filter fun v : V => par (some v) = none) ⊆
      M.image efst ∪ II := by
    intro v hv
    have hp := (Finset.mem_filter.mp hv).2
    rcases hsome v with ⟨e, he, hve, hhub, hcase⟩ | ⟨hunm, hrk, hcase⟩
    · rcases hcase with ⟨hfst, hpar, hrk⟩ | ⟨hsnd, hpar, hrk⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨e, he, hfst.symm⟩
      · rw [hpar] at hp
        contradiction
    · rcases hcase with ⟨w, hw, hadj, hpar⟩ | ⟨hnl, hroot, hpar, hhub⟩ |
          ⟨hnl, hroot, hpar, hhub⟩
      · rw [hpar] at hp
        contradiction
      · rw [hpar] at hp
        contradiction
      · apply Finset.mem_union_right
        rw [hIIdef]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro y
        cases y with
        | none => exact hroot
        | some w => exact hnl w
  have hrootcard : (Finset.univ.filter fun v : V => par (some v) = none).card ≤
      (M.image efst ∪ II).card := Finset.card_le_card hrootsub
  have hrootcount :
      2 * (Finset.univ.filter fun v : V => par (some v) = none).card ≤
        Fintype.card V + f := by
    have h3 : (M.image efst ∪ II).card ≤ (M.image efst).card + II.card :=
      Finset.card_union_le _ _
    have h4 : II.card ≤ f := hf
    omega
  exact ⟨pgraph par, hle, pgraph_isAcyclic par rk hdec, hdiam, hroot4, hcount,
    par, rk, pgraph_adj par, hdec, hrkle3, hrootcount⟩

end NUS
