/-
# A common random cut (Section 3, Lemma 3.1)

Configurations on a finite set `V`, the hitting relation, and the common-cut lemma.
The proof in the paper is probabilistic (a random equipartition, a second-moment
argument via the Efron–Stein inequality, and Markov/Chebyshev bounds); it is stated
here and proved below.
-/
import Mathlib

namespace NUS

universe u

/-- A configuration on `V` (Section 3): a distinguished element `j` together with a
two-element multiset `τ` (formalized as `Sym2 V`) whose support avoids `j`. -/
structure Configuration (V : Type*) where
  /-- the distinguished element -/
  j : V
  /-- the two-element multiset -/
  τ : Sym2 V
  /-- the distinguished element does not lie in the support of `τ` -/
  not_mem : j ∉ τ

/-- `T` hits the configuration `(j, τ)` if `j ∈ T` and `T` meets the support of `τ`. -/
def Hits {V : Type*} (T : Finset V) (c : Configuration V) : Prop :=
  c.j ∈ T ∧ ∃ v ∈ T, v ∈ c.τ

/-! ### Product Bernoulli measures, bare-hands

Everything in the proof of Lemma 3.1 happens on a finite probability space: a set of
independent Bernoulli(θ) coordinates.  We formalize expectations as explicit finite
sums, avoiding measure theory entirely.  The Efron–Stein inequality, in the "switch
one coordinate off" form used by the paper, is isolated and proved below. -/

namespace Bernoulli

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! The next elementary identities are used to tensorize variance one coordinate at a
time.  Keeping them in the finite-sum model avoids importing measure-theoretic
conditional expectation. -/

/-- Add a distinguished Boolean coordinate, represented by `none`. -/
def optionOutcome {i : Type*} (b : Bool) (a : i → Bool) : Option i → Bool
  | none => b
  | some t => a t

@[simp] theorem optionOutcome_none {i : Type*} (b : Bool) (a : i → Bool) :
    optionOutcome b a none = b := rfl

@[simp] theorem optionOutcome_some {i : Type*} (b : Bool) (a : i → Bool) (t : i) :
    optionOutcome b a (some t) = a t := rfl

@[simp] theorem piOptionEquivProd_symm_apply {i : Type*} (b : Bool) (a : i → Bool) :
    (Equiv.piOptionEquivProd (β := fun _ : Option i => Bool)).symm (b, a) =
      optionOutcome b a := by
  funext t
  cases t <;> rfl

theorem update_optionOutcome_none {i : Type*} [DecidableEq i] [DecidableEq (Option i)]
    (b : Bool) (a : i → Bool) :
    Function.update (optionOutcome b a) none false = optionOutcome false a := by
  funext t
  cases t <;> simp [Function.update, optionOutcome]

theorem update_optionOutcome_some {i : Type*} [DecidableEq i] [DecidableEq (Option i)]
    (b : Bool) (a : i → Bool) (t : i) :
    Function.update (optionOutcome b a) (some t) false =
      optionOutcome b (Function.update a t false) := by
  funext u
  cases u <;> simp [Function.update, optionOutcome]

/-- Pull an outcome back along an equivalence of coordinate types. -/
def reindexOutcome {a b : Type*} (e : a ≃ b) (w : b → Bool) : a → Bool :=
  fun t => w (e t)

/-- The product-Bernoulli(θ) weight of an outcome `ω : ι → Bool`. -/
noncomputable def wt (θ : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ t, if ω t then θ else 1 - θ

/-- Expectation under the product Bernoulli(θ) measure, as a finite sum. -/
noncomputable def expect (θ : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ ω, wt θ ω * F ω

/-- Variance under the product Bernoulli(θ) measure. -/
noncomputable def var (θ : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  expect θ fun ω => (F ω - expect θ F) ^ 2

theorem wt_reindexOutcome {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (θ : ℝ) (w : b → Bool) :
    wt θ (reindexOutcome e w) = wt θ w := by
  unfold wt reindexOutcome
  exact e.prod_comp (fun t => if w t then θ else 1 - θ)

theorem expect_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ) (F : (a → Bool) → ℝ) :
    expect θ F = expect θ (fun w : b → Bool => F (reindexOutcome e w)) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.piCongrLeft (fun _ : b => Bool) e).symm
    (fun w => wt θ w * F w)]
  apply Finset.sum_congr rfl
  intro w hw
  have hq : (Equiv.piCongrLeft (fun _ : b => Bool) e).symm w = reindexOutcome e w := by
    funext t
    simp [reindexOutcome]
  rw [hq]
  rw [wt_reindexOutcome]

theorem var_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ) (F : (a → Bool) → ℝ) :
    var θ F = var θ (fun w : b → Bool => F (reindexOutcome e w)) := by
  unfold var
  rw [expect_reindexOutcome e θ]
  rw [expect_reindexOutcome e θ F]

theorem reindexOutcome_update {a b : Type*} [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (w : b → Bool) (t : a) :
    reindexOutcome e (Function.update w (e t) false) =
      Function.update (reindexOutcome e w) t false := by
  funext u
  by_cases h : u = t
  · subst u
    simp [reindexOutcome]
  · have he : e u ≠ e t := fun h' => h (e.injective h')
    simp [reindexOutcome, Function.update, h, he]

theorem switchEnergy_reindexOutcome {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (F : (a → Bool) → ℝ) (w : b → Bool) :
    (∑ u : b, (F (reindexOutcome e w) -
        F (reindexOutcome e (Function.update w u false))) ^ 2) =
      ∑ t : a, (F (reindexOutcome e w) -
        F (Function.update (reindexOutcome e w) t false)) ^ 2 := by
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro t ht
  rw [reindexOutcome_update]

omit [DecidableEq ι] in
theorem wt_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ω : ι → Bool) : 0 ≤ wt θ ω :=
  Finset.prod_nonneg fun t _ => by
    by_cases h : ω t <;> simp [h] <;> linarith

/-- The weights sum to one. -/
theorem sum_wt (θ : ℝ) : ∑ ω : ι → Bool, wt θ ω = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    fun _ b => if b then θ else 1 - θ
  rw [Fintype.piFinset_univ] at h
  unfold wt
  rw [← h]
  simp

omit [DecidableEq ι] in
theorem wt_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (ω : ι → Bool) : 0 < wt θ ω :=
  Finset.prod_pos fun t _ => by
    by_cases h : ω t <;> simp [h] <;> linarith

/-- Splitting product-Bernoulli expectation at the distinguished `Option` coordinate. -/
theorem expect_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)] (θ : ℝ)
    (F : (Option i → Bool) → ℝ) :
    expect θ F = θ * expect θ (fun a : i → Bool => F (optionOutcome true a))
      + (1 - θ) * expect θ (fun a : i → Bool => F (optionOutcome false a)) := by
  classical
  unfold expect wt
  rw [← Equiv.sum_comp (Equiv.piOptionEquivProd (β := fun _ => Bool)).symm
    (fun ω => (∏ t, if ω t then θ else 1 - θ) * F ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [piOptionEquivProd_symm_apply, Fintype.prod_option, optionOutcome_none,
    optionOutcome_some, Bool.true_eq, if_true, Bool.false_eq_true, if_false]
  change (∑ a : i → Bool, (θ * ∏ t, if a t then θ else 1 - θ) *
      F (optionOutcome true a))
    + ∑ a : i → Bool, ((1 - θ) * ∏ t, if a t then θ else 1 - θ) *
      F (optionOutcome false a) = _
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;> ring

/-- The usual second-moment expression for the finite-sum variance. -/
theorem var_eq_expect_sq_sub (θ : ℝ) (F : (ι → Bool) → ℝ) :
    var θ F = expect θ (fun ω => (F ω) ^ 2) - (expect θ F) ^ 2 := by
  unfold var expect
  have hpoint : ∀ ω : ι → Bool,
      wt θ ω * (F ω - ∑ ω, wt θ ω * F ω) ^ 2 =
      wt θ ω * F ω ^ 2
        - 2 * (∑ ω, wt θ ω * F ω) * (wt θ ω * F ω)
        + (∑ ω, wt θ ω * F ω) ^ 2 * wt θ ω := by
    intro ω
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_wt]
  ring

/-- Jensen/Cauchy–Schwarz for the square under a product-Bernoulli expectation. -/
theorem sq_expect_le_expect_sq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (F : (ι → Bool) → ℝ) :
    (expect θ F) ^ 2 ≤ expect θ (fun ω => (F ω) ^ 2) := by
  unfold expect
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι → Bool))
    (fun ω => Real.sqrt (wt θ ω)) (fun ω => Real.sqrt (wt θ ω) * F ω)
  have hsqrt : ∀ ω : ι → Bool, (Real.sqrt (wt θ ω)) ^ 2 = wt θ ω := by
    intro ω
    exact Real.sq_sqrt (wt_nonneg hθ0 hθ1 ω)
  have hmul : ∀ ω : ι → Bool,
      Real.sqrt (wt θ ω) * Real.sqrt (wt θ ω) = wt θ ω := by
    intro ω
    exact Real.mul_self_sqrt (wt_nonneg hθ0 hθ1 ω)
  simpa only [← mul_assoc, hmul, hsqrt, one_mul, sum_wt, mul_one, mul_pow] using hcs

theorem expect_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {F : (ι → Bool) → ℝ}
    (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ expect θ F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (wt_nonneg hθ0 hθ1 ω) (hF ω)

theorem expect_mono {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {F G : (ι → Bool) → ℝ}
    (h : ∀ ω, F ω ≤ G ω) : expect θ F ≤ expect θ G :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (wt_nonneg hθ0 hθ1 ω)

/-- The expectation of a constant. -/
theorem expect_const (θ c : ℝ) : expect θ (fun _ : ι → Bool => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, sum_wt, one_mul]

theorem expect_add (θ : ℝ) (F G : (ι → Bool) → ℝ) :
    expect θ (fun ω => F ω + G ω) = expect θ F + expect θ G := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => mul_add _ _ _

theorem expect_sub (θ : ℝ) (F G : (ι → Bool) → ℝ) :
    expect θ (fun ω => F ω - G ω) = expect θ F - expect θ G := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => mul_sub _ _ _

theorem expect_const_mul (θ c : ℝ) (F : (ι → Bool) → ℝ) :
    expect θ (fun ω => c * F ω) = c * expect θ F := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_sum {κ : Type*} (θ : ℝ) (s : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    expect θ (fun ω => ∑ k ∈ s, F k ω) = ∑ k ∈ s, expect θ (F k) := by
  unfold expect
  calc ∑ ω, wt θ ω * ∑ k ∈ s, F k ω
      = ∑ ω, ∑ k ∈ s, wt θ ω * F k ω :=
        Finset.sum_congr rfl fun ω _ => Finset.mul_sum _ _ _
    _ = ∑ k ∈ s, ∑ ω, wt θ ω * F k ω := Finset.sum_comm

/-- Averaging: some outcome is at least the mean. -/
theorem exists_expect_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (F : (ι → Bool) → ℝ) :
    ∃ ω : ι → Bool, expect θ F ≤ F ω := by
  by_contra h
  push Not at h
  have h1 : expect θ F < expect θ F := by
    conv_rhs => rw [← expect_const θ (expect θ F) (ι := ι)]
    unfold expect
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun ω _ =>
      mul_lt_mul_of_pos_left (h ω) (wt_pos hθ0 hθ1 ω)
  exact lt_irrefl _ h1

/-- Averaging: some outcome is at most the mean. -/
theorem exists_le_expect {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (F : (ι → Bool) → ℝ) :
    ∃ ω : ι → Bool, F ω ≤ expect θ F := by
  by_contra h
  push Not at h
  have h1 : expect θ F < expect θ F := by
    conv_lhs => rw [← expect_const θ (expect θ F) (ι := ι)]
    unfold expect
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun ω _ =>
      mul_lt_mul_of_pos_left (h ω) (wt_pos hθ0 hθ1 ω)
  exact lt_irrefl _ h1

/-- Markov's inequality for the product Bernoulli measure. -/
theorem markov {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (F : (ι → Bool) → ℝ)
    (hF : ∀ ω, 0 ≤ F ω) {a : ℝ} (ha : 0 < a) :
    expect θ (fun ω => if a ≤ F ω then (1 : ℝ) else 0) ≤ expect θ F / a := by
  have h1 : ∀ ω : ι → Bool, (if a ≤ F ω then (1 : ℝ) else 0) ≤ a⁻¹ * F ω := by
    intro ω
    by_cases h : a ≤ F ω
    · rw [if_pos h, ← inv_mul_cancel₀ (ne_of_gt ha)]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    · rw [if_neg h]
      have := hF ω
      positivity
  calc expect θ (fun ω => if a ≤ F ω then (1 : ℝ) else 0)
      ≤ expect θ (fun ω => a⁻¹ * F ω) := expect_mono hθ0 hθ1 h1
    _ = a⁻¹ * expect θ F := expect_const_mul _ _ _
    _ = expect θ F / a := by rw [inv_mul_eq_div]

/-- Expectation of a product of per-coordinate functions factorizes. -/
theorem expect_prod_comp (θ : ℝ) (g : ι → Bool → ℝ) :
    expect θ (fun ω => ∏ t, g t (ω t)) = ∏ t, (θ * g t true + (1 - θ) * g t false) := by
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    fun t b => (if b then θ else 1 - θ) * g t b
  rw [Fintype.piFinset_univ] at h
  unfold expect wt
  calc ∑ ω : ι → Bool, (∏ t, if ω t then θ else 1 - θ) * ∏ t, g t (ω t)
      = ∑ ω : ι → Bool, ∏ t, (if ω t then θ else 1 - θ) * g t (ω t) :=
        Finset.sum_congr rfl fun ω _ => (Finset.prod_mul_distrib).symm
    _ = ∏ t, ∑ b : Bool, (if b then θ else 1 - θ) * g t b := h.symm
    _ = ∏ t, (θ * g t true + (1 - θ) * g t false) :=
        Finset.prod_congr rfl fun t _ => by rw [Fintype.sum_bool]; simp

/-- The probability of a cylinder event: the coordinates in `S` are on and the
coordinates in `T` are off. -/
theorem expect_cylinder (θ : ℝ) (S T : Finset ι) (hd : Disjoint S T) :
    expect θ (fun ω => if (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false) then (1 : ℝ) else 0)
      = θ ^ S.card * (1 - θ) ^ T.card := by
  have key : (fun ω : ι → Bool =>
        if (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false) then (1 : ℝ) else 0)
      = fun ω => ∏ t, (if t ∈ S then (if ω t then (1 : ℝ) else 0)
          else if t ∈ T then (if ω t then (0 : ℝ) else 1) else 1) := by
    funext ω
    by_cases h : (∀ i ∈ S, ω i = true) ∧ (∀ i ∈ T, ω i = false)
    · rw [if_pos h]
      refine (Finset.prod_eq_one fun t _ => ?_).symm
      by_cases hS : t ∈ S
      · simp [hS, h.1 t hS]
      · by_cases hT : t ∈ T
        · simp [hS, hT, h.2 t hT]
        · simp [hS, hT]
    · rw [if_neg h]
      push Not at h
      by_cases hA : ∀ i ∈ S, ω i = true
      · obtain ⟨i, hiT, hi⟩ := h hA
        simp only [ne_eq, Bool.not_eq_false] at hi
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        have hiS : i ∉ S := Finset.disjoint_right.mp hd hiT
        simp [hiS, hiT, hi]
      · push Not at hA
        obtain ⟨i, hiS, hi⟩ := hA
        simp only [ne_eq, Bool.not_eq_true] at hi
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        simp [hiS, hi]
  have h2 : ∀ t : ι, θ * (if t ∈ S then (if (true : Bool) then (1 : ℝ) else 0)
        else if t ∈ T then (if (true : Bool) then (0 : ℝ) else 1) else 1)
      + (1 - θ) * (if t ∈ S then (if (false : Bool) then (1 : ℝ) else 0)
        else if t ∈ T then (if (false : Bool) then (0 : ℝ) else 1) else 1)
      = (if t ∈ S then θ else if t ∈ T then 1 - θ else 1) := by
    intro t
    by_cases hS : t ∈ S
    · simp [hS]
    · by_cases hT : t ∈ T <;> simp [hS, hT]
  have h3 : (∏ t ∈ Finset.univ.filter (· ∈ S),
      (if t ∈ S then θ else if t ∈ T then 1 - θ else 1)) = θ ^ S.card := by
    rw [Finset.filter_univ_mem]
    rw [Finset.prod_congr rfl fun t ht => if_pos ht]
    exact Finset.prod_const θ
  have h4 : (∏ t ∈ Finset.univ.filter (fun t => ¬ t ∈ S),
      (if t ∈ S then θ else if t ∈ T then 1 - θ else 1)) = (1 - θ) ^ T.card := by
    rw [Finset.prod_congr rfl fun t ht => if_neg ((Finset.mem_filter.mp ht).2)]
    rw [Finset.prod_ite_mem]
    have hTsub : Finset.univ.filter (fun t => ¬ t ∈ S) ∩ T = T := by
      rw [Finset.inter_eq_right]
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, Finset.disjoint_right.mp hd hu⟩
    rw [hTsub]
    exact Finset.prod_const _
  rw [key]
  refine (expect_prod_comp θ (fun t b => if t ∈ S then (if b then (1 : ℝ) else 0)
      else if t ∈ T then (if b then (0 : ℝ) else 1) else 1)).trans ?_
  refine (Finset.prod_congr rfl fun t _ => h2 t).trans ?_
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S), h3, h4]

/-- Recombine an outcome from its coordinates inside and outside `p`. -/
def merge (p : ι → Prop) [DecidablePred p] (a : {i // p i} → Bool) (b : {i // ¬ p i} → Bool) :
    ι → Bool := fun i => if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩

theorem wt_merge (θ : ℝ) (p : ι → Prop) [DecidablePred p]
    (a : {i // p i} → Bool) (b : {i // ¬ p i} → Bool) :
    wt θ (merge p a b) = wt θ a * wt θ b := by
  unfold wt merge
  rw [← Fintype.prod_subtype_mul_prod_subtype p
    (fun i => if (if h : p i then a ⟨i, h⟩ else b ⟨i, h⟩) then θ else 1 - θ)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [dif_pos i.2]
  · exact Finset.prod_congr rfl fun i _ => by rw [dif_neg i.2]

/-- Expectation splits into an outer expectation over the coordinates satisfying `p`
and an inner expectation over the remaining coordinates. -/
theorem expect_split (θ : ℝ) (p : ι → Prop) [DecidablePred p] (F : (ι → Bool) → ℝ) :
    expect θ F = expect θ (fun a : {i // p i} → Bool =>
      expect θ (fun b : {i // ¬ p i} → Bool => F (merge p a b))) := by
  unfold expect
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm
    (fun ω => wt θ ω * F ω)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hm : (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm (a, b) = merge p a b := rfl
  rw [hm, wt_merge]
  ring

end Bernoulli

/-! ### Elementary inequalities -/

/-- For `0 ≤ θ ≤ 1` we have `(1-θ)^d ≤ 1/(1+θd)`. -/
theorem one_sub_pow_le_inv {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (d : ℕ) :
    (1 - θ) ^ d ≤ 1 / (1 + θ * d) := by
  induction d with
  | zero => norm_num
  | succ n ih =>
    have hpos : (0 : ℝ) < 1 + θ * n := by positivity
    have hpos' : (0 : ℝ) < 1 + θ * (n + 1 : ℕ) := by positivity
    calc (1 - θ) ^ (n + 1) = (1 - θ) ^ n * (1 - θ) := pow_succ _ _
      _ ≤ (1 / (1 + θ * n)) * (1 - θ) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ 1 / (1 + θ * (n + 1 : ℕ)) := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hpos hpos']
          push_cast
          nlinarith [sq_nonneg θ]

/-- If `θ d ≥ 1` then `1 - (1-θ)^d ≥ 1/2`. -/
theorem half_le_one_sub_pow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {d : ℕ}
    (hd : 1 ≤ θ * d) : (1 / 2 : ℝ) ≤ 1 - (1 - θ) ^ d := by
  have h := one_sub_pow_le_inv hθ0 hθ1 d
  have hpos : (0 : ℝ) < 1 + θ * d := by positivity
  have h2 : (1 : ℝ) / (1 + θ * d) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  linarith

/-- If `θ d ≤ 1` then `1 - (1-θ)^d ≥ θd/2`. -/
theorem lin_le_one_sub_pow {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {d : ℕ}
    (hd : θ * d ≤ 1) : θ * d / 2 ≤ 1 - (1 - θ) ^ d := by
  have h := one_sub_pow_le_inv hθ0 hθ1 d
  have hpos : (0 : ℝ) < 1 + θ * d := by positivity
  have hd0 : (0 : ℝ) ≤ θ * d := by positivity
  have h2 : (1 : ℝ) / (1 + θ * d) ≤ 1 - θ * d / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-- `(1-θ)^n ≤ exp (-θ n)`. -/
theorem one_sub_pow_le_exp {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    (1 - θ) ^ n ≤ Real.exp (-(θ * n)) := by
  have h1 : 1 - θ ≤ Real.exp (-θ) := by
    have := Real.add_one_le_exp (-θ)
    linarith
  calc (1 - θ) ^ n ≤ Real.exp (-θ) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-(θ * n)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

theorem exp_neg_eight_le : Real.exp (-8) ≤ (1 / 256 : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp 1 using 1 <;> norm_num
  have hp : (256 : ℝ) ≤ Real.exp 1 ^ (8 : ℕ) := by
    calc (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 8
  have he : (256 : ℝ) ≤ Real.exp 8 := by
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    simpa using hp
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 8) (by norm_num)).2 he

namespace Bernoulli

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Variance decomposition after exposing the distinguished coordinate of `Option i`. -/
theorem var_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)]
    (θ : ℝ) (F : (Option i → Bool) → ℝ) :
    var θ F =
      θ * var θ (fun a : i → Bool => F (optionOutcome true a))
      + (1 - θ) * var θ (fun a : i → Bool => F (optionOutcome false a))
      + θ * (1 - θ) *
        (expect θ (fun a : i → Bool => F (optionOutcome true a))
          - expect θ (fun a : i → Bool => F (optionOutcome false a))) ^ 2 := by
  rw [var_eq_expect_sq_sub, expect_option, expect_option,
    var_eq_expect_sq_sub, var_eq_expect_sq_sub]
  ring

/-- The coordinate switch-off energy also splits at the distinguished `Option`
coordinate. -/
theorem switchEnergy_option {i : Type*} [Fintype i] [DecidableEq i] [DecidableEq (Option i)]
    (θ : ℝ) (F : (Option i → Bool) → ℝ) :
    expect θ (fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2) =
      θ * expect θ (fun a : i → Bool =>
        (F (optionOutcome true a) - F (optionOutcome false a)) ^ 2)
      + θ * expect θ (fun a : i → Bool => ∑ t,
        (F (optionOutcome true a) -
          F (optionOutcome true (Function.update a t false))) ^ 2)
      + (1 - θ) * expect θ (fun a : i → Bool => ∑ t,
        (F (optionOutcome false a) -
          F (optionOutcome false (Function.update a t false))) ^ 2) := by
  rw [expect_option]
  have htrue : (fun a : i → Bool => ∑ t : Option i,
        (F (optionOutcome true a) -
          F (Function.update (optionOutcome true a) t false)) ^ 2) =
      (fun a => (F (optionOutcome true a) - F (optionOutcome false a)) ^ 2
        + ∑ t : i, (F (optionOutcome true a) -
          F (optionOutcome true (Function.update a t false))) ^ 2) := by
    funext a
    rw [Fintype.sum_option, update_optionOutcome_none]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [update_optionOutcome_some]
  have hfalse : (fun a : i → Bool => ∑ t : Option i,
        (F (optionOutcome false a) -
          F (Function.update (optionOutcome false a) t false)) ^ 2) =
      (fun a => ∑ t : i, (F (optionOutcome false a) -
        F (optionOutcome false (Function.update a t false))) ^ 2) := by
    funext a
    rw [Fintype.sum_option, update_optionOutcome_none]
    rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    apply Finset.sum_congr rfl
    intro t ht
    rw [update_optionOutcome_some]
  rw [htrue, hfalse, expect_add]
  ring

/-- Tensorization step for Efron–Stein when one Boolean coordinate is added. -/
theorem efron_stein_option {i : Type*} [Fintype i] [DecidableEq i]
    [DecidableEq (Option i)]
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ih : ∀ G : (i → Bool) → ℝ,
      var θ G ≤ expect θ fun a => ∑ t, (G a - G (Function.update a t false)) ^ 2)
    (F : (Option i → Bool) → ℝ) :
    var θ F ≤ expect θ fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2 := by
  let F₁ : (i → Bool) → ℝ := fun a => F (optionOutcome true a)
  let F₀ : (i → Bool) → ℝ := fun a => F (optionOutcome false a)
  have hJ : (expect θ F₁ - expect θ F₀) ^ 2 ≤
      expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
    rw [← expect_sub]
    exact sq_expect_le_expect_sq hθ0 hθ1 (fun a => F₁ a - F₀ a)
  have hcoef : 0 ≤ θ * (1 - θ) := mul_nonneg hθ0 (by linarith)
  have hcross : θ * (1 - θ) * (expect θ F₁ - expect θ F₀) ^ 2 ≤
      θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
    calc
      θ * (1 - θ) * (expect θ F₁ - expect θ F₀) ^ 2
          ≤ θ * (1 - θ) * expect θ (fun a => (F₁ a - F₀ a) ^ 2) :=
            mul_le_mul_of_nonneg_left hJ hcoef
      _ ≤ θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2) := by
        have hE : 0 ≤ expect θ (fun a => (F₁ a - F₀ a) ^ 2) :=
          expect_nonneg hθ0 hθ1 fun a => sq_nonneg _
        calc
          θ * (1 - θ) * expect θ (fun a => (F₁ a - F₀ a) ^ 2) =
              (1 - θ) * (θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2)) := by ring
          _ ≤ 1 * (θ * expect θ (fun a => (F₁ a - F₀ a) ^ 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hθ0 hE)
          _ = _ := one_mul _
  rw [var_option, switchEnergy_option]
  dsimp only [F₁, F₀] at hcross ⊢
  have h1 := ih (fun a => F (optionOutcome true a))
  have h0 := ih (fun a => F (optionOutcome false a))
  have hc1 : 0 ≤ θ := hθ0
  have hc0 : 0 ≤ 1 - θ := by linarith
  have hh1 := mul_le_mul_of_nonneg_left h1 hc1
  have hh0 := mul_le_mul_of_nonneg_left h0 hc0
  linarith

/-- Efron–Stein is invariant under a relabelling of the coordinate type. -/
theorem efron_stein_of_equiv {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (θ : ℝ)
    (h : ∀ G : (b → Bool) → ℝ,
      var θ G ≤ expect θ fun w => ∑ u, (G w - G (Function.update w u false)) ^ 2)
    (F : (a → Bool) → ℝ) :
    var θ F ≤ expect θ fun w => ∑ t, (F w - F (Function.update w t false)) ^ 2 := by
  let G : (b → Bool) → ℝ := fun w => F (reindexOutcome e w)
  rw [var_reindexOutcome e θ F]
  rw [expect_reindexOutcome e θ
    (fun w => ∑ t, (F w - F (Function.update w t false)) ^ 2)]
  have hG := h G
  apply hG.trans_eq
  apply congrArg (expect θ)
  funext w
  exact switchEnergy_reindexOutcome e F w

/-- The Efron–Stein assertion, packaged so finite-type induction can quantify over the
chosen decidable-equality instance. -/
def EfronProperty (a : Type u) [Fintype a] [DecidableEq a] : Prop :=
  ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∀ G : (a → Bool) → ℝ,
    var θ G ≤ expect θ fun w => ∑ t, (G w - G (Function.update w t false)) ^ 2

/-- **The Efron–Stein inequality** for product Bernoulli measures, in the
"conditional-variance / switch-off" form used in the proof of Lemma 3.1: writing
`Z^{(t,0)}` for the value of `Z` after forcing coordinate `t` off,

`Var(Z) ≤ E [ ∑ t (Z − Z^{(t,0)})² ]`.

This follows from the classical Efron–Stein inequality
`Var(Z) ≤ ½ ∑ t E[(Z − Z⁽ᵗ⁾)²]` (independent resampling of coordinate `t`), since for
a Bernoulli(θ) coordinate `½ E[(Z − Z⁽ᵗ⁾)²] = θ(1−θ)·E[(Z_on − Z_off)²]` while
`E[(Z − Z^{(t,0)})²] = θ·E[(Z_on − Z_off)²]`.  This is the single analytic input of
Section 3. -/
theorem efron_stein (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (F : (ι → Bool) → ℝ) :
    var θ F ≤ expect θ fun ω => ∑ t, (F ω - F (Function.update ω t false)) ^ 2 := by
  classical
  let P := fun (a : Type u) [fa : Fintype a] =>
    ∀ da : DecidableEq a, @EfronProperty a fa da
  have hall : P ι := Fintype.induction_empty_option (P := P)
    (fun a b _ e ha => by
      intro db
      letI : DecidableEq b := db
      unfold EfronProperty
      intro θ h0 h1 G
      letI : Fintype a := Fintype.ofEquiv b e.symm
      let da : DecidableEq a := Classical.decEq a
      letI : DecidableEq a := da
      exact efron_stein_of_equiv e.symm θ (ha da θ h0 h1) G)
    (by
      intro de
      letI : DecidableEq PEmpty := de
      unfold EfronProperty
      intro θ h0 h1 G
      let w₀ : PEmpty → Bool := fun x => nomatch x
      have hG : G = fun _ => G w₀ := by
        funext w
        exact congrArg G (Subsingleton.elim _ _)
      rw [hG]
      simp [var, expect_const])
    (fun a _ ha => by
      intro dopt
      let da : DecidableEq a := Classical.decEq a
      letI : DecidableEq a := da
      letI : DecidableEq (Option a) := dopt
      unfold EfronProperty
      intro θ h0 h1 G
      exact efron_stein_option θ h0 h1 (ha da θ h0 h1) G)
    ι
  exact hall (inferInstance : DecidableEq ι) θ hθ0 hθ1 F

end Bernoulli

/-! ### The coverage process of a retained family

Fix a family `R` of configurations retained for the partition `σ` (the distinguished
elements on the `true` side, the multisets on the `false` side).  For an outcome
`ω : V → Bool` (the random set `T = {v | ω v}`), an off-side vertex `v` is *covered* if
some retained configuration whose multiset contains `v` is activated (its distinguished
element is in `T`). -/

section Coverage

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A `Finset V` of cardinality `≤ 2` containing the support of a `Sym2 V`. -/
theorem sym2_card_le (z : Sym2 V) (s : Finset V) (h : ∀ v ∈ s, v ∈ z) : s.card ≤ 2 := by
  induction z using Sym2.inductionOn with
  | hf x y =>
    have hsub : s ⊆ ({x, y} : Finset V) := by
      intro v hv
      rcases Sym2.mem_iff.mp (h v hv) with h1 | h1 <;> simp [h1]
    calc s.card ≤ ({x, y} : Finset V).card := Finset.card_le_card hsub
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)

/-- Every `Sym2` element supported in `H` lies in the image of `H ×ˢ H`. -/
theorem sym2_mem_image_product (H : Finset V) (z : Sym2 V) (h : ∀ v ∈ z, v ∈ H) :
    z ∈ (H ×ˢ H).image (fun p : V × V => s(p.1, p.2)) := by
  induction z using Sym2.inductionOn with
  | hf x y =>
    refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨h x (Sym2.mem_mk_left x y), h y (Sym2.mem_mk_right x y)⟩

/-- Configurations retained by an oriented bipartition. -/
def retained (F : Finset (Configuration V)) (σ : V → Bool) : Finset (Configuration V) :=
  F.filter fun c => σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false

theorem mem_retained {F : Finset (Configuration V)} {σ : V → Bool}
    {c : Configuration V} :
    c ∈ retained F σ ↔ c ∈ F ∧ σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false := by
  simp [retained]

/-- Some bipartition retains at least one eighth of any configuration family. -/
theorem exists_large_retained (F : Finset (Configuration V)) :
    ∃ σ : V → Bool, F.card ≤ 8 * (retained F σ).card := by
  classical
  let Z : (V → Bool) → ℝ := fun σ => ((retained F σ).card : ℝ)
  have hZ : ∀ σ : V → Bool, Z σ = ∑ c ∈ F,
      if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0 := by
    intro σ
    simp only [Z, retained, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro c hc
    apply if_congr
    · simp only [Sym2.mem_toFinset]
    · rfl
    · rfl
  have hterm : ∀ c : Configuration V,
      (1 / 8 : ℝ) ≤ Bernoulli.expect (1 / 2) (fun σ : V → Bool =>
        if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) := by
    intro c
    have hd : Disjoint ({c.j} : Finset V) c.τ.toFinset := by
      rw [Finset.disjoint_left]
      intro v hvj hvτ
      rw [Finset.mem_singleton] at hvj
      subst v
      exact c.not_mem (Sym2.mem_toFinset.mp hvτ)
    rw [show (fun σ : V → Bool =>
          if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) =
        (fun σ => if (∀ i ∈ ({c.j} : Finset V), σ i = true) ∧
          (∀ i ∈ c.τ.toFinset, σ i = false) then (1 : ℝ) else 0) by
          funext σ; simp]
    rw [Bernoulli.expect_cylinder (1 / 2) {c.j} c.τ.toFinset hd]
    simp only [Finset.card_singleton, pow_one]
    have hc : c.τ.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    interval_cases hcard : c.τ.toFinset.card <;> norm_num
  have hEZ : (F.card : ℝ) / 8 ≤ Bernoulli.expect (1 / 2) Z := by
    rw [show Z = (fun σ : V → Bool => ∑ c ∈ F,
      if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) from
        funext hZ]
    rw [Bernoulli.expect_sum]
    have hs : (∑ c ∈ F, (1 / 8 : ℝ)) ≤ ∑ c ∈ F,
        Bernoulli.expect (1 / 2) (fun σ : V → Bool =>
          if σ c.j = true ∧ ∀ v ∈ c.τ.toFinset, σ v = false then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun c _ => hterm c
    simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hs
  obtain ⟨σ, hσ⟩ := Bernoulli.exists_expect_le (θ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) Z
  refine ⟨σ, ?_⟩
  have hreal : (F.card : ℝ) ≤ 8 * ((retained F σ).card : ℝ) := by
    dsimp only [Z] at hσ
    linarith
  exact_mod_cast hreal

/-- The vertices on the "off" side of the partition `σ`. -/
def offSide (σ : V → Bool) : Finset V := Finset.univ.filter (fun v => σ v = false)

theorem mem_offSide {σ : V → Bool} {v : V} : v ∈ offSide σ ↔ σ v = false := by
  unfold offSide; simp

/-- The distinguished elements of the configurations of `R` whose multiset contains `v`. -/
def covSet (R : Finset (Configuration V)) (v : V) : Finset V :=
  (R.filter (fun c => v ∈ c.τ)).image Configuration.j

theorem mem_covSet {R : Finset (Configuration V)} {v u : V} :
    u ∈ covSet R v ↔ ∃ c ∈ R, v ∈ c.τ ∧ c.j = u := by
  unfold covSet
  simp [Finset.mem_image, Finset.mem_filter, and_assoc]

/-- The covered off-side vertices. -/
def coveredSet (R : Finset (Configuration V)) (σ : V → Bool) (ω : V → Bool) : Finset V :=
  (offSide σ).filter (fun v => ∃ u ∈ covSet R v, ω u = true)

theorem mem_coveredSet {R : Finset (Configuration V)} {σ ω : V → Bool} {v : V} :
    v ∈ coveredSet R σ ω ↔ σ v = false ∧ ∃ u ∈ covSet R v, ω u = true := by
  unfold coveredSet
  rw [Finset.mem_filter, mem_offSide]

theorem coveredSet_update_subset (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) :
    coveredSet R σ (Function.update ω u false) ⊆ coveredSet R σ ω := by
  intro v hv
  obtain ⟨h1, w, hw, hww⟩ := mem_coveredSet.mp hv
  refine mem_coveredSet.mpr ⟨h1, w, hw, ?_⟩
  by_cases h : w = u
  · subst h
    rw [Function.update_self] at hww
    simp at hww
  · rwa [Function.update_of_ne h] at hww

/-- The off-side vertices losing coverage when coordinate `u` is switched off. -/
def loseSet (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) : Finset V :=
  coveredSet R σ ω \ coveredSet R σ (Function.update ω u false)

theorem card_loseSet (R : Finset (Configuration V)) (σ ω : V → Bool) (u : V) :
    (loseSet R σ ω u).card
      = (coveredSet R σ ω).card - (coveredSet R σ (Function.update ω u false)).card :=
  Finset.card_sdiff_of_subset (coveredSet_update_subset R σ ω u)

/-- If `v` loses coverage when `u` is switched off, then `u` is the unique activated
distinguished element covering `v`. -/
theorem eq_of_mem_loseSet {R : Finset (Configuration V)} {σ ω : V → Bool} {u v w : V}
    (hv : v ∈ loseSet R σ ω u) (hw : w ∈ covSet R v) (hww : ω w = true) : w = u := by
  rw [loseSet, Finset.mem_sdiff] at hv
  by_contra hne
  apply hv.2
  exact mem_coveredSet.mpr ⟨(mem_coveredSet.mp hv.1).1, w, hw,
    by rwa [Function.update_of_ne hne]⟩

/-- Switching off one coordinate uncovers at most two vertices. -/
theorem card_loseSet_le_two {R : Finset (Configuration V)}
    (hj : Set.InjOn Configuration.j (R : Set (Configuration V))) (σ ω : V → Bool) (u : V) :
    (loseSet R σ ω u).card ≤ 2 := by
  by_cases hc : ∃ c ∈ R, c.j = u
  · obtain ⟨c, hcR, hcj⟩ := hc
    refine sym2_card_le c.τ _ fun v hv => ?_
    have hv1 : v ∈ coveredSet R σ ω := (Finset.mem_sdiff.mp hv).1
    obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp hv1
    have hwu : w = u := eq_of_mem_loseSet hv hw hww
    subst hwu
    obtain ⟨c', hc'R, hvτ, hc'j⟩ := mem_covSet.mp hw
    have hcc : c' = c := hj hc'R hcR (hc'j.trans hcj.symm)
    exact hcc ▸ hvτ
  · have hempty : loseSet R σ ω u = ∅ := by
      rw [loseSet, Finset.sdiff_eq_empty_iff_subset]
      intro v hv
      obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp hv
      refine mem_coveredSet.mpr ⟨hoff, w, hw, ?_⟩
      have hne : w ≠ u := by
        intro h
        subst h
        obtain ⟨c', hc'R, _, hc'j⟩ := mem_covSet.mp hw
        exact hc ⟨c', hc'R, hc'j⟩
      rwa [Function.update_of_ne hne]
    rw [hempty]
    simp

/-- A covered vertex loses coverage for at most one switched-off coordinate:
the lose-sets are pairwise disjoint and contained in the covered set. -/
theorem sum_card_loseSet_le (R : Finset (Configuration V)) (σ ω : V → Bool) :
    ∑ u : V, (loseSet R σ ω u).card ≤ (coveredSet R σ ω).card := by
  have hdisj : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint (loseSet R σ ω) := by
    intro u _ u' _ hne
    refine Finset.disjoint_left.mpr fun v hv hv' => hne ?_
    obtain ⟨hoff, w, hw, hww⟩ := mem_coveredSet.mp (Finset.mem_sdiff.mp hv).1
    exact (eq_of_mem_loseSet hv hw hww).symm.trans (eq_of_mem_loseSet hv' hw hww)
  calc ∑ u : V, (loseSet R σ ω u).card
      = (Finset.univ.biUnion (loseSet R σ ω)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (coveredSet R σ ω).card := Finset.card_le_card (by
        intro v hv
        obtain ⟨u, _, hvu⟩ := Finset.mem_biUnion.mp hv
        exact (Finset.mem_sdiff.mp hvu).1)

end Coverage

section MissBound

open Bernoulli

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The single-family miss bound.**  Let `R` be a family of configurations retained for
the partition `σ` (distinguished elements on the `true` side, multisets on the `false`
side), with pairwise distinct distinguished elements and multisets and `|R| ≥ ρ > 0`.
Under the Bernoulli(θ) random set `T = {v | ω v = true}` the probability that no
configuration of `R` is hit is at most `8/μ₀ + exp (-θ μ₀/2)`, where
`μ₀ = min (√(ρ/2)/2) (θρ/4)` is a lower bound on the expected number of covered
off-side vertices. -/
theorem miss_bound (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (R : Finset (Configuration V)) (σ : V → Bool)
    (hret : ∀ c ∈ R, σ c.j = true ∧ ∀ v ∈ c.τ, σ v = false)
    (hj : Set.InjOn Configuration.j (R : Set (Configuration V)))
    (hτ : Set.InjOn Configuration.τ (R : Set (Configuration V)))
    {ρ : ℝ} (hρ : 0 < ρ) (hRcard : ρ ≤ (R.card : ℝ)) :
    expect θ (fun ω : V → Bool =>
        if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ 8 / min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4)
        + Real.exp (-(θ * min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4) / 2)) := by
  classical
  set μ₀ := min (Real.sqrt (ρ / 2) / 2) (θ * ρ / 4) with hμ₀def
  have hμ₀pos : 0 < μ₀ := by
    apply lt_min
    · exact div_pos (Real.sqrt_pos.mpr (by linarith)) two_pos
    · exact div_pos (mul_pos hθ0 hρ) (by norm_num)
  set Z : (V → Bool) → ℝ := fun ω => ((coveredSet R σ ω).card : ℝ) with hZdef
  set μ := expect θ Z with hμdef
  -- Step I: the exact formula for μ.
  have hZsum : ∀ ω : V → Bool, Z ω = ∑ v ∈ offSide σ,
      (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0) := by
    intro ω
    simp only [hZdef]
    unfold coveredSet
    rw [Finset.card_filter]
    push_cast
    rfl
  have hμeq : μ = ∑ v ∈ offSide σ, (1 - (1 - θ) ^ (covSet R v).card) := by
    rw [hμdef]
    rw [show Z = (fun ω : V → Bool => ∑ v ∈ offSide σ,
      (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)) from funext hZsum]
    rw [expect_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hpt : ∀ ω : V → Bool, (if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)
        = 1 - (if (∀ i ∈ (∅ : Finset V), ω i = true) ∧ (∀ i ∈ covSet R v, ω i = false)
            then (1 : ℝ) else 0) := by
      intro ω
      by_cases h : ∃ u ∈ covSet R v, ω u = true
      · have hncyl : ¬ ((∀ i ∈ (∅ : Finset V), ω i = true)
            ∧ (∀ i ∈ covSet R v, ω i = false)) := by
          rintro ⟨-, hall⟩
          obtain ⟨u, hu, huu⟩ := h
          rw [hall u hu] at huu
          exact Bool.noConfusion huu
        rw [if_pos h, if_neg hncyl]
        norm_num
      · rw [if_neg h]
        push Not at h
        have hcyl : (∀ i ∈ (∅ : Finset V), ω i = true)
            ∧ (∀ i ∈ covSet R v, ω i = false) := by
          refine ⟨by simp, fun i hi => ?_⟩
          simpa using h i hi
        rw [if_pos hcyl]
        norm_num
    rw [show (fun ω : V → Bool => if ∃ u ∈ covSet R v, ω u = true then (1 : ℝ) else 0)
      = (fun ω : V → Bool => 1 - (if (∀ i ∈ (∅ : Finset V), ω i = true)
          ∧ (∀ i ∈ covSet R v, ω i = false) then (1 : ℝ) else 0)) from funext hpt]
    rw [expect_sub, expect_const,
      expect_cylinder θ ∅ (covSet R v) (Finset.disjoint_empty_left _)]
    simp
  -- Step II: μ ≥ μ₀.
  have hterm_nonneg : ∀ d : ℕ, (0 : ℝ) ≤ 1 - (1 - θ) ^ d := by
    intro d
    have h1 : (1 - θ) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  set H := (offSide σ).filter (fun v => 1 ≤ θ * ((covSet R v).card : ℝ)) with hHdef
  set Hc := (offSide σ).filter (fun v => ¬ 1 ≤ θ * ((covSet R v).card : ℝ)) with hHcdef
  have hμsplit : μ = (∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card))
      + ∑ v ∈ Hc, (1 - (1 - θ) ^ (covSet R v).card) := by
    rw [hμeq, hHdef, hHcdef]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hμ0 : μ₀ ≤ μ := by
    by_cases hcase : ρ / 2 ≤ ((H.card : ℝ)) ^ 2
    · -- many high-degree vertices
      have h1 : (H.card : ℝ) / 2 ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) := by
        have h2 : ∀ v ∈ H, (1 / 2 : ℝ) ≤ 1 - (1 - θ) ^ (covSet R v).card := by
          intro v hv
          rw [hHdef] at hv
          exact half_le_one_sub_pow hθ0.le hθ1 (Finset.mem_filter.mp hv).2
        have h3 := Finset.sum_le_sum h2
        rw [Finset.sum_const, nsmul_eq_mul] at h3
        linarith
      have hsqrt : Real.sqrt (ρ / 2) ≤ (H.card : ℝ) := by
        have h2 : Real.sqrt (ρ / 2) ≤ Real.sqrt (((H.card : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hcase
        rwa [Real.sqrt_sq (by positivity)] at h2
      have hrest : 0 ≤ ∑ v ∈ Hc, (1 - (1 - θ) ^ (covSet R v).card) :=
        Finset.sum_nonneg fun v _ => hterm_nonneg _
      calc μ₀ ≤ Real.sqrt (ρ / 2) / 2 := min_le_left _ _
        _ ≤ (H.card : ℝ) / 2 := by linarith
        _ ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) := h1
        _ ≤ μ := by rw [hμsplit]; linarith
    · -- few high-degree vertices: double counting
      push Not at hcase
      have hcapped : ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
          ≤ ((H.card : ℝ)) ^ 2 := by
        have h1 : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card
            ≤ ((H ×ˢ H).image (fun p : V × V => s(p.1, p.2))).card := by
          apply Finset.card_le_card_of_injOn Configuration.τ
          · intro c hc
            exact sym2_mem_image_product H c.τ (Finset.mem_filter.mp hc).2
          · exact hτ.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
        have h2 : ((H ×ˢ H).image (fun p : V × V => s(p.1, p.2))).card ≤ (H ×ˢ H).card :=
          Finset.card_image_le
        have h3 : (H ×ˢ H).card = H.card * H.card := Finset.card_product _ _
        have h4 : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card ≤ H.card * H.card := by
          omega
        calc ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            ≤ (H.card : ℝ) * H.card := by exact_mod_cast h4
          _ = ((H.card : ℝ)) ^ 2 := by ring
      have hcard_cov : ∀ v : V, (covSet R v).card = (R.filter (fun c => v ∈ c.τ)).card :=
        fun v => Finset.card_image_of_injOn
          (hj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
      have hdouble : ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℕ)
          ≤ ∑ v ∈ Hc, (covSet R v).card := by
        calc (R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card
            = ∑ c ∈ R, if ¬ ∀ v ∈ c.τ, v ∈ H then 1 else 0 := Finset.card_filter _ _
          _ ≤ ∑ c ∈ R, (Hc.filter (fun v => v ∈ c.τ)).card := by
              apply Finset.sum_le_sum
              intro c hcR
              by_cases hcap : ∀ v ∈ c.τ, v ∈ H
              · have hnone : ¬ ∃ v ∈ c.τ, v ∉ H := by
                  rintro ⟨v, hvτ, hvH⟩
                  exact hvH (hcap v hvτ)
                simp [hnone]
              · have hncap : ¬ ∀ v ∈ c.τ, v ∈ H := hcap
                push Not at hcap
                obtain ⟨v, hvτ, hvH⟩ := hcap
                rw [if_pos hncap]
                refine Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨?_, hvτ⟩⟩
                have hoff : σ v = false := (hret c hcR).2 v hvτ
                rw [hHcdef, Finset.mem_filter, mem_offSide]
                refine ⟨hoff, fun hpred => hvH ?_⟩
                rw [hHdef, Finset.mem_filter, mem_offSide]
                exact ⟨hoff, hpred⟩
          _ = ∑ v ∈ Hc, (R.filter (fun c => v ∈ c.τ)).card := by
              simp only [Finset.card_filter]
              exact Finset.sum_comm
          _ = ∑ v ∈ Hc, (covSet R v).card := by
              exact Finset.sum_congr rfl fun v _ => (hcard_cov v).symm
      have hfil : (R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card
          + (R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card = R.card :=
        Finset.card_filter_add_card_filter_not _
      have hsum_ge : ρ / 2 ≤ ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
        have h2 : ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            ≤ ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
          have := hdouble
          push_cast
          exact_mod_cast this
        have h3 : ((R.filter (fun c => ∀ v ∈ c.τ, v ∈ H)).card : ℝ)
            + ((R.filter (fun c => ¬ ∀ v ∈ c.τ, v ∈ H)).card : ℝ) = (R.card : ℝ) := by
          exact_mod_cast hfil
        linarith
      have hHc_term : ∀ v ∈ Hc, θ * ((covSet R v).card : ℝ) / 2
          ≤ 1 - (1 - θ) ^ (covSet R v).card := by
        intro v hv
        have hnp := (Finset.mem_filter.mp (hHcdef ▸ hv)).2
        push Not at hnp
        exact lin_le_one_sub_pow hθ0.le hθ1 hnp.le
      have hB : θ * ρ / 4 ≤ μ := by
        have h1 := Finset.sum_le_sum hHc_term
        have h2 : ∑ v ∈ Hc, θ * ((covSet R v).card : ℝ) / 2
            = θ / 2 * ∑ v ∈ Hc, ((covSet R v).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
        have h3 : θ / 2 * (ρ / 2) ≤ θ / 2 * ∑ v ∈ Hc, ((covSet R v).card : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_ge (by positivity)
        have h4 : 0 ≤ ∑ v ∈ H, (1 - (1 - θ) ^ (covSet R v).card) :=
          Finset.sum_nonneg fun v _ => hterm_nonneg _
        rw [hμsplit]
        nlinarith
      exact le_trans (min_le_right _ _) hB
  have hμpos : 0 < μ := lt_of_lt_of_le hμ₀pos hμ0
  -- Step III: Var(Z) ≤ 2μ via Efron–Stein.
  have hvar : var θ Z ≤ 2 * μ := by
    refine le_trans (efron_stein θ hθ0.le hθ1 Z) ?_
    have hpt : ∀ ω : V → Bool,
        (∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2) ≤ 2 * Z ω := by
      intro ω
      have hcast : ∀ u : V, Z ω - Z (Function.update ω u false)
          = ((loseSet R σ ω u).card : ℝ) := by
        intro u
        simp only [hZdef]
        rw [card_loseSet R σ ω u,
          Nat.cast_sub (Finset.card_le_card (coveredSet_update_subset R σ ω u))]
      calc ∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2
          = ∑ u : V, ((loseSet R σ ω u).card : ℝ) ^ 2 :=
            Finset.sum_congr rfl fun u _ => by rw [hcast u]
        _ ≤ ∑ u : V, 2 * ((loseSet R σ ω u).card : ℝ) := by
            apply Finset.sum_le_sum
            intro u _
            have h2 : ((loseSet R σ ω u).card : ℝ) ≤ 2 := by
              exact_mod_cast card_loseSet_le_two hj σ ω u
            have h0 : (0 : ℝ) ≤ ((loseSet R σ ω u).card : ℝ) := by positivity
            nlinarith
        _ = 2 * ∑ u : V, ((loseSet R σ ω u).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ 2 * Z ω := by
            have hc : (∑ u : V, ((loseSet R σ ω u).card : ℝ))
                ≤ ((coveredSet R σ ω).card : ℝ) := by
              exact_mod_cast sum_card_loseSet_le R σ ω
            simp only [hZdef]
            linarith
    calc expect θ (fun ω => ∑ u : V, (Z ω - Z (Function.update ω u false)) ^ 2)
        ≤ expect θ (fun ω => 2 * Z ω) := expect_mono hθ0.le hθ1 hpt
      _ = 2 * μ := by rw [expect_const_mul, ← hμdef]
  -- Step IV: Chebyshev.
  have hcheb : expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0) ≤ 8 / μ₀ := by
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have hpt : ∀ ω : V → Bool, (if Z ω < μ / 2 then (1 : ℝ) else 0)
        ≤ 4 / μ ^ 2 * (Z ω - μ) ^ 2 := by
      intro ω
      by_cases h : Z ω < μ / 2
      · rw [if_pos h]
        have h1 : μ / 2 ≤ μ - Z ω := by
          have h0 : (0 : ℝ) ≤ Z ω := by simp only [hZdef]; positivity
          linarith
        have h2 : (μ / 2) ^ 2 ≤ (Z ω - μ) ^ 2 := by
          rw [show (Z ω - μ) ^ 2 = (μ - Z ω) ^ 2 by ring]
          exact pow_le_pow_left₀ (by positivity) h1 2
        have h3 : 4 / μ ^ 2 * (μ / 2) ^ 2 = 1 := by
          field_simp
          ring
        calc (1 : ℝ) = 4 / μ ^ 2 * (μ / 2) ^ 2 := h3.symm
          _ ≤ 4 / μ ^ 2 * (Z ω - μ) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      · rw [if_neg h]
        positivity
    calc expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0)
        ≤ expect θ (fun ω => 4 / μ ^ 2 * (Z ω - μ) ^ 2) := expect_mono hθ0.le hθ1 hpt
      _ = 4 / μ ^ 2 * var θ Z := by
          rw [expect_const_mul, hμdef]
          rfl
      _ ≤ 4 / μ ^ 2 * (2 * μ) := mul_le_mul_of_nonneg_left hvar (by positivity)
      _ = 8 / μ := by
          field_simp
          ring
      _ ≤ 8 / μ₀ := div_le_div_of_nonneg_left (by norm_num) hμ₀pos hμ0
  -- Step V: conditional bound on {all covered vertices off} ∩ {Z ≥ μ/2}.
  have hσall : ∀ {v u : V}, u ∈ covSet R v → σ u = true := by
    intro v u hu
    obtain ⟨c, hcR, _, hcj⟩ := mem_covSet.mp hu
    rw [← hcj]
    exact (hret c hcR).1
  have hcond : expect θ (fun ω : V → Bool =>
      if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω then (1 : ℝ) else 0)
      ≤ Real.exp (-(θ * μ₀ / 2)) := by
    rw [expect_split θ (fun v => σ v = true)]
    have houter : ∀ a : {i : V // σ i = true} → Bool,
        expect θ (fun b : {i : V // ¬ σ i = true} → Bool =>
          if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
              (merge (fun v => σ v = true) a b) v = false)
            ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
        ≤ Real.exp (-(θ * μ / 2)) := by
      intro a
      set ω₀ : V → Bool := merge (fun v => σ v = true) a (fun _ => false) with hω₀
      set Wa := coveredSet R σ ω₀ with hWa
      have hkey : ∀ (b : {i : V // ¬ σ i = true} → Bool) (u : V) (hu : σ u = true),
          merge (fun v => σ v = true) a b u = ω₀ u := by
        intro b u hu
        rw [hω₀]
        unfold merge
        rw [dif_pos hu, dif_pos hu]
      have hkey2 : ∀ (b : {i : V // ¬ σ i = true} → Bool) (i : {i : V // ¬ σ i = true}),
          merge (fun v => σ v = true) a b ↑i = b i := by
        intro b i
        unfold merge
        rw [dif_neg i.2]
      have hWeq : ∀ b : {i : V // ¬ σ i = true} → Bool,
          coveredSet R σ (merge (fun v => σ v = true) a b) = Wa := by
        intro b
        rw [hWa]
        unfold coveredSet
        apply Finset.filter_congr
        intro v _
        constructor
        · rintro ⟨u, hu, huu⟩
          refine ⟨u, hu, ?_⟩
          rw [← hkey b u (hσall hu)]
          exact huu
        · rintro ⟨u, hu, huu⟩
          refine ⟨u, hu, ?_⟩
          rw [hkey b u (hσall hu)]
          exact huu
      have hZeq : ∀ b : {i : V // ¬ σ i = true} → Bool,
          Z (merge (fun v => σ v = true) a b) = (Wa.card : ℝ) := by
        intro b
        simp only [hZdef]
        rw [hWeq b]
      have hWnp : ∀ v ∈ Wa, ¬ σ v = true := by
        intro v hv
        have h1 := (mem_coveredSet.mp (hWa ▸ hv)).1
        simp [h1]
      by_cases hbig : μ / 2 ≤ (Wa.card : ℝ)
      · have hfun : (fun b : {i : V // ¬ σ i = true} → Bool =>
            if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
                (merge (fun v => σ v = true) a b) v = false)
              ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
            = fun b => if (∀ i ∈ (∅ : Finset {i : V // ¬ σ i = true}), b i = true)
              ∧ (∀ i ∈ Wa.subtype (fun v => ¬ σ v = true), b i = false)
              then (1 : ℝ) else 0 := by
          funext b
          apply if_congr _ rfl rfl
          rw [hWeq b, hZeq b]
          constructor
          · rintro ⟨hall, -⟩
            refine ⟨by simp, fun i hi => ?_⟩
            rw [← hkey2 b i]
            exact hall _ (Finset.mem_subtype.mp hi)
          · rintro ⟨-, hall⟩
            refine ⟨fun v hv => ?_, hbig⟩
            exact (hkey2 b ⟨v, hWnp v hv⟩).trans
              (hall ⟨v, hWnp v hv⟩ (Finset.mem_subtype.mpr hv))
        rw [hfun, expect_cylinder θ ∅ (Wa.subtype (fun v => ¬ σ v = true))
          (Finset.disjoint_empty_left _)]
        have hcards : (Wa.subtype (fun v => ¬ σ v = true)).card = Wa.card := by
          rw [Finset.card_subtype, Finset.filter_true_of_mem hWnp]
        rw [hcards]
        simp only [Finset.card_empty, pow_zero, one_mul]
        calc (1 - θ) ^ Wa.card ≤ Real.exp (-(θ * Wa.card)) :=
            one_sub_pow_le_exp hθ0.le hθ1 _
          _ ≤ Real.exp (-(θ * μ / 2)) := by
              rw [Real.exp_le_exp]
              have h5 : θ * (μ / 2) ≤ θ * (Wa.card : ℝ) :=
                mul_le_mul_of_nonneg_left hbig hθ0.le
              linarith
      · have hfun : (fun b : {i : V // ¬ σ i = true} → Bool =>
            if (∀ v ∈ coveredSet R σ (merge (fun v => σ v = true) a b),
                (merge (fun v => σ v = true) a b) v = false)
              ∧ μ / 2 ≤ Z (merge (fun v => σ v = true) a b) then (1 : ℝ) else 0)
            = fun _ => (0 : ℝ) := by
          funext b
          rw [if_neg]
          rintro ⟨-, hZb⟩
          rw [hZeq b] at hZb
          exact hbig hZb
        rw [hfun, expect_const]
        positivity
    calc expect θ (fun a : {i : V // σ i = true} → Bool =>
          expect θ (fun b : {i : V // ¬ σ i = true} → Bool =>
            (fun ω : V → Bool => if (∀ v ∈ coveredSet R σ ω, ω v = false)
              ∧ μ / 2 ≤ Z ω then (1 : ℝ) else 0) (merge (fun v => σ v = true) a b)))
        ≤ expect θ (fun _ : {i : V // σ i = true} → Bool => Real.exp (-(θ * μ / 2))) :=
          expect_mono hθ0.le hθ1 houter
      _ = Real.exp (-(θ * μ / 2)) := expect_const _ _
      _ ≤ Real.exp (-(θ * μ₀ / 2)) := by
          rw [Real.exp_le_exp]
          have h5 := mul_le_mul_of_nonneg_left hμ0 hθ0.le
          linarith
  -- Step VI: combine.
  have hsplit : ∀ ω : V → Bool,
      (if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ (if Z ω < μ / 2 then (1 : ℝ) else 0)
        + (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
            then (1 : ℝ) else 0) := by
    intro ω
    by_cases hmiss : ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true
    · rw [if_pos hmiss]
      have h1 : (0 : ℝ) ≤ (if Z ω < μ / 2 then (1 : ℝ) else 0) := by positivity
      have h2 : (0 : ℝ) ≤ (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
          then (1 : ℝ) else 0) := by positivity
      linarith
    · rw [if_neg hmiss]
      have hallOff : ∀ v ∈ coveredSet R σ ω, ω v = false := by
        intro v hv
        obtain ⟨hoff, u, hu, huu⟩ := mem_coveredSet.mp hv
        obtain ⟨c, hcR, hvτ, hcj⟩ := mem_covSet.mp hu
        by_contra hvt
        simp only [Bool.not_eq_false] at hvt
        exact hmiss ⟨c, hcR, by rw [hcj]; exact huu, v, hvτ, hvt⟩
      by_cases hZb : Z ω < μ / 2
      · rw [if_pos hZb, if_neg (fun hcontra => (not_le.mpr hZb) hcontra.2)]
        norm_num
      · rw [if_neg hZb, if_pos ⟨hallOff, not_lt.mp hZb⟩]
        norm_num
  calc expect θ (fun ω : V → Bool =>
        if ∃ c ∈ R, ω c.j = true ∧ ∃ v ∈ c.τ, ω v = true then (0 : ℝ) else 1)
      ≤ expect θ (fun ω : V → Bool => (if Z ω < μ / 2 then (1 : ℝ) else 0)
          + (if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
              then (1 : ℝ) else 0)) := expect_mono hθ0.le hθ1 hsplit
    _ = expect θ (fun ω => if Z ω < μ / 2 then (1 : ℝ) else 0)
        + expect θ (fun ω : V → Bool =>
            if (∀ v ∈ coveredSet R σ ω, ω v = false) ∧ μ / 2 ≤ Z ω
              then (1 : ℝ) else 0) := expect_add _ _ _
    _ ≤ 8 / μ₀ + Real.exp (-(θ * μ₀ / 2)) := add_le_add hcheb hcond

end MissBound

/-- **Lemma 3.1 (Common-cut lemma), single family.**  A family of `≥ α·m`
configurations with pairwise distinct distinguished elements and pairwise distinct
multisets can be hit by a set of size `O_α(√m)`. -/
theorem common_cut_single (α : ℝ) (hα : 0 < α) :
    ∃ (D : ℝ) (m₀ : ℕ), 0 < D ∧
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (F : Finset (Configuration V)),
        m₀ ≤ Fintype.card V →
        α * Fintype.card V ≤ F.card →
        Set.InjOn Configuration.j (F : Set (Configuration V)) →
        Set.InjOn Configuration.τ (F : Set (Configuration V)) →
        ∃ T : Finset V, (T.card : ℝ) ≤ D * Real.sqrt (Fintype.card V) ∧
          ∃ c ∈ F, Hits T c := by
  -- The conclusion only asks for a set hitting a *single* configuration of the family,
  -- so a three-element witness `{c.j, a, b}` (where `c.τ = s(a, b)`) suffices.
  refine ⟨3, 1, by norm_num, ?_⟩
  intro V _ _ F hm hcard _ _
  have hm1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hm
  have h0 : (0 : ℝ) < (F.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hα (by linarith)) hcard
  obtain ⟨c, hc⟩ : F.Nonempty := Finset.card_pos.mp (by exact_mod_cast h0)
  set a := c.τ.out.1 with ha
  set b := c.τ.out.2 with hb
  refine ⟨{c.j, a, b}, ?_, c, hc, Finset.mem_insert_self _ _, a, by simp, Sym2.out_fst_mem c.τ⟩
  have hT3 : ({c.j, a, b} : Finset V).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({a, b} : Finset V).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  have hsq : (1 : ℝ) ≤ Real.sqrt (Fintype.card V) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hm1
  calc (({c.j, a, b} : Finset V).card : ℝ) ≤ 3 := by exact_mod_cast hT3
    _ ≤ 3 * Real.sqrt (Fintype.card V) := by linarith

/-- **Lemma 3.1, "moreover" part.**  Given at most `m` such families on the same
ground set, a single set of size `O_α(√m)` hits all but at most `m/8` of them. -/
theorem common_cut (α : ℝ) (hα : 0 < α) :
    ∃ (D : ℝ) (m₀ : ℕ), 0 < D ∧
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (q : ℕ)
        (𝓕 : Fin q → Finset (Configuration V)),
        m₀ ≤ Fintype.card V →
        q ≤ Fintype.card V →
        (∀ k, α * Fintype.card V ≤ ((𝓕 k).card : ℝ)) →
        (∀ k, Set.InjOn Configuration.j (𝓕 k : Set (Configuration V))) →
        (∀ k, Set.InjOn Configuration.τ (𝓕 k : Set (Configuration V))) →
        ∃ T : Finset V, (T.card : ℝ) ≤ D * Real.sqrt (Fintype.card V) ∧
          ∃ Bad : Finset (Fin q), 8 * Bad.card ≤ Fintype.card V ∧
            ∀ k, k ∉ Bad → ∃ c ∈ 𝓕 k, Hits T c := by
  classical
  let C : ℝ := 256 * (1 / α + 1 / Real.sqrt α)
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let c₀ : ℝ := min (Real.sqrt α / 8) (C * α / 32)
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact lt_min (by positivity) (by positivity)
  let R₀ : ℝ := max (C + 1) (1024 / c₀)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by positivity : 0 < C + 1) (le_max_left _ _)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, R₀ ^ 2 ≤ m₀ := exists_nat_ge (R₀ ^ 2)
  refine ⟨4 * C, m₀, by positivity, ?_⟩
  intro V _ _ q families hm hq hcard hj hτ
  let m : ℕ := Fintype.card V
  have hmR : R₀ ^ 2 ≤ (m : ℝ) := by
    exact le_trans hm₀ (by exact_mod_cast hm)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hRroot : R₀ ≤ Real.sqrt m := by
    have h := Real.sqrt_le_sqrt hmR
    rwa [Real.sqrt_sq hR₀.le] at h
  have hsqrtm : 0 < Real.sqrt m := lt_of_lt_of_le hR₀ hRroot
  have hmpos : 0 < m := by
    by_contra hz
    have : m = 0 := Nat.eq_zero_of_not_pos hz
    rw [this] at hsqrtm
    norm_num at hsqrtm
  let θ : ℝ := C / Real.sqrt m
  have hθ0 : 0 < θ := div_pos hC hsqrtm
  have hθ1 : θ < 1 := by
    have hCR : C + 1 ≤ R₀ := le_max_left _ _
    have hCsqrt : C < Real.sqrt m := lt_of_lt_of_le (by linarith) hRroot
    exact (div_lt_one hsqrtm).2 hCsqrt
  have hm_sqrt : (m : ℝ) / Real.sqrt m = Real.sqrt m := by
    apply (div_eq_iff (ne_of_gt hsqrtm)).2
    rw [Real.mul_self_sqrt hm0]
  have hCsa : (256 : ℝ) ≤ C * Real.sqrt α := by
    have hpart : 256 * (1 / Real.sqrt α) ≤ C := by
      dsimp only [C]
      have ha0 : 0 ≤ 1 / α := by positivity
      nlinarith
    have h := mul_le_mul_of_nonneg_right hpart hsα.le
    calc (256 : ℝ) = 256 * ((1 / Real.sqrt α) * Real.sqrt α) := by
          rw [one_div_mul_cancel (ne_of_gt hsα), mul_one]
      _ = (256 * (1 / Real.sqrt α)) * Real.sqrt α := by ring
      _ ≤ C * Real.sqrt α := h
  choose σ hσ using fun k => exists_large_retained (families k)
  let R : Fin q → Finset (Configuration V) := fun k => retained (families k) (σ k)
  have hRcard : ∀ k, α * m / 8 ≤ ((R k).card : ℝ) := by
    intro k
    have hk := hσ k
    have hk' : ((families k).card : ℝ) ≤ 8 * ((R k).card : ℝ) := by
      dsimp only [R]
      exact_mod_cast hk
    have hc := hcard k
    dsimp only [m]
    linarith
  have hRret : ∀ k, ∀ c ∈ R k,
      σ k c.j = true ∧ ∀ v ∈ c.τ, σ k v = false := by
    intro k c hc
    exact (mem_retained.mp hc).2
  have hRj : ∀ k, Set.InjOn Configuration.j (R k : Set (Configuration V)) := by
    intro k
    exact (hj k).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hRτ : ∀ k, Set.InjOn Configuration.τ (R k : Set (Configuration V)) := by
    intro k
    exact (hτ k).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hmu : (1024 : ℝ) ≤
      min (Real.sqrt ((α * m / 8) / 2) / 2) (θ * (α * m / 8) / 4) := by
    have hA : c₀ * Real.sqrt m ≤ Real.sqrt ((α * m / 8) / 2) / 2 := by
      have hcA : c₀ ≤ Real.sqrt α / 8 := min_le_left _ _
      have hsqrtprod : Real.sqrt ((α * (m : ℝ) / 8) / 2) / 2 =
          (Real.sqrt α / 8) * Real.sqrt m := by
        rw [show (α * (m : ℝ) / 8) / 2 = α * ((m : ℝ) / 16) by ring,
          Real.sqrt_mul hα.le, Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
        norm_num
        ring
      rw [hsqrtprod]
      exact mul_le_mul_of_nonneg_right hcA (Real.sqrt_nonneg _)
    have hB : c₀ * Real.sqrt m ≤ θ * (α * m / 8) / 4 := by
      have hcB : c₀ ≤ C * α / 32 := min_le_right _ _
      have hform : θ * (α * (m : ℝ) / 8) / 4 =
          (C * α / 32) * Real.sqrt m := by
        dsimp only [θ]
        field_simp
        nlinarith [Real.sq_sqrt hm0]
      rw [hform]
      exact mul_le_mul_of_nonneg_right hcB (Real.sqrt_nonneg _)
    have hbase : (1024 : ℝ) ≤ c₀ * Real.sqrt m := by
      have hquot : 1024 / c₀ ≤ R₀ := le_max_right _ _
      have h := le_trans hquot hRroot
      simpa [mul_comm] using (div_le_iff₀ hc₀).mp h
    exact le_min (le_trans hbase hA) (le_trans hbase hB)
  let μ₀ : ℝ := min (Real.sqrt ((α * m / 8) / 2) / 2) (θ * (α * m / 8) / 4)
  have hμ₀ : (1024 : ℝ) ≤ μ₀ := hmu
  have hμ₀pos : 0 < μ₀ := lt_of_lt_of_le (by norm_num) hμ₀
  have hAform : θ * (Real.sqrt ((α * m / 8) / 2) / 2) / 2 =
      C * Real.sqrt α / 16 := by
    have hsqrtprod : Real.sqrt ((α * (m : ℝ) / 8) / 2) / 2 =
        (Real.sqrt α / 8) * Real.sqrt m := by
      rw [show (α * (m : ℝ) / 8) / 2 = α * ((m : ℝ) / 16) by ring,
        Real.sqrt_mul hα.le, Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
      norm_num
      ring
    rw [hsqrtprod]
    dsimp only [θ]
    field_simp
    ring
  have hBform : θ * (θ * (α * m / 8) / 4) / 2 = C ^ 2 * α / 64 := by
    dsimp only [θ]
    field_simp
    nlinarith [Real.sq_sqrt hm0]
  have hAe : (8 : ℝ) ≤ θ * (Real.sqrt ((α * m / 8) / 2) / 2) / 2 := by
    rw [hAform]
    linarith
  have hBe : (8 : ℝ) ≤ θ * (θ * (α * m / 8) / 4) / 2 := by
    rw [hBform]
    have hsquare : (256 : ℝ) ^ 2 ≤ (C * Real.sqrt α) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hCsa 2
    rw [mul_pow, Real.sq_sqrt hα.le] at hsquare
    nlinarith
  have harg : (8 : ℝ) ≤ θ * μ₀ / 2 := by
    dsimp only [μ₀]
    by_cases hab : Real.sqrt ((α * m / 8) / 2) / 2 ≤ θ * (α * m / 8) / 4
    · rw [min_eq_left hab]
      exact hAe
    · rw [min_eq_right (le_of_not_ge hab)]
      exact hBe
  have hsmall : 8 / μ₀ + Real.exp (- (θ * μ₀ / 2)) ≤ (1 / 64 : ℝ) := by
    have hfirst : 8 / μ₀ ≤ (1 / 128 : ℝ) := by
      rw [div_le_iff₀ hμ₀pos]
      nlinarith
    have hsecond : Real.exp (- (θ * μ₀ / 2)) ≤ (1 / 256 : ℝ) := by
      calc Real.exp (- (θ * μ₀ / 2)) ≤ Real.exp (-8) := by
              rw [Real.exp_le_exp]
              linarith
        _ ≤ (1 / 256 : ℝ) := exp_neg_eight_le
    linarith
  let Tset : (V → Bool) → Finset V := fun w => Finset.univ.filter (fun v => w v = true)
  have hHits : ∀ (w : V → Bool) (c : Configuration V),
      Hits (Tset w) c ↔ w c.j = true ∧ ∃ v ∈ c.τ, w v = true := by
    intro w c
    simp only [Hits, Tset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hjw, v, hvw, hvτ⟩
      exact ⟨hjw, v, hvτ, hvw⟩
    · rintro ⟨hjw, v, hvτ, hvw⟩
      exact ⟨hjw, v, hvw, hvτ⟩
  have hmissR : ∀ k, Bernoulli.expect θ (fun w : V → Bool =>
      if ∃ c ∈ R k, Hits (Tset w) c then (0 : ℝ) else 1) ≤ 1 / 64 := by
    intro k
    have hraw := miss_bound θ hθ0 hθ1.le (R k) (σ k) (hRret k) (hRj k) (hRτ k)
      (show 0 < α * m / 8 by positivity) (hRcard k)
    rw [show (fun w : V → Bool =>
        if ∃ c ∈ R k, Hits (Tset w) c then (0 : ℝ) else 1) =
      (fun w => if ∃ c ∈ R k, w c.j = true ∧ ∃ v ∈ c.τ, w v = true
        then (0 : ℝ) else 1) by
          funext w
          apply if_congr
          · simp only [hHits]
          · rfl
          · rfl]
    exact hraw.trans hsmall
  have hmissF : ∀ k, Bernoulli.expect θ (fun w : V → Bool =>
      if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) ≤ 1 / 64 := by
    intro k
    refine le_trans (Bernoulli.expect_mono hθ0.le hθ1.le ?_) (hmissR k)
    intro w
    by_cases hf : ∃ c ∈ families k, Hits (Tset w) c
    · rw [if_pos hf]
      positivity
    · have hr : ¬ ∃ c ∈ R k, Hits (Tset w) c := by
        rintro ⟨c, hcR, hhit⟩
        exact hf ⟨c, (mem_retained.mp hcR).1, hhit⟩
      simp [hf, hr]
  let Bad : (V → Bool) → Finset (Fin q) := fun w =>
    Finset.univ.filter (fun k => ¬ ∃ c ∈ families k, Hits (Tset w) c)
  have hBadcard : ∀ w : V → Bool, ((Bad w).card : ℝ) = ∑ k : Fin q,
      if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1 := by
    intro w
    dsimp only [Bad]
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hhit : ∃ c ∈ families k, Hits (Tset w) c <;> simp [hhit]
  have hEBad : Bernoulli.expect θ (fun w : V → Bool => ((Bad w).card : ℝ)) ≤ m / 64 := by
    rw [show (fun w : V → Bool => ((Bad w).card : ℝ)) =
      (fun w => ∑ k : Fin q, if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) from
        funext hBadcard]
    rw [show (fun w : V → Bool => ∑ k : Fin q,
        if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) =
      (fun w => ∑ k ∈ (Finset.univ : Finset (Fin q)),
        (fun k w => if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1) k w) by
          funext w; simp]
    rw [Bernoulli.expect_sum]
    calc ∑ k ∈ (Finset.univ : Finset (Fin q)), Bernoulli.expect θ
          (fun w : V → Bool => if ∃ c ∈ families k, Hits (Tset w) c then (0 : ℝ) else 1)
        ≤ ∑ k ∈ (Finset.univ : Finset (Fin q)), (1 / 64 : ℝ) :=
          Finset.sum_le_sum fun k _ => hmissF k
      _ = q / 64 := by simp [div_eq_mul_inv]
      _ ≤ m / 64 := by
        have hqm : (q : ℝ) ≤ m := by exact_mod_cast hq
        exact div_le_div_of_nonneg_right hqm (by norm_num)
  have hTcard : ∀ w : V → Bool, ((Tset w).card : ℝ) = ∑ v : V,
      if w v = true then (1 : ℝ) else 0 := by
    intro w
    dsimp only [Tset]
    rw [Finset.card_filter]
    push_cast
    rfl
  have hsingle : ∀ v : V, Bernoulli.expect θ (fun w : V → Bool =>
      if w v = true then (1 : ℝ) else 0) = θ := by
    intro v
    rw [show (fun w : V → Bool => if w v = true then (1 : ℝ) else 0) =
      (fun w => if (∀ i ∈ ({v} : Finset V), w i = true) ∧
        (∀ i ∈ (∅ : Finset V), w i = false) then (1 : ℝ) else 0) by
          funext w; simp]
    rw [Bernoulli.expect_cylinder θ {v} ∅ (Finset.disjoint_empty_right _)]
    simp
  have hET : Bernoulli.expect θ (fun w : V → Bool => ((Tset w).card : ℝ)) =
      θ * m := by
    rw [show (fun w : V → Bool => ((Tset w).card : ℝ)) =
      (fun w => ∑ v : V, if w v = true then (1 : ℝ) else 0) from funext hTcard]
    rw [show (fun w : V → Bool => ∑ v : V, if w v = true then (1 : ℝ) else 0) =
      (fun w => ∑ v ∈ (Finset.univ : Finset V),
        (fun v w => if w v = true then (1 : ℝ) else 0) v w) by funext w; simp]
    rw [Bernoulli.expect_sum]
    simp only [hsingle, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
  let Obj : (V → Bool) → ℝ := fun w =>
    (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ)
      + (8 / m) * ((Bad w).card : ℝ)
  have hEObj : Bernoulli.expect θ Obj ≤ 3 / 8 := by
    have hdenT : 0 < 4 * C * Real.sqrt m := by positivity
    have hdenm : (0 : ℝ) < m := by exact_mod_cast hmpos
    rw [show Obj = (fun w => (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ)
      + (8 / m) * ((Bad w).card : ℝ)) from rfl]
    rw [Bernoulli.expect_add, Bernoulli.expect_const_mul, Bernoulli.expect_const_mul, hET]
    have hfirst : (1 / (4 * C * Real.sqrt m)) * (θ * m) = (1 / 4 : ℝ) := by
      have ht : θ * (m : ℝ) = C * Real.sqrt m := by
        dsimp only [θ]
        calc C / Real.sqrt m * (m : ℝ) = C * ((m : ℝ) / Real.sqrt m) := by ring
          _ = C * Real.sqrt m := by rw [hm_sqrt]
      rw [ht]
      field_simp
    rw [hfirst]
    have hsecond : (8 / (m : ℝ)) * Bernoulli.expect θ
        (fun w : V → Bool => ((Bad w).card : ℝ)) ≤ 1 / 8 := by
      calc (8 / (m : ℝ)) * Bernoulli.expect θ
            (fun w : V → Bool => ((Bad w).card : ℝ))
          ≤ (8 / (m : ℝ)) * ((m : ℝ) / 64) :=
            mul_le_mul_of_nonneg_left hEBad (by positivity)
        _ = (1 / 8 : ℝ) := by
          field_simp [ne_of_gt hdenm]
          norm_num
    linarith
  obtain ⟨w, hw⟩ := Bernoulli.exists_le_expect hθ0 hθ1 Obj
  have hw' : Obj w ≤ 3 / 8 := le_trans hw hEObj
  refine ⟨Tset w, ?_, Bad w, ?_, ?_⟩
  · have hbadnonneg : 0 ≤ (8 / (m : ℝ)) * ((Bad w).card : ℝ) := by positivity
    have hpart : (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ) ≤ 3 / 8 := by
      dsimp only [Obj] at hw'
      linarith
    have hden : 0 < 4 * C * Real.sqrt m := by positivity
    rw [one_div_mul_eq_div, div_le_iff₀ hden] at hpart
    change ((Tset w).card : ℝ) ≤ 4 * C * Real.sqrt m
    linarith
  · have hTnonneg : 0 ≤ (1 / (4 * C * Real.sqrt m)) * ((Tset w).card : ℝ) := by
      positivity
    have hpart : (8 / (m : ℝ)) * ((Bad w).card : ℝ) ≤ 3 / 8 := by
      dsimp only [Obj] at hw'
      linarith
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hreal : (8 * (Bad w).card : ℕ) < m := by
      have : (8 * ((Bad w).card : ℝ)) < m := by
        rw [div_mul_eq_mul_div] at hpart
        have hle := (div_le_iff₀ hmreal).mp hpart
        have hlt : (3 / 8 : ℝ) * m < m := by
          exact mul_lt_of_lt_one_left hmreal (by norm_num)
        exact lt_of_le_of_lt hle hlt
      have hcast : (((8 * (Bad w).card : ℕ) : ℝ)) < (m : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact this
      exact Nat.cast_lt.mp hcast
    exact Nat.le_of_lt hreal
  · intro k hk
    by_contra hno
    apply hk
    dsimp only [Bad]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hno⟩

end NUS
