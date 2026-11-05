module

public import Workspace.Impl.TermHyp

@[expose] public section

/-!
# Right coset representatives by closure (T3, the mathematics)

Corollary A.22 enumerates the right cosets `R r` of the radical preimage `R` in `H`. We find one
representative per coset by the usual closure: start with the list `[1]`; for each listed
representative `r` in turn and each generator `g` of `H`, add `r g` unless it lies in the coset
of a listed representative. Two elements `y, r'` lie in the same right coset exactly when
`y r'⁻¹ ∈ R`, and this is one membership test.

The invariant `TmRpInv` holds along the run. When every listed representative has been
processed, the listed cosets are closed under right multiplication by the generators. In a
finite group this closure is the whole of `H`, so the list has one representative per coset
(`tmRp_final`): this is what `Iface.TermRepsSpec` asks. The list has at most `[H : R]` entries at
every time (`TmRpInv.length_le`); this bounds the number of rounds of the program.
-/

namespace GI.Impl

variable {G : Type*} [Group G]

/-- `y` lies in the right coset `R r'` of some `r'` of the list. -/
def TmRpCov (R : Subgroup G) (reps : List G) (y : G) : Prop := ∃ r' ∈ reps, y * r'⁻¹ ∈ R

theorem TmRpCov.mono {R : Subgroup G} {reps reps' : List G} {y : G} (h : TmRpCov R reps y)
    (hp : reps <+: reps') : TmRpCov R reps' y := by
  obtain ⟨r', hr', hy⟩ := h
  exact ⟨r', hp.subset hr', hy⟩

/-- **One test.** Add `y` to the list unless it lies in the coset of a listed element. -/
noncomputable def tmRpAdd (R : Subgroup G) (y : G) (reps : List G) : List G := by
  classical
  exact if reps.any (fun r' => decide (y * r'⁻¹ ∈ R)) then reps else reps ++ [y]

/-- **One round.** The tests of `r g` for the generators `g` in turn. -/
noncomputable def tmRpProc (R : Subgroup G) (r : G) (gs : List G) (reps : List G) : List G :=
  gs.foldl (fun acc g => tmRpAdd R (r * g) acc) reps

/-- The invariant after `i` rounds: the list starts with `1`, lies in `H`, has pairwise distinct
cosets, at least `i` entries, and the first `i` entries are processed (each `reps[j] g` lies in a
listed coset). -/
structure TmRpInv (H R : Subgroup G) (gs : List G) (i : ℕ) (reps : List G) : Prop where
  head : reps.head? = some 1
  sub : ∀ r ∈ reps, r ∈ H
  distinct : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)
  le : i ≤ reps.length
  closed : ∀ j (hj : j < reps.length), j < i → ∀ g ∈ gs, TmRpCov R reps (reps[j] * g)

theorem tmRpInv_start (H R : Subgroup G) (gs : List G) : TmRpInv H R gs 0 [1] where
  head := rfl
  sub := fun r hr => by rw [List.mem_singleton.1 hr]; exact H.one_mem
  distinct := List.pairwise_singleton _ _
  le := Nat.zero_le _
  closed := fun j _ hj => absurd hj (Nat.not_lt_zero _)

section add

variable {H R : Subgroup G}

theorem tmRpAdd_prefix (y : G) (reps : List G) : reps <+: tmRpAdd R y reps := by
  unfold tmRpAdd
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem tmRpAdd_cov (y : G) (reps : List G) : TmRpCov R (tmRpAdd R y reps) y := by
  classical
  unfold tmRpAdd
  split
  · rename_i h
    obtain ⟨r', hr', hy⟩ := List.any_eq_true.1 h
    exact ⟨r', hr', of_decide_eq_true hy⟩
  · exact ⟨y, List.mem_append_right _ (List.mem_singleton_self _), by
      rw [mul_inv_cancel]; exact R.one_mem⟩

theorem tmRpAdd_of_cov {y : G} {reps : List G} (h : TmRpCov R reps y) :
    tmRpAdd R y reps = reps := by
  classical
  obtain ⟨r', hr', hy⟩ := h
  unfold tmRpAdd
  rw [if_pos (List.any_eq_true.2 ⟨r', hr', decide_eq_true hy⟩)]

theorem tmRpAdd_of_not_cov {y : G} {reps : List G} (h : ¬ TmRpCov R reps y) :
    tmRpAdd R y reps = reps ++ [y] := by
  classical
  unfold tmRpAdd
  rw [if_neg]
  intro ha
  obtain ⟨r', hr', hy⟩ := List.any_eq_true.1 ha
  exact h ⟨r', hr', of_decide_eq_true hy⟩

theorem tmRpAdd_sub {y : G} (hy : y ∈ H) {reps : List G} (h : ∀ r ∈ reps, r ∈ H) :
    ∀ r ∈ tmRpAdd R y reps, r ∈ H := by
  unfold tmRpAdd
  split
  · exact h
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h r hr
    · rw [List.mem_singleton.1 hr]; exact hy

theorem tmRpAdd_distinct (y : G) {reps : List G} (h : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)) :
    (tmRpAdd R y reps).Pairwise (fun a b => a * b⁻¹ ∉ R) := by
  classical
  unfold tmRpAdd
  split
  · exact h
  · rename_i hn
    refine List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.1 hb]
    intro hay
    apply hn
    refine List.any_eq_true.2 ⟨a, ha, decide_eq_true ?_⟩
    have := R.inv_mem hay
    rwa [mul_inv_rev, inv_inv] at this

theorem tmRpAdd_head {y : G} {reps : List G} (h : reps.head? = some 1) :
    (tmRpAdd R y reps).head? = some 1 := by
  unfold tmRpAdd
  split
  · exact h
  · cases reps with
    | nil => simp at h
    | cons a l => simpa using h

end add

section proc

variable {H R : Subgroup G}

theorem tmRpProc_prefix (r : G) (gs : List G) (reps : List G) : reps <+: tmRpProc R r gs reps := by
  induction gs generalizing reps with
  | nil => exact List.prefix_refl _
  | cons g gs ih =>
    exact (tmRpAdd_prefix (r * g) reps).trans (ih _)

theorem tmRpProc_cov (r : G) (gs : List G) (reps : List G) :
    ∀ g ∈ gs, TmRpCov R (tmRpProc R r gs reps) (r * g) := by
  induction gs generalizing reps with
  | nil => intro g hg; simp at hg
  | cons g gs ih =>
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact (tmRpAdd_cov (r * g') reps).mono (tmRpProc_prefix r gs _)
    · exact ih _ g' hg'

theorem tmRpProc_sub {r : G} (hr : r ∈ H) {gs : List G} (hgs : ∀ g ∈ gs, g ∈ H) {reps : List G}
    (h : ∀ x ∈ reps, x ∈ H) : ∀ x ∈ tmRpProc R r gs reps, x ∈ H := by
  induction gs generalizing reps with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      (tmRpAdd_sub (H.mul_mem hr (hgs g (List.mem_cons_self))) h)

theorem tmRpProc_distinct (r : G) (gs : List G) {reps : List G}
    (h : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)) :
    (tmRpProc R r gs reps).Pairwise (fun a b => a * b⁻¹ ∉ R) := by
  induction gs generalizing reps with
  | nil => exact h
  | cons g gs ih => exact ih (tmRpAdd_distinct _ h)

theorem tmRpProc_head (r : G) (gs : List G) {reps : List G} (h : reps.head? = some 1) :
    (tmRpProc R r gs reps).head? = some 1 := by
  induction gs generalizing reps with
  | nil => exact h
  | cons g gs ih => exact ih (tmRpAdd_head h)

theorem tmRpProc_take_succ (r : G) (gs reps : List G) {i : ℕ} (hi : i < gs.length) :
    tmRpProc R r (gs.take (i + 1)) reps = tmRpAdd R (r * gs[i]) (tmRpProc R r (gs.take i) reps) := by
  unfold tmRpProc
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- **One round keeps the invariant.** -/
theorem tmRpInv_step {gs : List G} (hgs : ∀ g ∈ gs, g ∈ H) {i : ℕ} {reps : List G}
    (h : TmRpInv H R gs i reps) (hi : i < reps.length) :
    TmRpInv H R gs (i + 1) (tmRpProc R reps[i] gs reps) := by
  have hp := tmRpProc_prefix (R := R) reps[i] gs reps
  have hlen := hp.length_le
  have hget : ∀ j (hj : j < reps.length), (tmRpProc R reps[i] gs reps)[j]'(by omega) = reps[j] :=
    fun j hj => (List.IsPrefix.getElem hp hj).symm
  refine ⟨tmRpProc_head _ _ h.head, tmRpProc_sub (h.sub _ (List.getElem_mem hi)) hgs h.sub,
    tmRpProc_distinct _ _ h.distinct, by omega, fun j hj hji g hg => ?_⟩
  have hjr : j < reps.length := by omega
  rw [hget j hjr]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
  · exact (h.closed j hjr hji g hg).mono hp
  · exact tmRpProc_cov _ gs reps g hg

end proc

section final

variable {H R : Subgroup G}

/-- The coset of a listed element, as an element of the quotient `H / R` (the left coset of
its inverse); elements outside `H` go to `1`. -/
noncomputable def tmRpQ (H R : Subgroup G) (r : G) : H ⧸ R.subgroupOf H := by
  classical
  exact if h : r ∈ H then QuotientGroup.mk (⟨r⁻¹, H.inv_mem h⟩ : H) else QuotientGroup.mk 1

theorem tmRp_mk_eq_iff (a b : H) :
    (QuotientGroup.mk (a⁻¹) : H ⧸ R.subgroupOf H) = QuotientGroup.mk (b⁻¹) ↔
      (a : G) * (b : G)⁻¹ ∈ R := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem tmRpQ_eq_iff {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    tmRpQ H R a = tmRpQ H R b ↔ a * b⁻¹ ∈ R := by
  unfold tmRpQ
  rw [dif_pos ha, dif_pos hb]
  exact tmRp_mk_eq_iff ⟨a, ha⟩ ⟨b, hb⟩

theorem tmRpQuot_nodup {reps : List G} (hsub : ∀ r ∈ reps, r ∈ H)
    (hd : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)) : (reps.map (tmRpQ H R)).Nodup := by
  refine List.pairwise_map.2 ?_
  have hd' : reps.Pairwise (fun a b => (a ∈ H ∧ b ∈ H) ∧ a * b⁻¹ ∉ R) := by
    have h2 : reps.Pairwise (fun a b => a ∈ H ∧ b ∈ H) :=
      List.pairwise_of_forall_mem_list fun a ha b hb => ⟨hsub a ha, hsub b hb⟩
    exact List.Pairwise.and h2 hd
  exact hd'.imp fun ⟨⟨ha, hb⟩, hab⟩ heq => hab ((tmRpQ_eq_iff ha hb).1 heq)

/-- **A list of elements of `H` with distinct cosets has at most `[H : R]` entries.** -/
theorem tmRp_len_le [Finite G] {reps : List G} (hsub : ∀ r ∈ reps, r ∈ H)
    (hd : reps.Pairwise (fun a b => a * b⁻¹ ∉ R)) : reps.length ≤ (R.subgroupOf H).index := by
  classical
  haveI : Fintype (H ⧸ R.subgroupOf H) := Fintype.ofFinite _
  have hn := tmRpQuot_nodup hsub hd
  have hl : (reps.map (tmRpQ H R)).length = reps.length := List.length_map _
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← hl]
  exact hn.length_le_card

theorem TmRpInv.length_le [Finite G] {gs : List G} {i : ℕ} {reps : List G}
    (h : TmRpInv H R gs i reps) : reps.length ≤ (R.subgroupOf H).index :=
  tmRp_len_le h.sub h.distinct

/-- `x g⁻¹ = x g^(o - 1)` for the order `o` of `g`, in a finite group. -/
theorem tmRp_mul_inv_eq_pow [Finite G] (x g : G) :
    x * g⁻¹ = x * g ^ (orderOf g - 1) := by
  congr 1
  have ho := orderOf_pos g
  rw [eq_comm, ← mul_left_cancel_iff (a := g), mul_inv_cancel, ← pow_succ',
    Nat.sub_add_cancel ho, pow_orderOf_eq_one]

/-- **When every listed coset is processed, the list meets every coset of `⟨gs⟩`.** -/
theorem tmRp_cover [Finite G] {gs : List G} {i : ℕ} {reps : List G}
    (h : TmRpInv H R gs i reps) (hi : reps.length ≤ i) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gs}, TmRpCov R reps x := by
  -- the set of covered elements is closed under right multiplication by the generators
  have hstep : ∀ x, TmRpCov R reps x → ∀ g ∈ gs, TmRpCov R reps (x * g) := by
    rintro x ⟨r, hr, hx⟩ g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨r', hr', hy⟩ := h.closed j hj (by omega) g hg
    refine ⟨r', hr', ?_⟩
    have := R.mul_mem hx hy
    simpa [mul_assoc] using this
  have hpow : ∀ x, TmRpCov R reps x → ∀ g ∈ gs, ∀ k : ℕ, TmRpCov R reps (x * g ^ k) := by
    intro x hx g hg k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, ← mul_assoc]; exact hstep _ ih g hg
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one =>
    refine ⟨1, ?_, by simp [R.one_mem]⟩
    cases reps with
    | nil => simp at hi; have := h.head; simp at this
    | cons a l =>
      have := h.head
      simp only [List.head?_cons, Option.some.injEq] at this
      exact this ▸ List.mem_cons_self
  | mul_right y _ g hg ih => exact hstep y ih g hg
  | mul_inv_cancel y _ g hg ih =>
    rw [tmRp_mul_inv_eq_pow]
    exact hpow y ih g hg _

/-- **The final list.** When `H = ⟨gs⟩`, every element of `H` is `x r` with `x ∈ R` and `r`
listed, and the list has exactly `[H : R]` entries. -/
theorem tmRp_final [Finite G] {gs : List G}
    (hH : Subgroup.closure {g | g ∈ gs} = H) {i : ℕ} {reps : List G}
    (h : TmRpInv H R gs i reps) (hi : reps.length ≤ i) :
    (∀ x ∈ H, ∃ r ∈ reps, ∃ y ∈ R, x = y * r) ∧ reps.length = (R.subgroupOf H).index := by
  classical
  have hcov := tmRp_cover h hi
  rw [hH] at hcov
  refine ⟨fun x hx => ?_, le_antisymm h.length_le ?_⟩
  · obtain ⟨r, hr, hxr⟩ := hcov x hx
    exact ⟨r, hr, x * r⁻¹, hxr, by group⟩
  · haveI : Fintype (H ⧸ R.subgroupOf H) := Fintype.ofFinite _
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    have hl : (reps.map (tmRpQ H R)).length = reps.length := List.length_map _
    rw [← hl, ← List.toFinset_card_of_nodup (tmRpQuot_nodup h.sub h.distinct)]
    refine Finset.card_le_card fun q _ => ?_
    rw [List.mem_toFinset]
    induction q using QuotientGroup.induction_on with
    | H z =>
      obtain ⟨r, hr, hzr⟩ := hcov ((z⁻¹ : H) : G) (z⁻¹).2
      refine List.mem_map.2 ⟨r, hr, ?_⟩
      have key := (tmRp_mk_eq_iff (R := R) ⟨r, h.sub r hr⟩ (z⁻¹)).2
      simp only [inv_inv] at key
      unfold tmRpQ
      rw [dif_pos (h.sub r hr)]
      exact key (by simpa using R.inv_mem hzr)

end final

end GI.Impl
