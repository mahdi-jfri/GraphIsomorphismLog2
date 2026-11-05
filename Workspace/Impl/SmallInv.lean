module

public import Workspace.Assembly.Final
public import Workspace.Algorithm.Existence

@[expose] public section

/-!
# An invariant that keeps states `Small`

`Small` bounds the length of the hierarchy and the numbers stored
in a state by `N`. It is not closed under the steps of `Run`. The model lets a step store
intervals of ratio `1`: `TowerFrom` allows them in the initial tower, and an exposure
(`PrimitiveQuotient`) keeps those already stored (its new intervals have ratio at least `2`,
`from_old`). A ratio-`1` interval adds `0` to `ρ` and to `Q`, so the cost bounds allow it. So a
state of a run may have a hierarchy of any length. The paper never stores such intervals
(Section 7.1: "Only nontrivial interval ratios occur"; its hierarchy is a chain of block
systems).

This file gives the invariant that the implementation keeps instead (`SmallInv`):

* every stored ratio is at least `2` and at most `N`, and every bound and origin is at most `N`;
* `ρ ≤ N`, with `ρ` counted in natural numbers (`rhoNat`);
* the row degree is at most `N`.

Every interval of ratio at least `2` adds at least `1` to `ρ`, so the hierarchy has at most
`ρ ≤ N` intervals, and `SmallInv` implies `Small` (`SmallInv.small`). The invariant passes to
every child whose hierarchy has `ρ` at most the parent's and whose new intervals are
nontrivial with numbers at most `N` (`SmallInv.of_rho_le`). Every step of `Run` keeps `ρ` from
growing (the fields `rho_le`, `exp_rho` and the cap update `CapUpdate.rho_eq`), so the remaining
condition is on the new intervals: an implementation must not store a trivial interval. The
fresh hierarchy of one interval satisfies it (`smallInv_fresh`), and so does a cap update
(`SmallInv.capUpdate`).
-/

namespace GI.Impl

open GI.Algorithm

variable {Ω C : Type}

/-- **The numbers stored in a state are small**: the hierarchy has at most `N` intervals, every
ratio, cap and origin is at most `N`, and so is the degree of the row record. With `k ≤ N` this
bounds the weight of a canonical value by a polynomial in `N` (`stateW_le_of_small`,
`Workspace/Impl/Weights.lean`). The stage 1 invariants do not bound these numbers, but the paper
keeps them small: a ratio counts classes, a cap is at most its ratio, an origin names an older
interval, and the row degree counts row classes of the domain. -/
def Small (S : State Ω C) : Prop :=
  S.hier.length ≤ S.N ∧ (∀ I ∈ S.hier, I.ratio ≤ S.N ∧ I.cap ≤ S.N ∧ I.origin ≤ S.N) ∧
    ∀ R ∈ S.rows, R.m ≤ S.N

/-- A state with the same hierarchy and phase size and no row record keeps the bound. -/
theorem Small.reset {S T : State Ω C} (h : Small S) (hh : T.hier = S.hier) (hN : T.N = S.N)
    (hr : T.rows = none) : Small T :=
  ⟨hh ▸ hN ▸ h.1, hh ▸ hN ▸ h.2.1, fun R hR => by rw [hr] at hR; cases hR⟩

/-- Every interval of the list is nontrivial and its numbers are at most `N`. -/
def IntervalsOK (N : ℕ) (l : List (Interval Ω)) : Prop :=
  ∀ I ∈ l, 2 ≤ I.ratio ∧ I.ratio ≤ N ∧ I.cap ≤ N ∧ I.origin ≤ N

/-- **The invariant that keeps a state `Small`**: nontrivial intervals with numbers at most `N`,
`ρ ≤ N`, and a row degree at most `N`. -/
def SmallInv (S : State Ω C) : Prop :=
  IntervalsOK S.N S.hier ∧ rhoNat S.hier ≤ S.N ∧ ∀ R ∈ S.rows, R.m ≤ S.N

/-- A nontrivial ratio adds at least `1` to `ρ`. -/
theorem one_le_towerRank {d : ℕ} (hd : 2 ≤ d) : 1 ≤ (GI.towerRank d).toNat := by
  have h1 : 1 ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by norm_num) (by simpa using hd)
  unfold GI.towerRank
  rw [if_neg (by omega)]
  omega

/-- **A hierarchy of nontrivial intervals has at most `ρ` intervals.** -/
theorem length_le_rhoNat : ∀ {l : List (Interval Ω)}, (∀ I ∈ l, 2 ≤ I.ratio) →
    l.length ≤ rhoNat l
  | [], _ => by simp [rhoNat]
  | I :: l, h => by
    have hI := one_le_towerRank (h I List.mem_cons_self)
    have hl := length_le_rhoNat fun J hJ => h J (List.mem_cons_of_mem _ hJ)
    simp only [rhoNat, List.map_cons, List.sum_cons, List.length_cons] at hl ⊢
    omega

/-- **The invariant implies `Small`**: the length bound comes from `length_le_rhoNat`. -/
theorem SmallInv.small {S : State Ω C} (h : SmallInv S) : Small S :=
  ⟨(length_le_rhoNat fun I hI => (h.1 I hI).1).trans h.2.1,
    fun I hI => ⟨(h.1 I hI).2.1, (h.1 I hI).2.2.1, (h.1 I hI).2.2.2⟩, h.2.2⟩

/-- **The invariant passes to a child** with the same `N`, a hierarchy of nontrivial intervals
with numbers at most `N` and with `ρ` at most the parent's, and a row degree at most `N`. -/
theorem SmallInv.of_rho_le {S T : State Ω C} (h : SmallInv S) (hN : T.N = S.N)
    (hI : IntervalsOK T.N T.hier) (hρ : rhoNat T.hier ≤ rhoNat S.hier)
    (hr : ∀ R ∈ T.rows, R.m ≤ T.N) : SmallInv T :=
  ⟨hI, hρ.trans (h.2.1.trans hN.ge), hr⟩

/-- A child with the same hierarchy and `N` keeps the invariant if its row degree is at most
`N` (orbit-chain children, restrictions). -/
theorem SmallInv.of_hier_eq {S T : State Ω C} (h : SmallInv S) (hh : T.hier = S.hier)
    (hN : T.N = S.N) (hr : ∀ R ∈ T.rows, R.m ≤ T.N) : SmallInv T :=
  h.of_rho_le hN (by rw [hh, hN]; exact h.1) (by rw [hh]) hr

/-- A state with the same hierarchy and phase size and no row record keeps the invariant. -/
theorem SmallInv.reset {S T : State Ω C} (h : SmallInv S) (hh : T.hier = S.hier) (hN : T.N = S.N)
    (hr : T.rows = none) : SmallInv T :=
  h.of_hier_eq hh hN fun R hR => by rw [hr] at hR; cases hR

/-- **A cap update keeps the invariant**: it lowers one bound and keeps every ratio and origin
(the hierarchy of an aggregation child, `Aggregation.newHier`). -/
theorem SmallInv.capUpdate {S T : State Ω C} (h : SmallInv S) (hN : T.N = S.N) (i : ℕ)
    (c : ℕ) (hc : c ≤ S.hier[i]?.elim 0 Interval.cap)
    (hh : T.hier = S.hier.modify i fun I => { I with cap := c })
    (hr : ∀ R ∈ T.rows, R.m ≤ T.N) : SmallInv T := by
  have hlen : T.hier.length = S.hier.length := by rw [hh, List.length_modify]
  have hget : ∀ j (hj : j < T.hier.length), T.hier[j] =
      if i = j then { S.hier[j]'(hlen ▸ hj) with cap := c } else S.hier[j]'(hlen ▸ hj) := by
    intro j hj
    simp only [hh, List.getElem_modify]
  refine h.of_rho_le hN (fun I hI => ?_) (le_of_eq ?_) hr
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hI
    have hS := h.1 _ (List.getElem_mem (hlen ▸ hj))
    rw [hget j hj, hN]
    split_ifs with hij
    · subst hij
      have hc' : c ≤ (S.hier[i]'(hlen ▸ hj)).cap := by
        rw [List.getElem?_eq_getElem (hlen ▸ hj)] at hc; exact hc
      exact ⟨hS.1, hS.2.1, hc'.trans hS.2.2.1, hS.2.2.2⟩
    · exact hS
  · have hm : T.hier.map Interval.ratio = S.hier.map Interval.ratio := by
      refine List.ext_getElem (by simp [hlen]) fun j h1 h2 => ?_
      simp only [List.getElem_map]
      rw [hget j (by simpa using h1)]
      split_ifs <;> rfl
    have e : ∀ l : List (Interval Ω), rhoNat l =
        ((l.map Interval.ratio).map fun d => (GI.towerRank d).toNat).sum := fun l => by
      simp [rhoNat, List.map_map, Function.comp_def]
    rw [e, e, hm]

/-- `2k ≤ 2^k + 1`. -/
theorem two_mul_le_two_pow_add_one : ∀ k : ℕ, 2 * k ≤ 2 ^ k + 1
  | 0 => by norm_num
  | 0 + 1 => by norm_num
  | k + 1 + 1 => by
    have := two_mul_le_two_pow_add_one (k + 1)
    have h1 : 2 ≤ 2 ^ (k + 1) := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
    rw [pow_succ 2 (k + 1)]
    omega

/-- The tower rank of `s` is at most `s`. -/
theorem towerRank_toNat_le (s : ℕ) : (GI.towerRank s).toNat ≤ s := by
  unfold GI.towerRank
  split_ifs with hs
  · simp
  · have hk := two_mul_le_two_pow_add_one (Nat.log 2 s)
    have hp : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 (by omega)
    omega

/-- **The fresh hierarchy keeps the invariant**: one interval of ratio, bound and origin at most
`N`, with ratio at least `2` (a fresh state whose largest orbit is a point stores no interval). -/
theorem smallInv_fresh {S : State Ω C} {I : Interval Ω} (hh : S.hier = [I]) (h2 : 2 ≤ I.ratio)
    (hd : I.ratio ≤ S.N) (hc : I.cap ≤ S.N) (ho : I.origin ≤ S.N)
    (hr : ∀ R ∈ S.rows, R.m ≤ S.N) : SmallInv S := by
  refine ⟨fun J hJ => ?_, ?_, hr⟩
  · rw [hh, List.mem_singleton] at hJ
    subst hJ
    exact ⟨h2, hd, hc, ho⟩
  · rw [hh]
    simp only [rhoNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact (towerRank_toNat_le _).trans hd

/-- A state with no interval and a row degree at most `N` keeps the invariant. -/
theorem smallInv_nil {S : State Ω C} (hh : S.hier = []) (hr : ∀ R ∈ S.rows, R.m ≤ S.N) :
    SmallInv S :=
  ⟨fun I hI => (by rw [hh] at hI; cases hI), (by rw [hh]; simp [rhoNat]), hr⟩

end GI.Impl

/-! ### The model alone does not give `Small` -/

namespace GI.Impl

open GI.Algorithm Equiv

/-- **Trivial intervals can be added to an initial tower**: `n` intervals of ratio `1` from the
points to the points, with any origin `k`, in front of an initial tower, give an initial tower.
So the model allows a fresh state with a hierarchy of any length and any origin labels; `Small`
is not a consequence of the model, and the implementation must keep `SmallInv` by its own
choices. -/
theorem initialTower_pad {Ω : Type} {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)}
    (h : InitialTower G D l) (n k : ℕ) :
    InitialTower G D (List.replicate n ⟨⊥, 1, 1, k⟩ ++ l) := by
  obtain ⟨⟨a, haD, hmax, ht⟩, hcap⟩ := h
  refine ⟨⟨a, haD, hmax, ?_⟩, fun I hI => ?_⟩
  · clear hcap hmax
    induction n with
    | zero => simpa using ht
    | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      refine ⟨fun g _ v w => ?_, le_rfl, one_mul _, ih⟩
      show g v = g w ↔ v = w
      exact g.injective.eq_iff
  · rcases List.mem_append.1 hI with hI | hI
    · rw [(List.eq_of_mem_replicate hI)]
    · exact hcap I hI

end GI.Impl
