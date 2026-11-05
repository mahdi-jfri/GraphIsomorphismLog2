module

public import Workspace.Lang.Prims.Reduce
public import Workspace.Lang.Lib.Fold
public import Workspace.Lang.Lib.Perm

@[expose] public section

/-!
# Combining the answers of the cosets

Algorithm 5: "apply that reduction and solve its children with `Continue`; return their exact
combined answer", and for the normalization "Return the exact combination of these answers".
A reduction splits the group `G` into cosets `τ_j K`; the child on `τ_j K` returns its answer
`A_j`, and the answer of the parent is the union `U = ⋃_j τ_j A_j`. Each `A_j` is empty or a
left coset `x_j L_j` of a group given by generators, and the union `U` is the set of
isomorphisms of the parent, which is empty or a left coset of a group (`answer_eq_smul_aut`).

**Why generators suffice.** Let `U = c H` be a left coset, `c₀ ∈ U`, and `X` a set with
`c₀ X ⊆ U` and `U ⊆ c₀ ⟨X⟩`. Then `U = c₀ ⟨X⟩` (`coset_eq_of_gens`): `c₀ H = U`, so `X ⊆ H` and
`⟨X⟩ ≤ H`. The program takes for `c₀` the first `c_j = τ_j x_j` of a nonempty piece, and for `X`
the generators of all the `L_j` together with the elements `c₀⁻¹ c_j`. Every element `u` of `U`
lies in some piece, `u = c_j l = c₀ (c₀⁻¹ c_j) l` with `l ∈ L_j`.

**The program.** `combStep` is the step of a fold over the list of pairs `[encPerm τ_j, u_j]`. The
accumulator is `[]` while all pieces seen so far are empty, and `[encPerm c₀, encGroup gs]`
afterwards. A nonempty piece `u_j = [encPerm x_j, encGroup hs]` adds `c₀⁻¹ τ_j x_j`, `1` and `hs`
to `gs` (`combStep_spec`). The fold computes `combine` (`comb_spec`), and `combine` gives a
coset-or-empty value of `U` (`combine_cosetOrEmpty`). The coset normal form (`cosetNF_spec`) then
cuts the generators to at most `n²`. The cost is polynomial in the input weight and `n`
(`combCost`).
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms encGroup gens)
open Equiv Equiv.Perm
open scoped Pointwise

variable {n : ℕ}

/-! ### The mathematics -/

section Math

variable {G : Type*} [Group G]

/-- In a left coset `c H`, an element `c₀` of the coset gives the same coset. -/
theorem coset_eq_of_mem {U : Set G} {c : G} {H : Subgroup G} (hU : U = c • (H : Set G)) {c₀ : G}
    (h₀ : c₀ ∈ U) : U = c₀ • (H : Set G) := by
  rw [hU] at h₀ ⊢
  obtain ⟨h, hh, rfl⟩ := h₀
  ext g
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h⁻¹ * k, H.mul_mem (H.inv_mem hh) hk, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h * k, H.mul_mem hh hk, by group⟩

/-- **A coset from generators.** If `U` is a left coset of a subgroup, `c₀ ∈ U`, `c₀ X ⊆ U` and
`U ⊆ c₀ ⟨X⟩`, then `U = c₀ ⟨X⟩`. -/
theorem coset_eq_of_gens {U : Set G} {c : G} {H : Subgroup G} (hU : U = c • (H : Set G)) {c₀ : G}
    (h₀ : c₀ ∈ U) {X : Set G} (hX : ∀ x ∈ X, c₀ * x ∈ U) (hsub : U ⊆ c₀ • (Subgroup.closure X : Set G)) :
    U = c₀ • (Subgroup.closure X : Set G) := by
  have hU' := coset_eq_of_mem hU h₀
  refine le_antisymm hsub ?_
  have hXH : Subgroup.closure X ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    have := hX x hx
    rw [hU'] at this
    obtain ⟨k, hk, hk'⟩ := this
    have : x = k := mul_left_cancel hk'.symm
    rw [this]; exact hk
  rw [hU']
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hXH hg, rfl⟩

/-- In a left coset `U`, if `a, b, a g ∈ U` then `b g ∈ U`. -/
theorem mul_mem_coset {U : Set G} {c : G} {H : Subgroup G} (hU : U = c • (H : Set G)) {a b g : G}
    (ha : a ∈ U) (hb : b ∈ U) (hag : a * g ∈ U) : b * g ∈ U := by
  rw [coset_eq_of_mem hU ha] at hag
  rw [coset_eq_of_mem hU hb]
  obtain ⟨k, hk, hk'⟩ := hag
  have : g = k := mul_left_cancel hk'.symm
  exact ⟨g, this ▸ hk, rfl⟩

end Math

/-! ### The step of the combination -/

/-- The weight of a concatenation. -/
theorem wt_list_append_le (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ (Val.list xs).wt + (Val.list ys).wt := by
  rw [wt_list_eq, wt_list_eq, wt_list_eq]
  simp only [List.map_append, List.sum_append, List.length_append]
  have := GI.Machine.len_add_le_add xs.length ys.length
  have := GI.Machine.len_add_le_add (xs.map Val.size).sum (ys.map Val.size).sum
  omega

/-- The accumulator of the combination: nothing yet, or a representative and generators. -/
abbrev Acc (n : ℕ) := Option (Perm (Fin n) × List (Perm (Fin n)))

/-- The value of an accumulator, or of a piece: `[]`, or `[encPerm c, encGroup gs]`. -/
def encAcc : Acc n → Val
  | none => .list []
  | some (c, gs) => .list [encPerm c, encGroup gs]

/-- **One step of the combination**, on the accumulator `a`, the representative `t` of a coset
and the answer `p` on it. -/
def combAcc : Acc n → Perm (Fin n) → Acc n → Acc n
  | a, _, none => a
  | none, t, some (x, hs) => some (t * x, hs)
  | some (c, gs), t, some (x, hs) => some (c, gs ++ (c⁻¹ * (t * x)) :: 1 :: hs)

/-- Adding a nonempty piece to a nonempty accumulator, in the environment
`[[ctx, acc, [encPerm t, piece]], encPerm (t * x)]`. -/
def combMerge (comp inv app : ℕ) : Expr :=
  .letE (.call comp (mk2 (.call inv (.get (arg 1) (.nat 0))) (.var 1)))
    (mk2 (.get (arg 1) (.nat 0))
      (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call app (mk2 (.snoc (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.var 2))
          (.get (.get (.get (arg 2) (.nat 1)) (.nat 1)) (.nat 1))))))

/-- Adding a nonempty piece, in the environment `[[ctx, acc, [encPerm t, piece]], encPerm (t * x)]`. -/
def combAdd (comp inv app : ℕ) : Expr :=
  .ite (.length (arg 1)) (combMerge comp inv app)
    (mk2 (.var 1) (.get (.get (arg 2) (.nat 1)) (.nat 1)))

/-- The step of the combination on `[ctx, acc, [encPerm t, piece]]`. `comp`, `inv` and `app` are
the indices of composition, inverse and append. -/
def combStep (comp inv app : ℕ) : Expr :=
  .ite (.length (.get (arg 2) (.nat 1)))
    (.letE (.call comp (mk2 (.get (arg 2) (.nat 0)) (.get (.get (arg 2) (.nat 1)) (.nat 0))))
      (combAdd comp inv app))
    (arg 1)

/-- The cost constant of a step. -/
def combK : ℕ := 10 ^ 7

theorem encGroup_append (gs hs : List (Perm (Fin n))) (z : Perm (Fin n)) :
    encGroup (gs ++ z :: 1 :: hs) = .list [.nat n, .list (((1 :: gs).map encPerm ++
      [encPerm z]) ++ (1 :: hs).map encPerm)] := by
  simp [encGroup, encPerms]

/-- **The step of the combination.** -/
theorem combStep_spec {P : Program} {f comp inv app : ℕ}
    (hf : P.funs[f]? = some (combStep comp inv app)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv)) (happ : P.HasAt app (appendFuns app))
    (c : Val) (a : Acc n) (t : Perm (Fin n)) (p : Acc n) :
    FunDet P f (.list [c, encAcc a, .list [encPerm t, encAcc p]]) (encAcc (combAcc a t p))
      (combK * ((Val.list [c, encAcc a, .list [encPerm t, encAcc p]]).wt + (n + 1) ^ 4) ^ 2) := by
  set A := Val.list [c, encAcc a, .list [encPerm t, encAcc p]] with hA
  have wc : c.wt < A.wt := wt_le_wt_list (by simp)
  have wa : (encAcc a).wt < A.wt := wt_le_wt_list (by simp)
  have wpp : (Val.list [encPerm t, encAcc p]).wt < A.wt := wt_le_wt_list (by simp)
  have wt' : (encPerm t).wt < (Val.list [encPerm t, encAcc p]).wt := wt_le_wt_list (by simp)
  have wp : (encAcc p).wt < (Val.list [encPerm t, encAcc p]).wt := wt_le_wt_list (by simp)
  have hX : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have p34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq : ∀ y : ℕ, y ≤ y ^ 2 := fun y => Nat.le_self_pow (by norm_num) y
  set X := A.wt + (n + 1) ^ 4 with hXdef
  have hXsq := hsq X
  have hK : 5000000 * X ^ 2 ≤ combK * X ^ 2 := Nat.mul_le_mul_right _ (by norm_num [combK])
  have g0 : Det P [A] (arg 0) c (2 * A.wt + 0 + 5) := Det.arg' rfl
  have g1 : ∀ rest, Det P (A :: rest) (arg 1) (encAcc a) (2 * A.wt + 1 + 5) := fun _ =>
    Det.arg' rfl
  have g2 : ∀ rest, Det P (A :: rest) (arg 2) (.list [encPerm t, encAcc p]) (2 * A.wt + 2 + 5) :=
    fun _ => Det.arg' rfl
  refine FunDet.intro hf ?_
  unfold combStep
  cases p with
  | none =>
    -- an empty piece: keep the accumulator
    have dl := Det.length (Det.get' (g2 []) (Det.nat 1)
      (show [encPerm t, encAcc (n := n) none][1]? = some (.list []) from rfl))
    have he : combAcc a t none = a := by cases a <;> rfl
    rw [he]
    refine (Det.ite_zero dl (g1 [])).mono ?_
    have : (encAcc a).wt ≤ X := by omega
    simp only [wt_list_nil, List.length_nil]
    omega
  | some q =>
    obtain ⟨x, hs⟩ := q
    have hpv : encAcc (some (x, hs)) = .list [encPerm x, encGroup hs] := rfl
    have wx : (encPerm x).wt < (encAcc (some (x, hs))).wt := wt_le_wt_list (by simp)
    have whs : (encGroup hs).wt < (encAcc (some (x, hs))).wt := wt_le_wt_list (by simp)
    have dpu := Det.get' (g2 []) (Det.nat 1)
      (show [encPerm t, encAcc (some (x, hs))][1]? = some (.list [encPerm x, encGroup hs]) from
        rfl)
    have dl := Det.length dpu
    have dy := Det.call (Det.mk2 (Det.get' (g2 []) (Det.nat 0)
        (show [encPerm t, encAcc (some (x, hs))][0]? = some (encPerm t) from rfl))
      (Det.get' dpu (Det.nat 0) (show [encPerm x, encGroup hs][0]? = some (encPerm x) from rfl)))
      (compose_spec hcomp t x)
    have wtx := wt_encPerm_le (t * x)
    have wt2 := wt_list2_le (encPerm t) (encPerm x)
    have hsv : encGroup hs = .list [.nat n, .list ((1 :: hs).map encPerm)] := rfl
    have whsl : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt := by
      rw [hsv]; exact wt_le_wt_list (by simp)
    have e1 : (Val.list [encPerm x, encGroup hs]).wt = (encAcc (some (x, hs))).wt := rfl
    have e2 : (Val.list [Val.nat n, .list ((1 :: hs).map encPerm)]).wt = (encGroup hs).wt := rfl
    have wz : ∀ z : Perm (Fin n), (encPerm z).wt ≤ 4 * X := fun z => by
      have := wt_encPerm_le z
      have : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have whsl' : (Val.list ((1 :: hs).map encPerm)).wt ≤ X := by omega
    have hnhs : ((1 :: hs).map encPerm).length ≤ X := by
      have := length_lt_wt_list ((1 :: hs).map encPerm); omega
    have dhs : ∀ y, Det P [A, y] (.get (.get (.get (arg 2) (.nat 1)) (.nat 1)) (.nat 1))
        (.list ((1 :: hs).map encPerm)) (8 * X + 30) := fun y => by
      refine (Det.get' (Det.get' (Det.get' (g2 [y]) (Det.nat 1)
        (show [encPerm t, encAcc (some (x, hs))][1]? = some (.list [encPerm x, encGroup hs])
          from rfl)) (Det.nat 1)
        (show [encPerm x, encGroup hs][1]? = some (encGroup hs) from rfl)) (Det.nat 1)
        (show [Val.nat n, .list ((1 :: hs).map encPerm)][1]? = some (.list ((1 :: hs).map encPerm))
          from rfl)).mono ?_
      have := wt_le_wt_list (show (Val.list ((1 :: hs).map encPerm)) ∈
        [Val.nat n, .list ((1 :: hs).map encPerm)] by simp)
      rw [← hsv] at this
      omega
    obtain ⟨cb, hcb, hle⟩ : ∃ cb, Det P [A, encPerm (t * x)] (combAdd comp inv app)
        (encAcc (combAcc a t (some (x, hs)))) cb ∧ cb ≤ 10 ^ 6 * X ^ 2 := by
      unfold combAdd
      cases a with
      | none =>
        have da := Det.length (g1 [encPerm (t * x)])
        have dh := dhs (encPerm (t * x))
        refine ⟨_, Det.ite_zero da (Det.mk2 (Det.var' (i := 1) rfl) (Det.get' (Det.get' (g2 _)
          (Det.nat 1) (show [encPerm t, encAcc (some (x, hs))][1]? =
            some (.list [encPerm x, encGroup hs]) from rfl)) (Det.nat 1)
            (show [encPerm x, encGroup hs][1]? = some (encGroup hs) from rfl))), ?_⟩
        have hr : encAcc (combAcc none t (some (x, hs))) = .list [encPerm (t * x), encGroup hs] :=
          rfl
        rw [hr]
        have := wt_list2_le (encPerm (t * x)) (encGroup hs)
        have := wz (t * x)
        have : (encAcc (n := n) none).wt = 4 := rfl
        simp only [List.length_nil]
        omega
      | some q =>
        obtain ⟨c0, gs⟩ := q
        have hav : encAcc (some (c0, gs)) = .list [encPerm c0, encGroup gs] := rfl
        have wc0 : (encPerm c0).wt < (encAcc (some (c0, gs))).wt := wt_le_wt_list (by simp)
        have wgs : (encGroup gs).wt < (encAcc (some (c0, gs))).wt := wt_le_wt_list (by simp)
        have hgv : encGroup gs = .list [.nat n, .list ((1 :: gs).map encPerm)] := rfl
        have wgsl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := by
          rw [hgv]; exact wt_le_wt_list (by simp)
        have da := Det.length (g1 [encPerm (t * x)])
        set z := c0⁻¹ * (t * x) with hz
        have g1' : ∀ rest, Det P (A :: rest) (arg 1) (.list [encPerm c0, encGroup gs])
            (2 * A.wt + 1 + 5) := fun rest => by have := g1 rest; rwa [hav] at this
        have dz := Det.call (Det.mk2 (Det.call (Det.get' (g1' [encPerm (t * x)]) (Det.nat 0)
            (show [encPerm c0, encGroup gs][0]? = some (encPerm c0) from rfl))
          (inv_spec hinv c0)) (Det.var' (P := P) (env := [A, encPerm (t * x)]) (i := 1) rfl))
          (compose_spec hcomp c0⁻¹ (t * x))
        have dsn := Det.snoc (Det.get' (Det.get' (g1' [encPerm (t * x), encPerm z]) (Det.nat 1)
            (show [encPerm c0, encGroup gs][1]? = some (encGroup gs) from rfl)) (Det.nat 1)
            (show [Val.nat n, .list ((1 :: gs).map encPerm)][1]? =
              some (.list ((1 :: gs).map encPerm)) from rfl))
          (Det.var' (P := P) (env := [A, encPerm (t * x), encPerm z]) (i := 2) rfl)
        have dys := dhs (encPerm z)
        -- the environment of the merge is longer; the same lookups work
        have dys' : Det P [A, encPerm (t * x), encPerm z]
            (.get (.get (.get (arg 2) (.nat 1)) (.nat 1)) (.nat 1))
            (.list ((1 :: hs).map encPerm)) (8 * X + 30) := by
          refine (Det.get' (Det.get' (Det.get' (g2 _) (Det.nat 1)
            (show [encPerm t, encAcc (some (x, hs))][1]? = some (.list [encPerm x, encGroup hs])
              from rfl)) (Det.nat 1)
            (show [encPerm x, encGroup hs][1]? = some (encGroup hs) from rfl)) (Det.nat 1)
            (show [Val.nat n, .list ((1 :: hs).map encPerm)][1]? =
              some (.list ((1 :: hs).map encPerm)) from rfl)).mono ?_
          omega
        set xs := (1 :: gs).map encPerm ++ [encPerm z] with hxs
        set ys := (1 :: hs).map encPerm with hys
        have hap := append_spec happ xs ys
        have dap := Det.call (Det.mk2 dsn dys') (w := .list (xs ++ ys))
          (cb := loopModK * (ys.length + 1) *
            ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1))
          (hap.mono fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩)
        have dc0 := Det.get' (g1' [encPerm (t * x), encPerm z]) (Det.nat 0)
          (show [encPerm c0, encGroup gs][0]? = some (encPerm c0) from rfl)
        have dn := Det.get' (Det.get' (g1' [encPerm (t * x), encPerm z]) (Det.nat 1)
            (show [encPerm c0, encGroup gs][1]? = some (encGroup gs) from rfl)) (Det.nat 0)
            (show [Val.nat n, .list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
        have dm := Det.letE dz (Det.mk2 dc0 (Det.mk2 dn dap))
        have hr : encAcc (combAcc (some (c0, gs)) t (some (x, hs))) =
            .list [encPerm c0, .list [.nat n, .list (xs ++ ys)]] := by
          show Val.list [encPerm c0, encGroup (gs ++ z :: 1 :: hs)] = _
          rw [encGroup_append]
        have dl0 : ¬ ([encPerm c0, encGroup gs].length = 0) := by simp
        refine ⟨_, Det.ite_pos da dl0 (hr ▸ dm), ?_⟩
        have hn4 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
        have w1 := wz c0
        have w2 := wz z
        have w3 := wz (t * x)
        have w4 := wz c0⁻¹
        have hxs1 : (Val.list xs).wt ≤ (Val.list ((1 :: gs).map encPerm)).wt + 2 * (encPerm z).wt + 2 :=
          wt_list_snoc_le _ _
        have hyl : ys.length ≤ X := hnhs
        have hxy := wt_list_append_le xs ys
        have hl2 := wt_list2_le (.list xs) (.list ys)
        have hl3 := wt_list2_le (encPerm c0⁻¹) (encPerm (t * x))
        have hl4 := wt_list2_le (.nat n) (.list (xs ++ ys))
        have hl5 := wt_list2_le (encPerm c0) (.list [.nat n, .list (xs ++ ys)])
        have hnn := wt_nat_le n
        have hB : (Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1 ≤
            100 * X := by omega
        have hprod : loopModK * (ys.length + 1) *
            ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1) ≤
            200000 * X ^ 2 := by
          have h1 : (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
              (Val.list (xs ++ ys)).wt + 1) ≤ (2 * X) * (100 * X) :=
            Nat.mul_le_mul (by omega) hB
          unfold loopModK
          rw [Nat.mul_assoc]
          nlinarith
        have hinvc : invK * (n + 1) ^ 4 ≤ 100000 * X := by unfold invK; omega
        have hcomc : permK * (n + 1) ^ 3 ≤ 30000 * X := by unfold permK; omega
        have w5 : (encPerm (c0⁻¹ * (t * x))).wt ≤ 4 * X := wz _
        have e3 : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt = (encGroup gs).wt := rfl
        clear dm dap dsn dz dc0 dn dys dys' hap g0 g1 g2 g1' dy dl dpu dhs hf
        simp only [List.length_cons, List.length_nil]
        rw [hr]
        clear_value X xs ys z
        omega
    have hw : (encAcc (combAcc a t (some (x, hs)))).wt < cb := by
      obtain ⟨v', c', -, ⟨⟨rfl, hc⟩, hw⟩⟩ := (EvalAll.wt_lt hcb).exists_eval
      omega
    refine (Det.ite_pos dl (by simp) (Det.letE dy hcb)).mono ?_
    have hcomc : permK * (n + 1) ^ 3 ≤ 30000 * X := by unfold permK; omega
    have e0 : (Val.list [encPerm x, encGroup hs]).wt = (encAcc (some (x, hs))).wt := rfl
    have hsx := wz x
    have hst := wz t
    have htx := wz (t * x)
    clear dy dl dpu dhs hcb hf g0 g1 g2
    simp only [List.length_cons, List.length_nil]
    clear_value X
    omega

/-! ### What the combination computes -/

/-- The set of an accumulator or a piece. -/
def accSet : Acc n → Set (Perm (Fin n))
  | none => ∅
  | some (x, hs) => x • (gens hs : Set (Perm (Fin n)))

/-- The union `⋃_j τ_j A_j` of the pieces. -/
def unionSet (ps : List (Perm (Fin n) × Acc n)) : Set (Perm (Fin n)) :=
  {g | ∃ q ∈ ps, g ∈ q.1 • accSet q.2}

/-- The combination of a list of pieces. -/
def combine (ps : List (Perm (Fin n) × Acc n)) : Acc n :=
  ps.foldl (fun a p => combAcc a p.1 p.2) none

/-- What the accumulator knows after the pieces `pre`, inside a union `U`. -/
def AccInv (U : Set (Perm (Fin n))) (pre : List (Perm (Fin n) × Acc n)) : Acc n → Prop
  | none => unionSet pre = ∅
  | some (c₀, gs) => c₀ ∈ unionSet pre ∧ (∀ g ∈ gs, c₀ * g ∈ U) ∧
      unionSet pre ⊆ c₀ • (gens gs : Set (Perm (Fin n)))

theorem unionSet_snoc (pre : List (Perm (Fin n) × Acc n)) (p : Perm (Fin n) × Acc n) :
    unionSet (pre ++ [p]) = unionSet pre ∪ p.1 • accSet p.2 := by
  ext g
  simp only [unionSet, List.mem_append, List.mem_singleton, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨q, hq | rfl, hg⟩
    · exact Or.inl ⟨q, hq, hg⟩
    · exact Or.inr hg
  · rintro (⟨q, hq, hg⟩ | hg)
    · exact ⟨q, Or.inl hq, hg⟩
    · exact ⟨p, Or.inr rfl, hg⟩

theorem mem_gens_of_mem {gs : List (Perm (Fin n))} {g : Perm (Fin n)} (h : g ∈ gs) :
    g ∈ gens gs := Subgroup.subset_closure h

theorem gens_mono {gs gs' : List (Perm (Fin n))} (h : ∀ g ∈ gs, g ∈ gs') : gens gs ≤ gens gs' :=
  Subgroup.closure_mono fun g hg => h g hg

/-- **One step keeps the invariant**, when the new piece lies in `U` and `U` is empty or a left
coset. -/
theorem accInv_step {U : Set (Perm (Fin n))}
    (hU : U = ∅ ∨ ∃ (c : Perm (Fin n)) (H : Subgroup (Perm (Fin n))), U = c • (H : Set _))
    {pre : List (Perm (Fin n) × Acc n)} (hpre : unionSet pre ⊆ U) {a : Acc n}
    (ha : AccInv U pre a) (p : Perm (Fin n) × Acc n) (hp : p.1 • accSet p.2 ⊆ U) :
    AccInv U (pre ++ [p]) (combAcc a p.1 p.2) := by
  obtain ⟨t, q⟩ := p
  cases q with
  | none =>
    have he : t • accSet (n := n) none = ∅ := Set.smul_set_empty
    cases a with
    | none =>
      show unionSet _ = ∅
      rw [unionSet_snoc, he, Set.union_empty]; exact ha
    | some a =>
      obtain ⟨c₀, gs⟩ := a
      obtain ⟨h1, h2, h3⟩ := ha
      refine ⟨?_, h2, ?_⟩ <;> rw [unionSet_snoc] <;> simp only [he, Set.union_empty]
      · exact h1
      · exact h3
  | some q =>
    obtain ⟨x, hs⟩ := q
    have hpS : t • accSet (some (x, hs)) = t • x • (gens hs : Set (Perm (Fin n))) := rfl
    have htx : t * x ∈ U := hp ⟨x, ⟨1, (gens hs).one_mem, mul_one x⟩, rfl⟩
    have htxh : ∀ h ∈ gens hs, t * x * h ∈ U := fun h hh =>
      hp ⟨x * h, ⟨h, hh, rfl⟩, by simp [mul_assoc]⟩
    cases a with
    | none =>
      have h0 : unionSet pre = ∅ := ha
      refine ⟨?_, fun g hg => htxh g (mem_gens_of_mem hg), ?_⟩
      · rw [unionSet_snoc]
        exact Or.inr ⟨x, ⟨1, (gens hs).one_mem, mul_one x⟩, rfl⟩
      · rw [unionSet_snoc, h0, Set.empty_union]
        rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
        exact ⟨h, hh, by simp [mul_assoc]⟩
    | some a =>
      obtain ⟨c₀, gs⟩ := a
      obtain ⟨h1, h2, h3⟩ := ha
      have hc₀ : c₀ ∈ U := hpre h1
      obtain ⟨c, H, hUc⟩ : ∃ (c : Perm (Fin n)) (H : Subgroup (Perm (Fin n))),
          U = c • (H : Set _) := by
        rcases hU with hU | hU
        · rw [hU] at hc₀; exact hc₀.elim
        · exact hU
      set z := c₀⁻¹ * (t * x) with hz
      have hsub : ∀ g ∈ gs ++ z :: 1 :: hs, g ∈ gens (gs ++ z :: 1 :: hs) :=
        fun g hg => mem_gens_of_mem hg
      have hgs : gens gs ≤ gens (gs ++ z :: 1 :: hs) := gens_mono fun g hg => by simp [hg]
      have hhs : gens hs ≤ gens (gs ++ z :: 1 :: hs) := gens_mono fun g hg => by simp [hg]
      have hzm : z ∈ gens (gs ++ z :: 1 :: hs) := hsub z (by simp)
      refine ⟨?_, ?_, ?_⟩
      · rw [unionSet_snoc]; exact Or.inl h1
      · intro g hg
        simp only [List.mem_append, List.mem_cons] at hg
        rcases hg with hg | rfl | rfl | hg
        · exact h2 g hg
        · rw [mul_inv_cancel_left]; exact htx
        · rw [mul_one]; exact hc₀
        · exact mul_mem_coset hUc htx hc₀ (htxh g (mem_gens_of_mem hg))
      · rw [unionSet_snoc]
        rintro g (hg | hg)
        · obtain ⟨k, hk, rfl⟩ := h3 hg
          exact ⟨k, hgs hk, rfl⟩
        · obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := hg
          refine ⟨z * h, (gens _).mul_mem hzm (hhs hh), ?_⟩
          simp [hz, mul_assoc]

/-- The invariant after a prefix of the pieces. -/
theorem accInv_combine {U : Set (Perm (Fin n))}
    (hU : U = ∅ ∨ ∃ (c : Perm (Fin n)) (H : Subgroup (Perm (Fin n))), U = c • (H : Set _))
    (pre : List (Perm (Fin n) × Acc n)) (hp : ∀ q ∈ pre, q.1 • accSet q.2 ⊆ U) :
    AccInv U pre (combine pre) := by
  induction pre using List.reverseRecOn with
  | nil =>
    show unionSet [] = ∅
    ext g; simp [unionSet]
  | append_singleton pre p ih =>
    have hpre : ∀ q ∈ pre, q.1 • accSet q.2 ⊆ U := fun q hq => hp q (by simp [hq])
    have hsub : unionSet pre ⊆ U := by
      rintro g ⟨q, hq, hg⟩
      exact hpre q hq hg
    rw [combine, List.foldl_append]
    exact accInv_step hU hsub (ih hpre) p (hp p (by simp))

/-- **The combination is correct.** If the union `U` of the pieces is empty or a left coset, the
combination is `[]` exactly when `U` is empty, and otherwise a representative and generators
of `U`. -/
theorem combine_cosetOrEmpty (ps : List (Perm (Fin n) × Acc n))
    (hU : unionSet ps = ∅ ∨ ∃ (c : Perm (Fin n)) (H : Subgroup (Perm (Fin n))),
      unionSet ps = c • (H : Set _)) :
    CosetOrEmpty n (encAcc (combine ps)) (unionSet ps) := by
  have hinv := accInv_combine hU ps fun q hq g hg => ⟨q, hq, hg⟩
  revert hinv
  cases combine ps with
  | none => exact fun h => Or.inl ⟨rfl, h⟩
  | some a =>
    obtain ⟨c₀, gs⟩ := a
    rintro ⟨h1, h2, h3⟩
    refine Or.inr ⟨c₀, gs, rfl, ?_⟩
    rcases hU with hU | ⟨c, H, hU⟩
    · rw [hU] at h1; exact h1.elim
    · exact coset_eq_of_gens hU h1 (fun g hg => h2 g hg) h3

/-! ### Size of the combination -/

/-- The number of generators a piece adds, at most. -/
def accLen : Acc n → ℕ
  | none => 0
  | some (_, hs) => hs.length + 2

theorem length_combine (ps : List (Perm (Fin n) × Acc n)) :
    ∀ c₀ gs, combine ps = some (c₀, gs) → gs.length ≤ (ps.map fun q => accLen q.2).sum := by
  induction ps using List.reverseRecOn with
  | nil => intro c₀ gs h; cases h
  | append_singleton pre p ih =>
    intro c₀ gs h
    rw [combine, List.foldl_append] at h
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, List.foldl_cons, List.foldl_nil] at h ⊢
    change combAcc (combine pre) p.1 p.2 = _ at h
    obtain ⟨t, q⟩ := p
    cases q with
    | none =>
      have := ih c₀ gs (by cases hc : combine pre <;> rw [hc] at h <;> simp only [combAcc] at h <;> exact h)
      have e : accLen (n := n) none = 0 := rfl
      omega
    | some q =>
      obtain ⟨x, hs⟩ := q
      cases hc : combine pre with
      | none =>
        rw [hc] at h
        simp only [combAcc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have e : accLen (t, some (x, hs)).2 = hs.length + 2 := rfl
        omega
      | some a =>
        obtain ⟨c₁, gs₁⟩ := a
        rw [hc] at h
        simp only [combAcc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := ih c₁ gs₁ hc
        have e : accLen (some (x, hs)) = hs.length + 2 := rfl
        simp only [List.length_append, List.length_cons]; omega

/-- The value of a piece: `[encPerm τ, answer]`. -/
def encPiece (p : Perm (Fin n) × Acc n) : Val := .list [encPerm p.1, encAcc p.2]

theorem accLen_lt (p : Perm (Fin n) × Acc n) : accLen p.2 < (encPiece p).wt := by
  obtain ⟨t, q⟩ := p
  cases q with
  | none =>
    have e : accLen (n := n) none = 0 := rfl
    have := wt_le_wt_list (vs := [encPerm t, encAcc (n := n) none]) (v := encPerm t) (by simp)
    have e2 : (encPiece (t, (none : Acc n))).wt = (Val.list [encPerm t, encAcc (n := n) none]).wt :=
      rfl
    show accLen (n := n) none < _
    omega
  | some q =>
    obtain ⟨x, hs⟩ := q
    have h1 : ((1 :: hs).map encPerm).length < (Val.list ((1 :: hs).map encPerm)).wt :=
      length_lt_wt_list _
    have h2 : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
    have h3 : (encGroup hs).wt < (encAcc (some (x, hs))).wt :=
      wt_le_wt_list (vs := [encPerm x, encGroup hs]) (by simp)
    have h4 : (encAcc (some (x, hs))).wt < (encPiece (t, some (x, hs))).wt :=
      wt_le_wt_list (vs := [encPerm t, encAcc (some (x, hs))]) (by simp)
    simp only [List.length_map, List.length_cons] at h1
    simp only [accLen]; omega

theorem sum_accLen_le (ps : List (Perm (Fin n) × Acc n)) :
    (ps.map fun q => accLen q.2).sum ≤ ((ps.map encPiece).map Val.wt).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have := accLen_lt p
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A bound on the weight of an accumulator with at most `L` generators. -/
theorem wt_encAcc_le (a : Acc n) {L : ℕ} (h : ∀ c gs, a = some (c, gs) → gs.length ≤ L) :
    (encAcc a).wt ≤ 100 * ((L + 2) * (n + 1)) ^ 2 := by
  have h4 : 4 ≤ ((L + 2) * (n + 1)) ^ 2 := by
    have : 2 ≤ (L + 2) * (n + 1) := le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
    nlinarith
  cases a with
  | none => show (Val.list []).wt ≤ _; rw [wt_list_nil]; omega
  | some a =>
    obtain ⟨c, gs⟩ := a
    have hl := h c gs rfl
    have h1 := wt_list2_le (encPerm c) (encGroup gs)
    have h2 := wt_encPerm_le c
    have h3 := wt_encGroup_le gs
    have h5 : ((gs.length + 2) * (n + 1)) ^ 2 ≤ ((L + 2) * (n + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2
    have h6 : (n + 1) ^ 2 ≤ ((L + 2) * (n + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) 2
    show (Val.list [encPerm c, encGroup gs]).wt ≤ _
    omega

/-- The weight bound of the accumulators, for an input of weight `W`. -/
def combM (n W : ℕ) : ℕ := 100 * ((W + 2) * (n + 1)) ^ 2

/-- The cost bound of the combination, for an input of weight `W`. -/
def combCost (n W : ℕ) : ℕ :=
  (W + 1) * (combK * (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2 +
    loopModK * (2 * W + combM n W + 1))

/-- **The combination as a program.** A fold of `combStep` over the pieces computes `combine`. -/
theorem comb_spec {P : Program} {b g comp inv app : ℕ} (hb : P.HasAt b (foldlFuns b g))
    (hg : P.funs[g]? = some (combStep comp inv app)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv)) (happ : P.HasAt app (appendFuns app))
    (c : Val) (ps : List (Perm (Fin n) × Acc n)) :
    FunAll P b (.list [c, .list (ps.map encPiece), .list []]) (fun w cost =>
      w = encAcc (combine ps) ∧
        cost ≤ combCost n (Val.list [c, .list (ps.map encPiece), .list []]).wt) := by
  set W := (Val.list [c, .list (ps.map encPiece), .list []]).wt with hW
  have hcW : c.wt < W := wt_le_wt_list (by simp)
  have hxW : (Val.list (ps.map encPiece)).wt < W := wt_le_wt_list (by simp)
  have hsum := sum_wt_lt_wt_list (ps.map encPiece)
  have hacc := sum_accLen_le ps
  have hlen : (ps.map encPiece).length < (Val.list (ps.map encPiece)).wt := length_lt_wt_list _
  rw [List.length_map] at hlen
  -- the weight of every partial combination
  have hM : ∀ i, (encAcc (combine (ps.take i))).wt ≤ combM n W := fun i => by
    refine wt_encAcc_le _ fun c₀ gs h => ?_
    have h1 := length_combine _ c₀ gs h
    have h2 := List.sum_take_add_sum_drop (ps.map fun q => accLen q.2) i
    rw [← List.map_take] at h2
    omega
  have hn4 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  refine (foldl_spec hb (Inv := fun i acc => acc = encAcc (combine (ps.take i)))
    (M := combM n W) (B := fun _ => combK * (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2)
    (by simp [combine, encAcc]) (fun i acc _ h => h ▸ hM i) fun i acc hi h => ?_).mono ?_
  · subst h
    rw [List.length_map] at hi
    have hx : (ps.map encPiece)[i] = encPiece ps[i] := List.getElem_map ..
    rw [hx]
    refine FunAll.mono (combStep_spec hg hcomp hinv happ c (combine (ps.take i)) ps[i].1 ps[i].2)
      fun w cost hw => ⟨?_, ?_⟩
    · show w = encAcc (combine (ps.take (i + 1)))
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
      simp only [combine, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · refine hw.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
      have h3 := wt_list3_le c (encAcc (combine (ps.take i))) (encPiece ps[i])
      have h4 : (encPiece ps[i]).wt < (Val.list (ps.map encPiece)).wt :=
        wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem hi))
      have h5 := hM i
      show (Val.list [c, encAcc (combine (ps.take i)), .list [encPerm ps[i].1, encAcc ps[i].2]]).wt
        + _ ≤ _
      have : encPiece ps[i] = .list [encPerm ps[i].1, encAcc ps[i].2] := rfl
      rw [← this]
      omega
  · rintro w cost ⟨hw, hc⟩
    simp only [List.length_map, List.take_length] at hw hc
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← hW] at hc
    refine ⟨hw, hc.trans ?_⟩
    unfold combCost
    have hl : ps.length + 1 ≤ W + 1 := by omega
    have h1 : ps.length * (combK * (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2) ≤
        (W + 1) * (combK * (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (ps.length + 1) * (W + ps.length + combM n W + 1) ≤
        (W + 1) * (loopModK * (2 * W + combM n W + 1)) := by
      rw [Nat.mul_comm loopModK, Nat.mul_assoc]
      exact Nat.mul_le_mul hl (Nat.mul_le_mul_left _ (by omega))
    have e1 := Nat.mul_add (W + 1) (combK * (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2)
      (loopModK * (2 * W + combM n W + 1))
    omega

end GI.Lang
