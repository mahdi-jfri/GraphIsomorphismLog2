module

public import Workspace.Impl.OutbSuppFix

@[expose] public section

/-!
# Brute-force Frattini descent step modulo `R`

Given subgroups `R ≤ E_H ≤ K ≤ Sym(n)` with `R ⊴ K` and `E_H ⊴ K`, generator lists `es` (`gens es = E_H`,
`es.length ≤ n²`) and `rs` (`gens rs = R`, `rs.length ≤ n²`), and coset representatives `reps` of
`R` in `E_H`:

1. `outbJoinCutF` on `[encGroup rs, outbSv ts]` appends `rs` and `ts` into `encGroup (rs ++ ts)` and
   calls `normalizedIntersectionPrim` on `(rs ++ ts) ∩ (rs ++ ts)` to cut the generator list of
   `R ⊔ ⟨ts⟩` to at most `n²` generators (`outbJoinCut_spec`).
2. `outbDescBody` on `[[encGroup es, encGroup rs, .list (reps.map encPerm)], .nat i, [flag, outbSv ss]]`
   runs one step of the Frattini descent modulo `R`:
   - if `flag ≠ 0`, the descent has finished (`(S ⊓ E_H) / R` is nilpotent) and the state is unchanged;
   - otherwise it computes `M = S ⊓ E_H` (`normalizedIntersectionPrim`), searches for a prime
     `p ≤ n` whose Sylow `p`-subgroup `P / R` of `M / R` is not normal (`outbFindBody`), and either
     corrects every generator `s ∈ ss` into `M s ∩ N_K(P)` (`outbFixBody` mapped via `mapFuns`) and
     forms `S₁ = R ⊔ ⟨ts⟩` with at most `n²` generators (`outbJoinCutF`), or sets `flag = 1`.
3. `outbDesc_step` proves that `outbDescBody` preserves `OutbDescInv K E_H R` from `i` to `i + 1`,
   and `outbDesc_done` shows that after `n² + 1` steps the flag is `1` and `(S ⊓ E_H) / R` is
   nilpotent.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Helper lemmas for subgroups, lists, and `mkGroup` -/

/-- An element of `K` conjugates `N` into itself when `N ⊴ K`. -/
theorem outb_conj_mem {K N : Subgroup (Perm (Fin n))} [hN : (N.subgroupOf K).Normal]
    (hNK : N ≤ K) {g x : Perm (Fin n)} (hg : g ∈ K) (hx : x ∈ N) : g * x * g⁻¹ ∈ N := by
  have h := hN.conj_mem ⟨x, hNK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using h

/-- If `R ⊴ K` and `M ≤ K`, then `R.subgroupOf M` is normal in `M`. -/
theorem outb_normal_subgroupOf_of_le {K M R : Subgroup (Perm (Fin n))}
    [hRK_norm : (R.subgroupOf K).Normal] (hRK : R ≤ K) (hMK : M ≤ K) :
    (R.subgroupOf M).Normal :=
  ⟨fun ⟨r, hrM⟩ hr ⟨m, hmM⟩ => by
    have := hRK_norm.conj_mem ⟨r, hRK hr⟩ hr ⟨m, hMK hmM⟩
    simpa [Subgroup.mem_subgroupOf] using this⟩

theorem outb_forall₂_mem_right {α β : Type*} {Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Q l₁ l₂ → ∀ t ∈ l₂, ∃ s ∈ l₁, Q s t
  | _, _, List.Forall₂.nil => fun _ h => absurd h List.not_mem_nil
  | _, _, List.Forall₂.cons (a := a) h hr => fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨s, hs, hq⟩ := outb_forall₂_mem_right hr t ht
      exact ⟨s, List.mem_cons_of_mem _ hs, hq⟩

theorem outb_forall₂_mem_left {α β : Type*} {Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Q l₁ l₂ → ∀ s ∈ l₁, ∃ t ∈ l₂, Q s t
  | _, _, List.Forall₂.nil => fun _ h => absurd h List.not_mem_nil
  | _, _, List.Forall₂.cons (b := b) h hr => fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨t, ht, hq⟩ := outb_forall₂_mem_left hr s hs
      exact ⟨t, List.mem_cons_of_mem _ ht, hq⟩

/-- The value of a list of generators. -/
def outbSv (ss : List (Perm (Fin n))) : Val := .list (ss.map encPerm)

/-! ### Joining `rs` and `ts` and cutting to `≤ n²` generators (`outbJoinCutF`) -/

/-- `outbJoinCutF`, on `[encGroup rs, outbSv ts]`:
appends `(1 :: rs).map encPerm` and `ts.map encPerm` via `mg + 4` (`appendFuns`) to form
`encGroup (rs ++ ts)`, and calls `normalizedIntersectionPrim` (`jni`) on
`[encGroup (rs ++ ts), encGroup (rs ++ ts)]` to obtain `outbSv s1s` with `s1s.length ≤ n²`
and `gens s1s = gens (rs ++ ts)`. -/
def outbJoinCutF (mg jni : ℕ) : Expr :=
  .letE (mk2 (.get (arg 0) (.nat 0))
    (.call (mg + 4) (mk2 (.get (arg 0) (.nat 1)) (arg 1))))
  (.prim jni (mk2 (.var 1) (.var 1)))

/-- Cost bound of `outbJoinCutF`. -/
def outbJoinCutCost (pni : Prim) (n : ℕ) : ℕ :=
  pni.boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 8 * (n + 1) ^ 8

/-- **Specification of `outbJoinCutF`**: produces `outbSv s1s` with `s1s.length ≤ n²` and
`gens s1s = gens (rs ++ ts)`. -/
theorem outbJoinCut_spec {hni : NormalizedIntersection} {P : Program} {jc mg jni : ℕ}
    (hjc : P.funs[jc]? = some (outbJoinCutF mg jni))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hjni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    {rs ts : List (Perm (Fin n))} (hrl : rs.length ≤ n ^ 2) (htl : ts.length ≤ n ^ 2) :
    FunAll P jc (.list [encGroup rs, outbSv ts]) (fun w cost =>
      ∃ s1s : List (Perm (Fin n)), w = outbSv s1s ∧ s1s.length ≤ n ^ 2 ∧
        gens s1s = gens (rs ++ ts) ∧
        cost ≤ outbJoinCutCost (normalizedIntersectionPrim hni) n) := by
  have happ : P.HasAt (mg + 4) (appendFuns (mg + 4)) := by
    simp only [mkGroupFuns] at hmg
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hmg.right
  set in_v := Val.list [encGroup rs, outbSv ts] with hin_v
  have hrl1 : (1 :: rs).length ≤ n ^ 2 + 1 := by simp [hrl]
  have hrtl : (rs ++ ts).length ≤ 2 * n ^ 2 := by simp; omega
  have hRw := wt_encGroup_sq hrl
  have hR1w : (Val.list ((1 :: rs).map encPerm)).wt ≤ 160 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hRw
  have htw : (outbSv ts).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq htl
  have hRTw := wt_encGroup_two_sq hrtl
  have hRT1w : (Val.list ((1 :: (rs ++ ts)).map encPerm)).wt ≤ 640 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hRTw
  have hinw : in_v.wt ≤ 2 * ((encGroup rs).wt + (outbSv ts).wt) + 6 :=
    wt_list2_le (encGroup rs) (outbSv ts)
  have hnw := wt_nat_le n
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
  -- step 1: form `encGroup (rs ++ ts)`
  have dG : Det P [in_v]
      (mk2 (.get (arg 0) (.nat 0)) (.call (mg + 4) (mk2 (.get (arg 0) (.nat 1)) (arg 1))))
      (encGroup (rs ++ ts)) (2 * 10 ^ 7 * (n + 1) ^ 8) := by
    have d0 := Det.arg' (P := P) (vs := [encGroup rs, outbSv ts]) (rest := [])
      (j := 0) (v := encGroup rs) rfl
    have d1 := Det.arg' (P := P) (vs := [encGroup rs, outbSv ts]) (rest := [])
      (j := 1) (v := outbSv ts) rfl
    rw [← hin_v] at d0 d1
    have dn := Det.get' d0 (Det.nat 0) (v := .nat n) rfl
    have dr1 := Det.get' d0 (Det.nat 1) (v := .list ((1 :: rs).map encPerm)) rfl
    have hap0 := append_spec happ ((1 :: rs).map encPerm) (ts.map encPerm)
    have hmap_eq : ((1 :: rs).map encPerm) ++ ts.map encPerm = (1 :: (rs ++ ts)).map encPerm := by
      simp
    rw [hmap_eq] at hap0
    have hapd : FunDet P (mg + 4) (.list [.list ((1 :: rs).map encPerm), outbSv ts])
        (.list ((1 :: (rs ++ ts)).map encPerm))
        (loopModK * (ts.length + 1) *
          ((Val.list [.list ((1 :: rs).map encPerm), outbSv ts]).wt + ts.length +
            (Val.list ((1 :: (rs ++ ts)).map encPerm)).wt + 1)) :=
      FunAll.mono hap0 fun w c hw => by
        obtain ⟨rfl, hc⟩ := hw
        exact ⟨rfl, by simpa [outbSv] using hc⟩
    have dcall := Det.call (Det.mk2 dr1 d1) hapd
    have dmk := Det.mk2 dn dcall
    refine dmk.mono ?_
    have htl2 : ts.length + 1 ≤ (n + 1) ^ 2 := by
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have htl6 : ts.length ≤ (n + 1) ^ 6 := by omega
    have hw_pair := wt_list2_le (.list ((1 :: rs).map encPerm)) (outbSv ts)
    have hw_G : (Val.list [.nat n, .list ((1 :: (rs ++ ts)).map encPerm)]).wt =
        (encGroup (rs ++ ts)).wt := rfl
    have hL : loopModK * (ts.length + 1) *
        ((Val.list [.list ((1 :: rs).map encPerm), outbSv ts]).wt + ts.length +
          (Val.list ((1 :: (rs ++ ts)).map encPerm)).wt + 1) ≤
        10 ^ 7 * (n + 1) ^ 8 := by
      calc loopModK * (ts.length + 1) *
          ((Val.list [.list ((1 :: rs).map encPerm), outbSv ts]).wt + ts.length +
            (Val.list ((1 :: (rs ++ ts)).map encPerm)).wt + 1) ≤
          loopModK * (n + 1) ^ 2 * (3000 * (n + 1) ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ htl2) (by
              clear d0 d1 dn dr1 hap0 hapd dcall dmk
              clear_value in_v
              omega)
        _ = 3 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
        _ ≤ 10 ^ 7 * (n + 1) ^ 8 := Nat.mul_le_mul_right _ (by norm_num)
    clear d0 d1 dn dr1 hap0 hapd dcall dmk
    clear_value in_v
    omega
  -- step 2: call `jni` on `[encGroup (rs ++ ts), encGroup (rs ++ ts)]`
  set env1 := [in_v, encGroup (rs ++ ts)]
  have dv1 := Det.var' (P := P) (env := env1) (i := 1) (v := encGroup (rs ++ ts)) rfl
  have hnorm : GI.Lang.Normalizes (gens (rs ++ ts)) (gens (rs ++ ts)) := fun x hx y hy =>
    (gens (rs ++ ts)).mul_mem ((gens (rs ++ ts)).mul_mem hx hy) ((gens (rs ++ ts)).inv_mem hx)
  have dni := normalizedIntersection_call hni hjni (Det.mk2 dv1 dv1)
    ⟨rs ++ ts, rfl, rfl⟩ ⟨rs ++ ts, rfl, rfl⟩ hnorm
  refine FunAll.intro hjc (EvalAll.letE dG fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  refine dni.mono fun w c2 hw2 => ?_
  obtain ⟨⟨s1s, rfl, hs1l, hs1g⟩, hc2⟩ := hw2
  rw [inf_idem] at hs1g
  refine ⟨s1s, rfl, hs1l, hs1g, ?_⟩
  have hs1w : (Val.list (s1s.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hs1l
  have hGGw := wt_list2_le (encGroup (rs ++ ts)) (encGroup (rs ++ ts))
  have hNIb := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup (rs ++ ts), encGroup (rs ++ ts)]).size ≤ 10 ^ 4 * (n + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear dG dv1 dni
        clear_value in_v env1
        omega))
  unfold outbJoinCutCost
  clear dG dv1 dni
  clear_value in_v env1
  omega

/-! ### The descent invariant and termination -/

/-- **The invariant of the descent modulo `R`** after `i` steps. -/
def OutbDescInv (K E_H R : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  ∃ ss : List (Perm (Fin n)), ss.length ≤ n ^ 2 ∧ R ≤ gens ss ∧ gens ss ≤ K ∧ gens ss ⊔ E_H = K ∧
    ((acc = .list [.nat 1, outbSv ss] ∧
        ∃ (_ : (R.subgroupOf (gens ss ⊓ E_H : Subgroup _)).Normal),
          Group.IsNilpotent ((gens ss ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (gens ss ⊓ E_H : Subgroup _))) ∨
      (acc = .list [.nat 0, outbSv ss] ∧
        2 ^ i * Nat.card (gens ss ⊓ E_H : Subgroup _) ≤ Nat.card E_H))

theorem outb_desc_wt {K E_H R : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (h : OutbDescInv K E_H R i acc) : acc.wt ≤ 40 * (n + 1) ^ 6 := by
  obtain ⟨ss, hl, -, -, -, h⟩ := h
  have h1 : (outbSv ss).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hl
  have h0 := wt_nat_le 0
  have h1' := wt_nat_le 1
  have hk : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have := wt_list2_le (.nat 1) (outbSv ss); omega
  · have := wt_list2_le (.nat 0) (outbSv ss); omega

/-- **The end of the descent modulo `R`**: after `n² + 1` steps the flag is `1` and
`(S ⊓ E_H) / R` is nilpotent. -/
theorem outbDesc_done {K E_H R : Subgroup (Perm (Fin n))} {acc : Val}
    (h : OutbDescInv K E_H R (n ^ 2 + 1) acc) :
    ∃ ss : List (Perm (Fin n)), ss.length ≤ n ^ 2 ∧ R ≤ gens ss ∧ gens ss ≤ K ∧ gens ss ⊔ E_H = K ∧
      acc = .list [.nat 1, outbSv ss] ∧
      ∃ (_ : (R.subgroupOf (gens ss ⊓ E_H : Subgroup _)).Normal),
        Group.IsNilpotent ((gens ss ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (gens ss ⊓ E_H : Subgroup _)) := by
  obtain ⟨ss, hl, hRS, hSK, hsup, ⟨rfl, hnil⟩ | ⟨rfl, hc⟩⟩ := h
  · exact ⟨ss, hl, hRS, hSK, hsup, rfl, hnil⟩
  · exfalso
    have h1 := GI.CitedChecks.card_lt_two_pow E_H
    have h2 : 0 < Nat.card (gens ss ⊓ E_H : Subgroup _) := Nat.card_pos
    have : 2 ^ (n ^ 2 + 1) ≤ 2 ^ (n ^ 2 + 1) * Nat.card (gens ss ⊓ E_H : Subgroup _) :=
      Nat.le_mul_of_pos_right _ h2
    omega

/-! ### One descent step `outbDescBody` -/

/-- **One descent step modulo `R`** on
`[[encGroup es, encGroup rs, .list (reps.map encPerm)], .nat i, [flag, outbSv ss]]`:
1. If `flag ≠ 0`, returns `arg 2`.
2. Otherwise:
   - `.var 1 = encGroup hs` (`gens hs = gens ss`)
   - `.var 2 = v2` (`GensVal n v2 (gens hs ⊓ gens es)`)
   - `.var 3 = encGroup ms` (`gens ms = gens ss ⊓ gens es`)
   - `.var 4 = outbFindBody [encGroup rs, encGroup ms, .list (reps.map encPerm)]`
   - If `.get (.var 4) (.nat 1) ≠ 0`, maps `fx` (`mf`) over `outbSv ss` with context
     `[encGroup ms, .get (.var 4) (.nat 2), .list (reps.map encPerm)]` and joins/cuts with `rs`
     via `jc` (`outbJoinCutF`); otherwise returns `[.nat 1, outbSv ss]`. -/
def outbDescBody (mg jni fd_fn mf jc : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 0)) (arg 2)
  (.letE (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (arg 2) (.nat 1))))
  (.letE (.prim jni (mk2 (.var 1) (.get (arg 0) (.nat 0))))
  (.letE (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 2)))
  (.letE (.call fd_fn (mk3 (.get (arg 0) (.nat 1)) (.var 3) (.get (arg 0) (.nat 2))))
  (.ite (.get (.var 4) (.nat 1))
    (mk2 (.nat 0) (.call jc (mk2 (.get (arg 0) (.nat 1))
      (.call mf (mk2 (mk3 (.var 3) (.get (.var 4) (.nat 2)) (.get (arg 0) (.nat 2)))
        (.get (arg 2) (.nat 1)))))))
    (mk2 (.nat 1) (.get (arg 2) (.nat 1))))))))

/-- Where the descent step and its modules sit. -/
structure OutbDescAt (P : Program)
    (g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx : ℕ)
    (hni : NormalizedIntersection) (hnc : NormalClosure) (hord : GroupOrder)
    (hmem : Membership) : Prop where
  step : P.funs[g]? = some (outbDescBody mg jni fd_fn mf jc)
  joinCut : P.funs[jc]? = some (outbJoinCutF mg jni)
  ni : P.prims[jni]? = some (normalizedIntersectionPrim hni)
  find : OutbFindAt P fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy mg le_s jnc jord jm
    hnc hord hmem
  map : P.HasAt mf (mapFuns mf fx)
  fix : OutbFixAt P fx fd_fx st_fx cp iv mc cj le_fx jm hmem

/-- Cost bound of one descent step for `reps` of length `m`. -/
def outbDescCost (pni pnc pord pm : Prim) (n m : ℕ) : ℕ :=
  2 * pni.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    outbFindCost pnc pord pm n m +
    (n + 1) ^ 2 * outbFixCost pm n m +
    10 ^ 9 * (m + 1) ^ 2 * (n + 1) ^ 9

set_option maxHeartbeats 800000 in
open Classical in
/-- **One descent step modulo `R`** preserves `OutbDescInv K (gens es) (gens rs)` from `i` to `i + 1`. -/
theorem outbDesc_step {hni : NormalizedIntersection} {hnc : NormalClosure}
    {hord : GroupOrder} {hmem : Membership} {P : Program}
    {g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx : ℕ}
    (hP : OutbDescAt P g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx hni hnc hord hmem)
    {K : Subgroup (Perm (Fin n))} {es rs reps : List (Perm (Fin n))}
    (hRE : gens rs ≤ gens es) (hEK : gens es ≤ K)
    [((gens es).subgroupOf K).Normal] [((gens rs).subgroupOf K).Normal]
    (hel : es.length ≤ n ^ 2) (hrl : rs.length ≤ n ^ 2)
    (hcov : ∀ x ∈ gens es, TmRpCov (gens rs) reps x)
    {i : ℕ} (hi : i ≤ n ^ 2) {acc : Val}
    (hinv : OutbDescInv K (gens es) (gens rs) i acc) :
    FunAll P g (.list [.list [encGroup es, encGroup rs, .list (reps.map encPerm)], .nat i, acc])
      (fun w c => OutbDescInv K (gens es) (gens rs) (i + 1) w ∧
        c ≤ outbDescCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
          (groupOrderPrim hord) (membershipPrim hmem) n reps.length) := by
  set xs := reps.map encPerm with hxs
  set c := Val.list [encGroup es, encGroup rs, .list xs] with hc
  set C := outbDescCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
    (groupOrderPrim hord) (membershipPrim hmem) n reps.length with hC
  set Z2 := (reps.length + 1) ^ 2 * (n + 1) ^ 6 with hZ2
  set Z9 := (reps.length + 1) ^ 2 * (n + 1) ^ 9 with hZ9
  have hn12 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn19 : 1 ≤ (n + 1) ^ 9 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn89 : (n + 1) ^ 8 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hm12 : 1 ≤ (reps.length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hZ2_Z9 : Z2 ≤ Z9 := Nat.mul_le_mul_left _ hn69
  have hn6_Z2 : (n + 1) ^ 6 ≤ Z2 := by
    calc (n + 1) ^ 6 = 1 * (n + 1) ^ 6 := (one_mul _).symm
      _ ≤ Z2 := Nat.mul_le_mul_right _ hm12
  have hn9_Z9 : (n + 1) ^ 9 ≤ Z9 := by
    calc (n + 1) ^ 9 = 1 * (n + 1) ^ 9 := (one_mul _).symm
      _ ≤ Z9 := Nat.mul_le_mul_right _ hm12
  have hn8_Z9 : (n + 1) ^ 8 ≤ Z9 := hn89.trans hn9_Z9
  have haw := outb_desc_wt hinv
  have hEw := wt_encGroup_sq hel
  have hRw := wt_encGroup_sq hrl
  have hrepw : (Val.list xs).wt ≤ 13 * Z2 := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := outb_wt_reps_le reps
      _ ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ hn26
      _ = 13 * Z2 := by rw [hZ2]; ring
  have hcw0 : c.wt ≤ 2 * ((encGroup es).wt + (encGroup rs).wt + (Val.list xs).wt) + 7 :=
    wt_list3_le (encGroup es) (encGroup rs) (.list xs)
  have hcw : c.wt ≤ 1000 * Z2 := by
    clear_value c xs C Z2 Z9
    omega
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
  have hiw := wt_nat_le i
  have hnw := wt_nat_le n
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hRK : gens rs ≤ K := hRE.trans hEK
  set NB := (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) with hNB
  set FC := outbFindCost (normalClosurePrim hnc) (groupOrderPrim hord)
    (membershipPrim hmem) n reps.length with hFC
  set Fx := outbFixCost (membershipPrim hmem) n reps.length with hFx
  have hCe : C = 2 * NB + FC + (n + 1) ^ 2 * Fx + 10 ^ 9 * Z9 := by
    simp only [hC, outbDescCost, hNB, hFC, hFx, hZ9]; ring
  set a := Val.list [c, .nat i, acc] with ha
  have haw3 : a.wt ≤ 2 * (c.wt + (Val.nat i).wt + acc.wt) + 7 := wt_list3_le c (.nat i) acc
  refine FunAll.intro hP.step ?_
  unfold outbDescBody
  obtain ⟨ss, hl, hRS, hSK, hsup, ⟨rfl, hnil⟩ | ⟨rfl, hcard⟩⟩ := hinv
  · -- the descent has already ended (`flag = 1`)
    have dacc := Det.arg' (P := P) (vs := [c, .nat i, .list [.nat 1, outbSv ss]]) (rest := [])
      (j := 2) rfl
    rw [← ha] at dacc
    have d1 := Det.get' dacc (Det.nat 0) (v := .nat 1) rfl
    refine (Det.ite_pos d1 one_ne_zero dacc).post fun c' hc' => ⟨⟨ss, hl, hRS, hSK, hsup,
      Or.inl ⟨rfl, hnil⟩⟩, ?_⟩
    clear dacc d1
    clear_value a c xs C Z2 Z9 NB FC Fx
    omega
  -- the descent continues (`flag = 0`)
  set acc0 := Val.list [.nat 0, outbSv ss] with hacc0
  have hsvw : (outbSv ss).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hl
  have hmk : 8 * mkGroupK * (n + 1) ^ 9 ≤ 10 ^ 6 * Z9 := by
    simp only [mkGroupK]; omega
  have dacc := Det.arg' (P := P) (vs := [c, .nat i, acc0]) (rest := []) (j := 2) rfl
  rw [← ha] at dacc
  have d0 := Det.get' dacc (Det.nat 0) (v := .nat 0) rfl
  refine (outb_ite (R := fun w c' => OutbDescInv K (gens es) (gens rs) (i + 1) w ∧
    c' + 10 ^ 4 * Z2 ≤ C) d0 (fun h => absurd rfl h) fun _ => ?_).mono fun w c' h => ?_
  rotate_left
  · obtain ⟨ce, ⟨hI, hce⟩, hc'⟩ := h
    have hwI := outb_desc_wt hI
    refine ⟨hI, ?_⟩
    clear dacc d0
    clear_value a c xs C Z2 Z9 acc0 NB FC Fx
    omega
  -- step 1: `encGroup hs` (`gens hs = gens ss`)
  have dc := Det.arg' (P := P) (vs := [c, .nat i, acc0]) (rest := []) (j := 0) rfl
  have dn := Det.get' (Det.get' dc (Det.nat 0) (v := encGroup es) rfl) (Det.nat 0) (v := .nat n) rfl
  have dsv := Det.get' dacc (Det.nat 1) (v := outbSv ss) rfl
  obtain ⟨hs, hsl, hsg, dS, hSw⟩ := outb_mk_det hP.find.step.mg dn dsv
    (⟨ss, rfl, hl, rfl⟩ : GensVal n (outbSv ss) (gens ss))
  rw [← ha] at dS
  clear dc dn dsv
  refine EvalAll.letE dS fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  clear dS
  -- step 2: `S ⊓ E_H` (`v2`)
  have dS1 := Det.var' (P := P) (env := [a, encGroup hs]) (i := 1) (v := encGroup hs) rfl
  have dc' := Det.arg' (P := P) (vs := [c, .nat i, acc0]) (rest := [encGroup hs]) (j := 0) rfl
  rw [← ha] at dc'
  have dEv := Det.get' dc' (Det.nat 0) (v := encGroup es) rfl
  have hnorm_SE : GI.Lang.Normalizes (gens hs) (gens es) := fun x hx y hy =>
    outb_conj_mem hEK (hSK (hsg ▸ hx)) hy
  have hSE_w := wt_list2_le (encGroup hs) (encGroup es)
  have hNIb1 := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup hs, encGroup es]).size ≤ 10 ^ 4 * (n + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear dacc d0 dS1 dc' dEv
        clear_value a c xs C Z2 Z9 acc0 NB FC Fx
        omega))
  refine EvalAll.letE (normalizedIntersection_call hni hP.ni (Det.mk2 dS1 dEv) ⟨hs, rfl, rfl⟩
    ⟨es, rfl, rfl⟩ hnorm_SE) fun v2 c2 h2 => ?_
  obtain ⟨hMv, hc2⟩ := h2
  clear dS1 dc' dEv
  have hv2w := GensVal.wt_le hMv
  -- step 3: `encGroup ms` (`gens ms = gens ss ⊓ gens es`)
  have dn2 := Det.get' (Det.get' (Det.arg' (P := P) (vs := [c, .nat i, acc0])
    (rest := [encGroup hs, v2]) (j := 0) rfl) (Det.nat 0) (v := encGroup es) rfl) (Det.nat 0)
    (v := .nat n) rfl
  rw [← ha] at dn2
  obtain ⟨ms, hml, hmg_eq, dM, hMw⟩ := outb_mk_det hP.find.step.mg dn2
    (Det.var' (P := P) (env := [a, encGroup hs, v2]) (i := 2) (v := v2) rfl) hMv
  rw [hsg] at hmg_eq
  clear dn2
  refine EvalAll.letE dM fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  clear dM
  -- step 4: call `fd_fn` (`outbFindBody`) on `[encGroup rs, encGroup ms, .list xs]`
  set env3 := [a, encGroup hs, v2, encGroup ms] with henv3
  have dc3 := Det.arg' (P := P) (vs := [c, .nat i, acc0])
    (rest := [encGroup hs, v2, encGroup ms]) (j := 0) rfl
  rw [← ha] at dc3
  have dR3 := Det.get' dc3 (Det.nat 1) (v := encGroup rs) rfl
  have dM3 := Det.var' (P := P) (env := env3) (i := 3) (v := encGroup ms) rfl
  have drep3 := Det.get' dc3 (Det.nat 2) (v := .list xs) rfl
  have dfd_arg := Det.mk3 dR3 dM3 drep3
  have hRM : gens rs ≤ gens ms := by
    rw [hmg_eq]; exact le_inf hRS hRE
  have hME : gens ms ≤ gens es := by
    rw [hmg_eq]; exact inf_le_right
  have hMK : gens ms ≤ K := hME.trans hEK
  have : ((gens rs).subgroupOf (gens ms)).Normal := outb_normal_subgroupOf_of_le hRK hMK
  have hfd_argw := wt_list3_le (encGroup rs) (encGroup ms) (.list xs)
  refine EvalAll.letE (Ra := fun w cw => OutbSearchInv (gens rs) (gens ms) (n + 1) w ∧
      cw ≤ FC + 2 * 10 ^ 4 * Z2)
    (EvalAll.call_funAll dfd_arg fun v ca hv => ?_) fun v4 c4 h4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (outbFind_spec hP.find hRM hME hrl hml hcov).mono fun w cw hw => ⟨hw.1, ?_⟩
    have hw_wt := outb_search_wt hRM hw.1
    have hcw' := hw.2
    rw [← hFC] at hcw'
    clear dc3 dR3 dM3 drep3 dfd_arg dacc d0
    clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3
    omega
  clear dc3 dR3 dM3 drep3 dfd_arg
  obtain ⟨hres, hc4⟩ := h4
  have hv4w := outb_search_wt hRM hres
  set env4 := env3 ++ [v4] with henv4
  have dres := Det.var' (P := P) (env := env4) (i := 4) (v := v4) rfl
  have dsv4 := Det.get' (Det.arg' (P := P) (vs := [c, .nat i, acc0])
    (rest := [encGroup hs, v2, encGroup ms, v4]) (j := 2) rfl) (Det.nat 1) (v := outbSv ss) rfl
  rw [← ha] at dsv4
  have hnsv_w := wt_list2_le (.nat n) (outbSv ss)
  have hnv2_w := wt_list2_le (.nat n) v2
  rcases hres with ⟨r, rfl, hsv⟩ | ⟨p, ps, rfl, hpl, hp, _hpn, hsyl, hnn⟩
  · -- `(S ⊓ E_H) / R` is nilpotent (`flag_search = 0`): set `flag = 1`
    have dt := Det.get' dres (Det.nat 1) (v := .nat 0) rfl
    refine (Det.ite_zero dt (Det.mk2 (Det.nat 1) dsv4)).post fun c' hc' => ⟨⟨ss, hl, hRS, hSK, hsup,
      Or.inl ⟨rfl, ?_⟩⟩, ?_⟩
    · rw [← hmg_eq]
      exact ⟨inferInstance, outb_sieve_end hRM hsv⟩
    · have := wt_list2_le (.nat 1) (outbSv ss)
      clear dres dsv4 dt dacc d0
      clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
      omega
  · -- nonnormal Sylow subgroup `P = gens ps` found (`flag_search = 1`)
    have dt := Det.get' dres (Det.nat 1) (v := .nat 1) rfl
    have dc4 := Det.arg' (P := P) (vs := [c, .nat i, acc0])
      (rest := [encGroup hs, v2, encGroup ms, .list [.nat 0, .nat 1, encGroup ps]]) (j := 0) rfl
    rw [← ha] at dc4
    have dR4 := Det.get' dc4 (Det.nat 1) (v := encGroup rs) rfl
    have drep4 := Det.get' dc4 (Det.nat 2) (v := .list xs) rfl
    have dM4 := Det.var' (P := P) (env := env4) (i := 3) (v := encGroup ms) rfl
    have dP4 := Det.get' dres (Det.nat 2) (v := encGroup ps) rfl
    have dfa := Det.mk2 (Det.mk3 dM4 dP4 drep4) dsv4
    have hsR_inv : ∀ s ∈ ss, ∀ r ∈ gens rs, s⁻¹ * r * s ∈ gens rs := by
      intro s hs_mem r hr
      have hsK : s ∈ K := hSK (Subgroup.subset_closure hs_mem)
      have := outb_conj_mem hRK (K.inv_mem hsK) hr
      simpa [mul_assoc] using this
    have hsM : ∀ s ∈ ss, ∀ m ∈ gens ms, s * m * s⁻¹ ∈ gens ms := by
      intro s hs_mem m hm
      rw [hmg_eq] at hm ⊢
      have hs' : s ∈ gens ss := Subgroup.subset_closure hs_mem
      exact ⟨(gens ss).mul_mem ((gens ss).mul_mem hs' hm.1) ((gens ss).inv_mem hs'),
        outb_conj_mem hEK (hSK hs') hm.2⟩
    have hmap := map_spec hP.map (c := .list [encGroup ms, encGroup ps, .list xs])
      (xs := ss.map encPerm)
      (R := fun x w => ∀ s, x = encPerm s → ∃ t, w = encPerm t ∧
        (∃ g ∈ gens ms, t = g * s ∧ t ∈ Subgroup.normalizer (gens ps : Set (Perm (Fin n)))))
      (B := fun _ => Fx) (fun x hx => by
        obtain ⟨s, hs_mem, rfl⟩ := List.mem_map.mp hx
        exact (outbFix_spec hP.fix hME hml hpl hcov hp hsyl s (hsR_inv s hs_mem)
          (hsM s hs_mem)).mono fun w cw h => by
          obtain ⟨g, hg, rfl, hgn, hcw⟩ := h
          exact ⟨fun s' hs' => by
            obtain rfl := encPerm_injective hs'
            exact ⟨g * s, rfl, g, hg, rfl, hgn⟩, hcw⟩)
    refine (outb_ite (R := fun w cw => OutbDescInv K (gens es) (gens rs) (i + 1) w ∧
      cw ≤ NB + (n + 1) ^ 2 * Fx + 5 * 10 ^ 8 * Z9) dt (fun _ => ?_)
      fun h => absurd h one_ne_zero).mono fun w cw h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hcw⟩ := h
      refine ⟨hI, ?_⟩
      have hwI := outb_desc_wt hI
      clear dres dsv4 dt dc4 dR4 drep4 dM4 dP4 dfa hmap dacc d0
      clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
      omega
    -- step 5a: evaluate `.call mf (...)`
    have dmf_eval : EvalAll P env4
        (.call mf (mk2 (mk3 (.var 3) (.get (.var 4) (.nat 2)) (.get (arg 0) (.nat 2)))
          (.get (arg 2) (.nat 1))))
        (fun v_ts cts => ∃ ts : List (Perm (Fin n)), v_ts = outbSv ts ∧ ts.length = ss.length ∧
          List.Forall₂ (fun s t => ∃ g ∈ gens ms, t = g * s ∧
            t ∈ Subgroup.normalizer (gens ps : Set (Perm (Fin n)))) ss ts ∧
          cts ≤ (n + 1) ^ 2 * Fx + 2 * 10 ^ 7 * Z9) := by
      refine EvalAll.call_funAll dfa fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine hmap.mono fun w cb h => ?_
      obtain ⟨ws, rfl, h2, hcb⟩ := h
      obtain ⟨ts, rfl, hts⟩ := outb_forall₂_perm h2
      refine ⟨ts, rfl, hts.length_eq.symm, hts, ?_⟩
      have htl : ts.length ≤ n ^ 2 := hts.length_eq ▸ hl
      have hsum : ((ss.map encPerm).map fun _ => Fx).sum ≤ (n + 1) ^ 2 * Fx := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
        have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
        exact Nat.mul_le_mul_right _ (by omega)
      have htw : (outbSv ts).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq htl
      have hPw := wt_encGroup_two_sq hpl
      have hc_mf := wt_list3_le (encGroup ms) (encGroup ps) (.list xs)
      have hin_mf := wt_list2_le (.list [encGroup ms, encGroup ps, .list xs]) (outbSv ss)
      have hlen : (ss.map encPerm).length + 1 ≤ (n + 1) ^ 2 := by
        rw [List.length_map]
        have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
        omega
      have e1 : (Val.list (ss.map encPerm)).wt = (outbSv ss).wt := rfl
      have e1' : (Val.list [.list [encGroup ms, encGroup ps, .list xs], .list (ss.map encPerm)]).wt =
          (Val.list [.list [encGroup ms, encGroup ps, .list xs], outbSv ss]).wt := rfl
      have e2 : (Val.list (ts.map encPerm)).wt = (outbSv ts).wt := rfl
      have hwt_mf : (Val.list [.list [encGroup ms, encGroup ps, .list xs],
          .list (ss.map encPerm)]).wt + (Val.list (ts.map encPerm)).wt + 1 ≤ 4000 * Z2 := by
        clear dres dsv4 dt dc4 dR4 drep4 dM4 dP4 dfa hmap dacc d0
        clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
        omega
      have hL : mapK * ((ss.map encPerm).length + 1) *
          ((Val.list [.list [encGroup ms, encGroup ps, .list xs], .list (ss.map encPerm)]).wt +
            (Val.list (ts.map encPerm)).wt + 1) ≤ 4 * 10 ^ 6 * Z9 := by
        have hn23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
        calc _ ≤ mapK * (n + 1) ^ 3 * (4000 * Z2) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (hlen.trans hn23)) hwt_mf
          _ = 4 * 10 ^ 6 * Z9 := by simp only [mapK, hZ2, hZ9]; ring
      clear dres dsv4 dt dc4 dR4 drep4 dM4 dP4 dfa hmap dacc d0 hwt_mf
      clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
      omega
    -- step 5b: call `jc` (`outbJoinCutF`) on `[encGroup rs, v_ts]` and wrap in `mk2 (.nat 0) (...)`
    have djc_arg := EvalAll.mk2_last dR4 dmf_eval
    have djc_call : EvalAll P env4
        (.call jc (mk2 (.get (arg 0) (.nat 1))
          (.call mf (mk2 (mk3 (.var 3) (.get (.var 4) (.nat 2)) (.get (arg 0) (.nat 2)))
            (.get (arg 2) (.nat 1))))))
        (fun w_s1 cs1 => ∃ s1s ts : List (Perm (Fin n)),
          w_s1 = outbSv s1s ∧ s1s.length ≤ n ^ 2 ∧ gens s1s = gens (rs ++ ts) ∧
          ts.length = ss.length ∧
          List.Forall₂ (fun s t => ∃ g ∈ gens ms, t = g * s ∧
            t ∈ Subgroup.normalizer (gens ps : Set (Perm (Fin n)))) ss ts ∧
          cs1 ≤ NB + (n + 1) ^ 2 * Fx + 2 * 10 ^ 8 * Z9) := by
      refine EvalAll.call_funAll djc_arg fun v_jc c_jc hv_jc => ?_
      obtain ⟨v_ts, cts, ⟨ts, rfl, htl_eq, hts, hcts⟩, rfl, hc_jc⟩ := hv_jc
      have htl : ts.length ≤ n ^ 2 := htl_eq ▸ hl
      refine (outbJoinCut_spec hP.joinCut hP.find.step.mg hP.ni hrl htl).mono fun w_s1 c_cut hcut => ?_
      obtain ⟨s1s, rfl, hs1l, hs1g, hc_cut⟩ := hcut
      refine ⟨s1s, ts, rfl, hs1l, hs1g, htl_eq, hts, ?_⟩
      have htw : (outbSv ts).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq htl
      have hs1w : (outbSv s1s).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hs1l
      have hjc_w := wt_list2_le (encGroup rs) (outbSv ts)
      unfold outbJoinCutCost at hc_cut
      rw [← hNB] at hc_cut
      clear dres dsv4 dt dc4 dR4 drep4 dM4 dP4 dfa hmap dmf_eval djc_arg dacc d0
      clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
      omega
    refine (EvalAll.mk2_last (Det.nat 0) djc_call).mono fun w cw hw => ?_
    obtain ⟨w_s1, cs1, ⟨s1s, ts, rfl, hs1l, hs1g, htl_eq, hts, hcs1⟩, rfl, hcw⟩ := hw
    have hss_eq : gens ss ⊓ gens es = gens ms := hmg_eq.symm
    obtain ⟨hRS1, hS1S, hS1_sup, hcard_step⟩ :=
      outb_corr_step hRE hRS hsyl.1 (rfl : gens rs = gens rs) hsup
        (fun t ht => by
          obtain ⟨s, hs_mem, g, hg, rfl, hn⟩ := outb_forall₂_mem_right hts t ht
          exact ⟨hn, g, hss_eq ▸ hg, s, hs_mem, rfl⟩)
        (fun s hs_mem => by
          obtain ⟨t, ht, g, hg, rfl, -⟩ := outb_forall₂_mem_left hts s hs_mem
          exact ⟨g * s, ht, g, hss_eq ▸ hg, rfl⟩)
        (hss_eq ▸ hnn)
    rw [← hs1g] at hRS1 hS1S hS1_sup hcard_step
    refine ⟨⟨s1s, hs1l, hRS1, hS1S.trans hSK, hS1_sup, Or.inr ⟨rfl, ?_⟩⟩, ?_⟩
    · calc 2 ^ (i + 1) * Nat.card (gens s1s ⊓ gens es : Subgroup _)
          = 2 ^ i * (2 * Nat.card (gens s1s ⊓ gens es : Subgroup _)) := by ring
        _ ≤ 2 ^ i * Nat.card (gens ss ⊓ gens es : Subgroup _) := Nat.mul_le_mul_left _ hcard_step
        _ ≤ Nat.card (gens es) := hcard
    · have hs1w : (outbSv s1s).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hs1l
      have := wt_list2_le (.nat 0) (outbSv s1s)
      clear dres dsv4 dt dc4 dR4 drep4 dM4 dP4 dfa hmap dmf_eval djc_arg djc_call dacc d0
      clear_value a c xs C Z2 Z9 acc0 NB FC Fx env3 env4
      omega

end GI.Impl
