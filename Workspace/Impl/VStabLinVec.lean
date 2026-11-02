import Workspace.Lang.Lib.List
import Workspace.Lang.Lib.NatList
import Workspace.Lang.Lib.Tabulate

/-!
# Linear combinations of vectors over `𝔽_p`

A vector over `𝔽_p` is a list of numbers below `p` (`natList v`). The basic operation is the
entrywise linear combination `vsLin p a b v u = (a v + b u) mod p`. With `a = 1` and
`b = p - c` it subtracts `c u` from `v`; with `a = 0` it scales `u` by `b`.

* `vsLinFuns`: the program, on `[p, a, b, natList v, natList u]` (eight functions).
* `vsLin_spec`: it computes `natList (vsLin p a b v u)` at cost at most `10^6 (N + 1)^3`,
  when `p, a, b`, the length of `v` and every entry are at most `N`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The entrywise combination `(a v + b u) mod p`, of the length of `v`. -/
def vsLin (p a b : ℕ) (v u : List ℕ) : List ℕ :=
  (List.range v.length).map fun i => (a * v.getD i 0 + b * u.getD i 0) % p

theorem vsLin_length (p a b : ℕ) (v u : List ℕ) : (vsLin p a b v u).length = v.length := by
  simp [vsLin]

theorem vsLin_getD (p a b : ℕ) (v u : List ℕ) {i : ℕ} (hi : i < v.length) :
    (vsLin p a b v u).getD i 0 = (a * v.getD i 0 + b * u.getD i 0) % p := by
  simp [vsLin, List.getD_eq_getElem?_getD, hi]

theorem vsLin_lt {p a b : ℕ} (hp : 0 < p) (v u : List ℕ) : ∀ x ∈ vsLin p a b v u, x < p := by
  intro x hx
  simp only [vsLin, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Nat.mod_lt _ hp

/-- Entry `i` of the combination, on `[[p, a, b, natList v, natList u], i]`. -/
def vsLinEntryF : Expr :=
  .arith .mod
    (.arith .add
      (.arith .mul (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 3)) (arg 1)))
      (.arith .mul (.get (arg 0) (.nat 2)) (.get (.get (arg 0) (.nat 4)) (arg 1))))
    (.get (arg 0) (.nat 0))

/-- On `[p, a, b, natList v, natList u]`: map the entry over `range (length v)`. -/
def vsLinF (rng mp : ℕ) : Expr :=
  .letE (.call rng (.length (arg 3))) (.call mp (mk2 (.var 0) (.var 1)))

/-- The eight functions of the combination, at base `b`. -/
def vsLinFuns (b : ℕ) : List Expr :=
  [vsLinF (b + 2) (b + 5), vsLinEntryF] ++ rangeFuns (b + 2) ++ mapFuns (b + 5) (b + 1)

theorem vsLinFuns_length (b : ℕ) : (vsLinFuns b).length = 8 := rfl

/-- The argument of the combination. -/
abbrev vsLinArg (p a b : ℕ) (v u : List ℕ) : Val :=
  .list [.nat p, .nat a, .nat b, natList v, natList u]

theorem natList_getElem? {v : List ℕ} {i : ℕ} (hi : i < v.length) :
    (v.map Val.nat)[i]? = some (.nat (v.getD i 0)) := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem vsLinEntry_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsLinEntryF)
    {p a b N : ℕ} {v u : List ℕ} (hv : ∀ x ∈ v, x ≤ N) (hu : ∀ x ∈ u, x ≤ N)
    (hpN : p ≤ N) (haN : a ≤ N) (hbN : b ≤ N) {i : ℕ} (hi : i < v.length) (hiu : i < u.length) :
    FunDet P f (.list [vsLinArg p a b v u, .nat i])
      (.nat ((a * v.getD i 0 + b * u.getD i 0) % p))
      (100 * (vsLinArg p a b v u).wt + 20 * (N + 1) ^ 2 + 100 * i + 300) := by
  set A := vsLinArg p a b v u with hA
  set E := [Val.list [A, .nat i]]
  have hAw : A.wt < (Val.list [A, .nat i]).wt := wt_le_wt_list (by simp)
  have hiw : (Val.nat i).wt < (Val.list [A, .nat i]).wt := wt_le_wt_list (by simp)
  have h2 := wt_list2_le A (.nat i)
  have dA := Det.arg' (P := P) (rest := []) (vs := [A, .nat i]) (j := 0) rfl
  have dI := Det.arg' (P := P) (rest := []) (vs := [A, .nat i]) (j := 1) rfl
  have dp := Det.get' dA (Det.nat 0) (show [Val.nat p, .nat a, .nat b, natList v,
    natList u][0]? = some (.nat p) from rfl)
  have da := Det.get' dA (Det.nat 1) (show [Val.nat p, .nat a, .nat b, natList v,
    natList u][1]? = some (.nat a) from rfl)
  have db := Det.get' dA (Det.nat 2) (show [Val.nat p, .nat a, .nat b, natList v,
    natList u][2]? = some (.nat b) from rfl)
  have dv := Det.get' dA (Det.nat 3) (show [Val.nat p, .nat a, .nat b, natList v,
    natList u][3]? = some (natList v) from rfl)
  have du := Det.get' dA (Det.nat 4) (show [Val.nat p, .nat a, .nat b, natList v,
    natList u][4]? = some (natList u) from rfl)
  have dvi := Det.get' dv dI (natList_getElem? hi)
  have dui := Det.get' du dI (natList_getElem? hiu)
  have m1 := Det.arith' (op := .mul) da dvi rfl
  have m2 := Det.arith' (op := .mul) db dui rfl
  have s := Det.arith' (op := .add) m1 m2 rfl
  have r := Det.arith' (op := .mod) s dp rfl
  refine FunDet.intro hf (r.mono ?_)
  have hvi : v.getD i 0 ≤ N := hv _ (by simp [List.getD_eq_getElem?_getD, hi])
  have hui : u.getD i 0 ≤ N := hu _ (by simp [List.getD_eq_getElem?_getD, hiu])
  have hpA : (Val.nat p).wt < A.wt := wt_le_wt_list (by simp [hA])
  have haA : (Val.nat a).wt < A.wt := wt_le_wt_list (by simp [hA])
  have hbA : (Val.nat b).wt < A.wt := wt_le_wt_list (by simp [hA])
  have hvA : (natList v).wt < A.wt := wt_le_wt_list (by simp [hA])
  have huA : (natList u).wt < A.wt := wt_le_wt_list (by simp [hA])
  have w1 := wt_nat_le (v.getD i 0)
  have w2 := wt_nat_le (u.getD i 0)
  have w3 := wt_nat_le i
  have e1 : a * v.getD i 0 ≤ (N + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have e2 : b * u.getD i 0 ≤ (N + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have e3 : (a * v.getD i 0 + b * u.getD i 0) % p ≤ a * v.getD i 0 + b * u.getD i 0 :=
    Nat.mod_le _ _
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [BinOp.eval] at e3 ⊢
  omega

theorem wt_vsLinArg_le {p a b N : ℕ} {v u : List ℕ} (hv : ∀ x ∈ v, x ≤ N) (hu : ∀ x ∈ u, x ≤ N)
    (hlv : v.length ≤ N) (hlu : u.length ≤ N) (hpN : p ≤ N) (haN : a ≤ N) (hbN : b ≤ N) :
    (vsLinArg p a b v u).wt ≤ 50 * (N + 1) ^ 2 := by
  show (Val.list [Val.nat p, .nat a, .nat b, natList v, natList u]).wt ≤ _
  have h1 := wt_natList_le_sq hv hlv
  have h2 := wt_natList_le_sq hu hlu
  have h3 := wt_list_le [Val.nat p, .nat a, .nat b, natList v, natList u]
  have w1 := wt_nat_le p
  have w2 := wt_nat_le a
  have w3 := wt_nat_le b
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h3
  omega

/-- **The combination.** On `[p, a, b, natList v, natList u]` with `0 < p`, every number at most
`N` and `v` not longer than `u`, the result is `natList (vsLin p a b v u)`. -/
theorem vsLin_spec {P : Program} {bs : ℕ} (h : P.HasAt bs (vsLinFuns bs))
    {p a b N : ℕ} {v u : List ℕ} (hp : 0 < p) (hv : ∀ x ∈ v, x ≤ N) (hu : ∀ x ∈ u, x ≤ N)
    (hlv : v.length ≤ N) (hlu : u.length ≤ N) (hvu : v.length ≤ u.length)
    (hpN : p ≤ N) (haN : a ≤ N) (hbN : b ≤ N) :
    FunDet P bs (vsLinArg p a b v u) (natList (vsLin p a b v u)) (10 ^ 6 * (N + 1) ^ 3) := by
  have hf0 : P.funs[bs]? = some (vsLinF (bs + 2) (bs + 5)) := h.get (j := 0) (by simp [vsLinFuns])
  have hf1 : P.funs[bs + 1]? = some vsLinEntryF := h.get (j := 1) (by simp [vsLinFuns])
  have hr : P.HasAt (bs + 2) (rangeFuns (bs + 2)) := h.block 2 rfl
  have hm : P.HasAt (bs + 5) (mapFuns (bs + 5) (bs + 1)) := h.block 5 rfl
  set A := vsLinArg p a b v u with hA
  have hAw : A.wt ≤ 50 * (N + 1) ^ 2 := wt_vsLinArg_le hv hu hlv hlu hpN haN hbN
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3' : (N + 1) * (N + 1) ^ 2 = (N + 1) ^ 3 := by ring
  -- the range
  have dlen := Det.length (P := P) (env := [A]) (Det.arg' (rest := []) (vs := [Val.nat p, .nat a,
    .nat b, natList v, natList u]) (j := 3) rfl)
  have hrng : FunDet P (bs + 2) (.nat v.length) (natList (List.range v.length))
      (loopModK * (v.length + 1) * ((Val.nat v.length).wt + v.length +
        (natList (List.range v.length)).wt + 1)) :=
    (range_spec hr v.length).mono fun w c hw => ⟨hw.1, hw.1 ▸ hw.2⟩
  have dr := Det.call (by simpa [natList] using dlen) hrng
  -- the map
  have hentry : ∀ x ∈ (List.range v.length).map Val.nat,
      FunAll P (bs + 1) (.list [A, x]) (fun w cost =>
        (fun x w => ∃ i, x = Val.nat i ∧ w = .nat ((a * v.getD i 0 + b * u.getD i 0) % p)) x w ∧
        cost ≤ 100 * A.wt + 20 * (N + 1) ^ 2 + 100 * N + 300) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact FunAll.mono (vsLinEntry_spec hf1 hv hu hpN haN hbN hi (by omega)) fun w c hw =>
      ⟨⟨i, rfl, hw.1⟩, by have := hw.2; have e : (vsLinArg p a b v u).wt = A.wt := rfl; omega⟩
  have hmap := map_spec hm hentry
  set L := List.range v.length
  have dm : FunDet P (bs + 5) (.list [A, natList L]) (natList (vsLin p a b v u))
      (L.length * (100 * A.wt + 20 * (N + 1) ^ 2 + 100 * N + 300) +
        mapK * (L.length + 1) * ((Val.list [A, natList L]).wt +
          (natList (vsLin p a b v u)).wt + 1)) := by
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hR, hc⟩ := hw
    have hws : ws = L.map fun i => Val.nat ((a * v.getD i 0 + b * u.getD i 0) % p) :=
      forall₂_map_eq (fun i _ w hw => by
        obtain ⟨j, hj, rfl⟩ := hw; cases hj; rfl) hR
    have hval : Val.list ws = natList (vsLin p a b v u) := by
      rw [hws]; simp [natList, vsLin, L, List.map_map, Function.comp_def]
    refine ⟨hval, ?_⟩
    rw [← hval]
    simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    exact hc
  have dA0 := Det.var' (P := P) (env := [A, natList L]) (i := 0) rfl
  have dL1 := Det.var' (P := P) (env := [A, natList L]) (i := 1) rfl
  have dmc := Det.call (Det.mk2 dA0 dL1) dm
  refine FunDet.intro hf0 ((Det.letE dr dmc).mono ?_)
  -- the cost
  have hLlen : L.length = v.length := List.length_range
  have hLw : (natList L).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by simp [L] at hx; omega) (by simp [L]; omega)
  have hWw : (natList (vsLin p a b v u)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (vsLin_lt hp v u x hx).le.trans hpN)
      (by rw [vsLin_length]; omega)
  have hl2 := wt_list2_le A (natList L)
  have wn := wt_nat_le v.length
  have hvl : (natList v).wt < A.wt := wt_le_wt_list (by simp [hA])
  rw [hLlen] at dm ⊢
  have k1 : v.length * (100 * A.wt + 20 * (N + 1) ^ 2 + 100 * N + 300) ≤
      N * (5500 * (N + 1) ^ 2) := Nat.mul_le_mul hlv (by omega)
  have k2 : mapK * (v.length + 1) * ((Val.list [A, natList L]).wt +
      (natList (vsLin p a b v u)).wt + 1) ≤ 1000 * (N + 1) * (120 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have k3 : loopModK * (v.length + 1) * ((Val.nat v.length).wt + v.length +
      (natList L).wt + 1) ≤ 1000 * (N + 1) * (20 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have e1 : N * (5500 * (N + 1) ^ 2) ≤ 5500 * (N + 1) ^ 3 := by
    rw [← hN3']; nlinarith
  have e2 : 1000 * (N + 1) * (120 * (N + 1) ^ 2) = 120000 * (N + 1) ^ 3 := by rw [← hN3']; ring
  have e3 : 1000 * (N + 1) * (20 * (N + 1) ^ 2) = 20000 * (N + 1) ^ 3 := by rw [← hN3']; ring
  have eY : (Val.list [Val.nat p, Val.nat a, Val.nat b, Val.list (List.map Val.nat v),
    Val.list (List.map Val.nat u)]).wt = A.wt := rfl
  have eL : (List.range v.length).length = v.length := List.length_range
  simp only [L] at *
  norm_num
  omega

end GI.Impl
