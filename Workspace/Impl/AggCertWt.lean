module

public import Workspace.Impl.AggCertPhase

@[expose] public section

/-!
# The weight of the program states of the certificate phase

The relation `CpRep` asks that every program state weighs at most a bound `Bw`, and the cost of
a move is bounded in terms of `Bw`. This file gives `Bw` as a polynomial: the weight of a
program state is at most `cpBw` (`cp_wt_state`), from the length bounds `CpLen`, `CpInLen` and
the bounds on the numbers of test sets (`NT`) and cache entries (`M₀`).

The size parameter is `w = k + q + 1`; a graph form weighs `O(w⁴)`, a cache entry
`O((D + 1) w⁶)` and the data inside a round `O((D + 1) w⁶)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

variable {k q : ℕ}

/-- A list of `n` values of weight at most `c` each. -/
theorem cp_wt_list {vs : List Val} {n c : ℕ} (hl : vs.length ≤ n) (h : ∀ v ∈ vs, v.wt ≤ c) :
    (Val.list vs).wt ≤ n * (2 * c + 1) + 4 :=
  (wt_list_le_of vs h).trans (by have := Nat.mul_le_mul_right (2 * c + 1) hl; omega)

theorem cp_pow_facts (k q : ℕ) :
    1 ≤ (k + q + 1) ^ 2 ∧ (k + q) ^ 2 ≤ (k + q + 1) ^ 2 ∧ (k + 1) ^ 2 ≤ (k + q + 1) ^ 2 ∧
      (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 4 ∧ (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 6 ∧
      (k + q + 1) ^ 2 * (k + q + 1) ^ 2 = (k + q + 1) ^ 4 ∧
      (k + q + 1) ^ 4 * (k + q + 1) ^ 2 = (k + q + 1) ^ 6 ∧
      k ^ 2 ≤ (k + q + 1) ^ 2 ∧ k + q + 1 ≤ (k + q + 1) ^ 2 ∧ (k + 1) ^ 6 ≤ (k + q + 1) ^ 6 := by
  refine ⟨Nat.one_le_pow _ _ (by omega), Nat.pow_le_pow_left (by omega) 2,
    Nat.pow_le_pow_left (by omega) 2, Nat.pow_le_pow_right (by omega) (by omega),
    Nat.pow_le_pow_right (by omega) (by omega), by ring, by ring, Nat.pow_le_pow_left (by omega) 2,
    Nat.le_self_pow (by omega) _, Nat.pow_le_pow_left (by omega) 6⟩

/-- A graph form with at most `(k + q)²` pairs. -/
theorem cp_wt_gp {ps : GPairs k q} (h : ps.length ≤ (k + q) ^ 2) :
    (gpV ps).wt ≤ 50 * (k + q + 1) ^ 4 := by
  obtain ⟨h1, h2, -, -, -, e4, -⟩ := cp_pow_facts k q
  have := cp_wt_list (vs := ps.map pairV) (n := (k + q + 1) ^ 2) (c := 22 * (k + q + 1) ^ 2)
    (by simp only [List.length_map]; omega) (by
      simp only [List.mem_map]; rintro _ ⟨p, -, rfl⟩; exact wt_pairV_le p)
  have : (k + q + 1) ^ 2 * (2 * (22 * (k + q + 1) ^ 2) + 1) ≤ (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have : (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) = 45 * (k + q + 1) ^ 4 := by rw [← e4]; ring
  have : 1 ≤ (k + q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold gpV
  omega

theorem cp_wt_res {r : GPairs k q × GPairs k q} (h1 : r.1.length ≤ (k + q) ^ 2)
    (h2 : r.2.length ≤ (k + q) ^ 2) : (resV r).wt ≤ 210 * (k + q + 1) ^ 4 := by
  have a := cp_wt_gp h1
  have b := cp_wt_gp h2
  have := wt_list2_le (gpV r.1) (gpV r.2)
  have : 1 ≤ (k + q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold resV
  omega

/-- The group value of an encoded graph form. -/
theorem cp_wt_encGroupPairs {ps : GPairs k q} (h : ps.length ≤ (k + q) ^ 2) :
    (encGroup (ps.map encPair)).wt ≤ 360 * (k + q + 1) ^ 6 := by
  obtain ⟨h1, h2, -, -, -, e4, e6, -⟩ := cp_pow_facts k q
  have := wt_encGroup_le (ps.map encPair)
  simp only [List.length_map] at this
  have a : (ps.length + 2) * (k + q + 1) ≤ 3 * (k + q + 1) ^ 2 * (k + q + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have b := Nat.pow_le_pow_left a 2
  have : (3 * (k + q + 1) ^ 2 * (k + q + 1)) ^ 2 = 9 * (k + q + 1) ^ 6 := by ring
  omega

/-- A list of `n` permutations of `Fin k`. -/
theorem cp_wt_perms {as : List (Perm (Fin k))} {n : ℕ} (h : as.length ≤ n) :
    (Val.list (as.map encPerm)).wt ≤ 9 * n * (k + q + 1) ^ 2 + 4 := by
  obtain ⟨h1, -, h3, -⟩ := cp_pow_facts k q
  have := cp_wt_list (vs := as.map encPerm) (n := n) (c := 4 * (k + q + 1) ^ 2)
    (by simp only [List.length_map]; omega) (by
      simp only [List.mem_map]; rintro _ ⟨p, -, rfl⟩
      have := wt_encPerm_le p; omega)
  have : n * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ n * (9 * (k + q + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have : n * (9 * (k + q + 1) ^ 2) = 9 * n * (k + q + 1) ^ 2 := by ring
  omega

/-- A cache entry. -/
theorem cp_wt_ent {D : ℕ} {ent : CacheEntry k q} (h1 : ent.1.length ≤ (k + q) ^ 2)
    (h2 : ent.2.1.length ≤ (k + q) ^ 2) (h3 : ent.2.2.length ≤ D) :
    (ckEntV ent).wt ≤ 2000 * (D + 1) * (k + q + 1) ^ 6 := by
  obtain ⟨-, -, -, -, f46, -, -, -, -, -⟩ := cp_pow_facts k q
  have a := cp_wt_encGroupPairs h1
  have b := cp_wt_encGroupPairs h2
  have c := cp_wt_perms (q := q) h3
  have := wt_list3_le (encGroup (ent.1.map encPair)) (encGroup (ent.2.1.map encPair))
    (.list (ent.2.2.map encPerm))
  have : 9 * D * (k + q + 1) ^ 2 ≤ 9 * D * (k + q + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have : (D + 1) * (k + q + 1) ^ 6 = D * (k + q + 1) ^ 6 + (k + q + 1) ^ 6 := by ring
  have : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold ckEntV
  nlinarith

/-- A test set. -/
theorem cp_wt_ts (T : Finset (Fin q)) : (tsV k T).wt ≤ 50 * (k + q + 1) ^ 2 := by
  obtain ⟨h1, -, -, -, -, -, -, -, h9, -⟩ := cp_pow_facts k q
  have a : (indT T).wt ≤ q * (2 * 1 + 5) + 4 := wt_encFun_le _ fun i => by split_ifs <;> omega
  have hl : (tlist T).length ≤ q := by
    unfold tlist; rw [Finset.length_sort]; exact (Finset.card_le_univ T).trans (by simp)
  have b : (natList (ptsKey (labPts k (tlist T)))).wt ≤
      (ptsKey (labPts k (tlist T))).length * (2 * (k + q) + 5) + 4 :=
    wt_natList_le fun x hx => by
      simp only [ptsKey, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx; omega
  simp only [ptsKey, labPts, List.length_map] at b
  have c : (tlist T).length * (2 * (k + q) + 5) ≤ q * (2 * (k + q) + 5) :=
    Nat.mul_le_mul_right _ hl
  have d : q * (2 * (k + q) + 5) ≤ (k + q + 1) * (5 * (k + q + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (k + q + 1) * (5 * (k + q + 1)) = 5 * (k + q + 1) ^ 2 := by ring
  have := wt_list2_le (indT T) (natList (ptsKey (labPts k (tlist T))))
  unfold tsV
  simp only [ptsKey, labPts] at this ⊢
  omega

/-- At most `k` points of `Fin (k + q)`. -/
theorem cp_wt_pts {X : List (Fin (k + q))} (h : X.length ≤ k) :
    (encPts X).wt ≤ 10 * (k + q + 1) ^ 2 := by
  obtain ⟨h1, -, -, -, -, -, -, -, h9, -⟩ := cp_pow_facts k q
  have := wt_encPts_le X
  have : 3 * X.length * (k + q + 2) ≤ 3 * ((k + q + 1) * (k + q + 1)) + 3 * (k + q + 1) :=
    by nlinarith
  have : (k + q + 1) * (k + q + 1) = (k + q + 1) ^ 2 := by ring
  omega

/-- The data inside a round. -/
theorem cp_wt_inner {D : ℕ} {inner : Val} (h : CpInLen k q D inner) :
    inner.wt ≤ 10 ^ 4 * (D + 1) * (k + q + 1) ^ 6 := by
  obtain ⟨as, gs, hs, f, incP, a, rfl, hg, hh, hf, hi⟩ := h
  obtain ⟨h1, -, h3, h24, h46, e4, e6, hk2, -, hk6⟩ := cp_pow_facts k q
  have hgl : gs.length ≤ D * (k + q + 1) ^ 2 := by
    have : D * (k ^ 2 + 1) ≤ D * (k + q + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have : as.length * (k ^ 2 + 1) + (k ^ 2 + 1) = (as.length + 1) * (k ^ 2 + 1) := by ring
    omega
  have hal : as.length ≤ D := by
    have : (as.length + 1) * 1 ≤ (as.length + 1) * (k ^ 2 + 1) := Nat.mul_le_mul_left _ (by omega)
    have : D * (k ^ 2 + 1) ≤ D * (k ^ 2 + 1) := le_rfl
    by_contra hc
    have : D * (k ^ 2 + 1) < (as.length + 1) * (k ^ 2 + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have wa := cp_wt_perms (q := q) hal
  have wg := cp_wt_perms (q := q) hgl
  have wh : (encGroup hs).wt ≤ 320 * (k + 1) ^ 6 := wt_encGroup_le_sq hh
  have wf : (encFun f).wt ≤ k * (2 * 1 + 5) + 4 := wt_encFun_le f hf
  have wi := cp_wt_pts hi
  have wp : (encPerm a).wt ≤ 4 * (k + 1) ^ 2 := wt_encPerm_le a
  have := wt_list_le [.list (as.map encPerm), .list (gs.map encPerm), encGroup hs, encFun f,
    encPts incP, encPerm a]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have m1 : 9 * (D * (k + q + 1) ^ 2) * (k + q + 1) ^ 2 = 9 * D * (k + q + 1) ^ 4 := by
    rw [← e4]; ring
  have m2 : 9 * D * (k + q + 1) ^ 4 ≤ 9 * D * (k + q + 1) ^ 6 := Nat.mul_le_mul_left _ h46
  have m3 : 9 * D * (k + q + 1) ^ 2 ≤ 9 * D * (k + q + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (h24.trans h46)
  have m4 : (D + 1) * (k + q + 1) ^ 6 = D * (k + q + 1) ^ 6 + (k + q + 1) ^ 6 := by ring
  have m5 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold cpInnerV
  nlinarith

/-- A canonical answer. -/
theorem cp_wt_ans {Ω : Type} {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) :
    u.wt ≤ 1000 * (k + 1) ^ 6 := by
  have h1 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hl, -⟩
  · simp only [wt_list_nil]; omega
  · have a := wt_encPerm_le x
    have b : (encGroup gs).wt ≤ 320 * (k + 1) ^ 6 := wt_encGroup_le_sq hl
    have c := wt_list2_le (encPerm x) (encGroup gs)
    have : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- One stage of a log. -/
theorem cp_wt_sg {d : CpStgD k q} (h : CpSgLen d) : (cpSgV d).wt ≤ 130 * (k + q + 1) ^ 4 := by
  have := cp_wt_gp h.1
  have := cp_wt_pts (q := q) h.2
  have := wt_list2_le (gpV d.1) (encPts d.2)
  obtain ⟨h1, -, -, h24, -⟩ := cp_pow_facts k q
  unfold cpSgV
  omega

/-- A stage log of at most `k` stages. -/
theorem cp_wt_lg {l : List (CpStgD k q)} (h : CpLgLen l) :
    (Val.list (l.map cpSgV)).wt ≤ 300 * (k + q + 1) ^ 6 := by
  have h1 := cp_wt_list (vs := l.map cpSgV) (n := k) (c := 130 * (k + q + 1) ^ 4)
    (by simpa using h.1) (by simp only [List.mem_map]; rintro _ ⟨d, hd, rfl⟩; exact cp_wt_sg (h.2 d hd))
  obtain ⟨-, -, -, -, f46, -, e6, -, f9, -⟩ := cp_pow_facts k q
  have a : k * (2 * (130 * (k + q + 1) ^ 4) + 1) ≤ (k + q + 1) * (261 * (k + q + 1) ^ 4) :=
    Nat.mul_le_mul (by omega) (by have : 1 ≤ (k + q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega); omega)
  have b : (k + q + 1) * (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 6 := by
    have : (k + q + 1) * (k + q + 1) ^ 4 = (k + q + 1) ^ 5 := by ring
    rw [this]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have : (k + q + 1) * (261 * (k + q + 1) ^ 4) = 261 * ((k + q + 1) * (k + q + 1) ^ 4) := by ring
  have : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The log of a test set. -/
theorem cp_wt_log {l : Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q)}
    (h1 : CpLgLen l.2.1) (h2 : CpLgLen l.2.2) : (cpLogV l).wt ≤ 1400 * (k + q + 1) ^ 6 := by
  have := cp_wt_lg h1
  have := cp_wt_lg h2
  have := cp_wt_ts (k := k) l.1
  have := wt_list3_le (tsV k l.1) (.list (l.2.1.map cpSgV)) (.list (l.2.2.map cpSgV))
  obtain ⟨h1, -, -, h24, h46, -⟩ := cp_pow_facts k q
  unfold cpLogV
  omega

/-- The logs of at most `NT` test sets. -/
theorem cp_wt_logs {NT : ℕ} {ls : List (Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q))}
    (hl : ls.length ≤ NT) (h : ∀ l ∈ ls, CpLgLen l.2.1 ∧ CpLgLen l.2.2) :
    (Val.list (ls.map cpLogV)).wt ≤ NT * (2801 * (k + q + 1) ^ 6) + 4 := by
  have := cp_wt_list (vs := ls.map cpLogV) (n := NT) (c := 1400 * (k + q + 1) ^ 6)
    (by simpa using hl) (by
      simp only [List.mem_map]; rintro _ ⟨l, hl', rfl⟩; exact cp_wt_log (h l hl').1 (h l hl').2)
  have e : 2 * (1400 * (k + q + 1) ^ 6) + 1 ≤ 2801 * (k + q + 1) ^ 6 := by
    have : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have := Nat.mul_le_mul_left NT e
  omega

/-- **The weight bound of the program states.** -/
def cpBw (k q P NT M₀ D : ℕ) : ℕ := 4 * P + 10 ^ 6 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6

set_option maxHeartbeats 1000000 in
/-- **The data of a program state.** -/
theorem cp_wt_kst {D NT M₀ : ℕ} {par inner : Val} {σ : CpSt k q} (hlen : CpLen D σ)
    (hlog : CpLogLen σ)
    (hTs : σ.Ts.length ≤ NT) (hres : σ.res.length ≤ NT) (hc : σ.cache.length ≤ M₀)
    (hin : inner.wt ≤ 10 ^ 4 * (D + 1) * (k + q + 1) ^ 6) :
    (σ.val par inner).wt ≤ 2 * par.wt + 10 ^ 5 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 := by
  obtain ⟨ht, hos, hp0, hpx, hps, hr, hce⟩ := hlen
  obtain ⟨h1, -, -, h24, h46, -, -, -, h9, -⟩ := cp_pow_facts k q
  have w6 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have wTs := cp_wt_list (vs := σ.Ts.map (tsV k)) (n := NT) (c := 50 * (k + q + 1) ^ 2)
    (by simpa using hTs) (by simp only [List.mem_map]; rintro _ ⟨T, -, rfl⟩; exact cp_wt_ts T)
  have wres := cp_wt_list (vs := σ.res.map resV) (n := NT) (c := 210 * (k + q + 1) ^ 4)
    (by simpa using hres) (by
      simp only [List.mem_map]; rintro _ ⟨r, hr', rfl⟩; exact cp_wt_res (hr r hr').1 (hr r hr').2)
  have wc := cp_wt_list (vs := σ.cache.map ckEntV) (n := M₀) (c := 2000 * (D + 1) * (k + q + 1) ^ 6)
    (by simpa using hc) (by
      simp only [List.mem_map]; rintro _ ⟨r, hr', rfl⟩
      exact cp_wt_ent (hce r hr').1 (hce r hr').2.1 (hce r hr').2.2)
  have w0 := cp_wt_gp hp0
  have w1 := cp_wt_gp hpx
  have w2 := cp_wt_gp hps
  have wo := cp_wt_pts hos
  have wT := cp_wt_ts (k := k) σ.T
  have wb := wt_boolVal_le σ.s
  have wt := wt_nat_le σ.t
  have wlz := cp_wt_lg hlog.lz
  have wlx := cp_wt_lg hlog.lx
  have wlogs := cp_wt_logs (NT := NT) (by rw [hlog.logs_len]; exact hres) hlog.logs
  have a8 : NT * (2801 * (k + q + 1) ^ 6) ≤ 2801 * (NT * ((D + 1) * (k + q + 1) ^ 6)) := by
    have a4 : (k + q + 1) ^ 6 ≤ (D + 1) * (k + q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    rw [show NT * (2801 * (k + q + 1) ^ 6) = 2801 * (NT * (k + q + 1) ^ 6) by ring]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a4)
  have hv : σ.val par inner = Val.list [par, .list (σ.Ts.map (tsV k)), boolVal σ.s,
    .list (σ.res.map resV), .list (σ.cache.map ckEntV), gpV σ.p0, gpV σ.px, .nat σ.t, gpV σ.ps,
    encPts σ.osP, inner, tsV k σ.T, .list (σ.lz.map cpSgV), .list (σ.lx.map cpSgV),
    .list (σ.logs.map cpLogV)] := rfl
  rw [hv]
  have := wt_list_le [par, .list (σ.Ts.map (tsV k)), boolVal σ.s, .list (σ.res.map resV),
    .list (σ.cache.map ckEntV), gpV σ.p0, gpV σ.px, .nat σ.t, gpV σ.ps, encPts σ.osP, inner,
    tsV k σ.T, .list (σ.lz.map cpSgV), .list (σ.lx.map cpSgV), .list (σ.logs.map cpLogV)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have a1 : NT * (2 * (50 * (k + q + 1) ^ 2) + 1) ≤ NT * (101 * (k + q + 1) ^ 6) :=
    Nat.mul_le_mul_left _ (by omega)
  have a2 : NT * (2 * (210 * (k + q + 1) ^ 4) + 1) ≤ NT * (421 * (k + q + 1) ^ 6) :=
    Nat.mul_le_mul_left _ (by omega)
  have a4 : (k + q + 1) ^ 6 ≤ (D + 1) * (k + q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have a3 : M₀ * (2 * (2000 * (D + 1) * (k + q + 1) ^ 6) + 1) ≤
      M₀ * (4001 * ((D + 1) * (k + q + 1) ^ 6)) := by
    refine Nat.mul_le_mul_left _ ?_
    have : 2 * (2000 * (D + 1) * (k + q + 1) ^ 6) = 4000 * ((D + 1) * (k + q + 1) ^ 6) := by ring
    omega
  have e : (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 =
      NT * ((D + 1) * (k + q + 1) ^ 6) + M₀ * ((D + 1) * (k + q + 1) ^ 6) +
        (D + 1) * (k + q + 1) ^ 6 := by ring
  have a5 : NT * (101 * (k + q + 1) ^ 6) ≤ 101 * (NT * ((D + 1) * (k + q + 1) ^ 6)) := by
    rw [show NT * (101 * (k + q + 1) ^ 6) = 101 * (NT * (k + q + 1) ^ 6) by ring]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a4)
  have a6 : NT * (421 * (k + q + 1) ^ 6) ≤ 421 * (NT * ((D + 1) * (k + q + 1) ^ 6)) := by
    rw [show NT * (421 * (k + q + 1) ^ 6) = 421 * (NT * (k + q + 1) ^ 6) by ring]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a4)
  have a7 : M₀ * (4001 * ((D + 1) * (k + q + 1) ^ 6)) = 4001 * (M₀ * ((D + 1) * (k + q + 1) ^ 6)) :=
    by ring
  have : (k + q + 1) ^ 4 ≤ (D + 1) * (k + q + 1) ^ 6 := h46.trans a4
  have : (k + q + 1) ^ 2 ≤ (D + 1) * (k + q + 1) ^ 6 := (h24.trans h46).trans a4
  have : 10 ^ 4 * (D + 1) * (k + q + 1) ^ 6 = 10 ^ 4 * ((D + 1) * (k + q + 1) ^ 6) := by ring
  have : 10 ^ 5 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 =
      10 ^ 5 * ((NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6) := by ring
  omega

/-- **The weight of a program state.** -/
theorem cp_wt_state {D NT M₀ : ℕ} {par inner u : Val} {σ : CpSt k q} (hlen : CpLen D σ)
    (hlog : CpLogLen σ) (hTs : σ.Ts.length ≤ NT) (hres : σ.res.length ≤ NT) (hc : σ.cache.length ≤ M₀)
    (hin : inner.wt ≤ 10 ^ 4 * (D + 1) * (k + q + 1) ^ 6) (hu : u.wt ≤ 1000 * (k + 1) ^ 6) :
    (Val.list [σ.val par inner, u]).wt ≤ cpBw k q par.wt NT M₀ D := by
  have h := cp_wt_kst (par := par) hlen hlog hTs hres hc hin
  have := wt_list2_le (σ.val par inner) u
  have : (k + 1) ^ 6 ≤ (k + q + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have : (k + q + 1) ^ 6 ≤ (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have : 10 ^ 5 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 =
      10 ^ 5 * ((NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6) := by ring
  have : 10 ^ 6 * (NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6 =
      10 ^ 6 * ((NT + M₀ + 1) * (D + 1) * (k + q + 1) ^ 6) := by ring
  unfold cpBw
  omega

theorem cp_wt_empty_inner {D : ℕ} : (Val.list []).wt ≤ 10 ^ 4 * (D + 1) * (k + q + 1) ^ 6 := by
  have : 1 ≤ (D + 1) * (k + q + 1) ^ 6 := Nat.one_le_iff_ne_zero.2 (by positivity)
  simp only [wt_list_nil]
  nlinarith

end GI.Impl
