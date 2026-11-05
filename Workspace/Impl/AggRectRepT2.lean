module

public import Workspace.Impl.AggRectRepT1
public import Workspace.Impl.AggTupProg

@[expose] public section

/-!
# Stage 2 of the representation program

`rcR_st2_spec`: from the input `A` and the stage 1 value, stage 2 reads the two labels `d₁, d₂`
of the small list (first and last entry), computes the orbit of the base tuple
`(x, d₁, d₂)` under the graph pairs (`graphTup_spec`) and keeps its keys (the orbit table), finds
the first two points `w₀, w₁` of `W`, lists the generators of the side stabilizer `P`
(`rcRGenL`), and records two bits: whether the small list has one entry, and whether `d₁, d₂`
have the same orbit label.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts gens)
open Equiv

/-! ### Small facts -/

/-- A list of values made of a value and the values of a budget. -/
theorem rcR_mk2C {P : Program} {env : List Val} {W : ℕ} {a b : Expr} {va : Val} {ca Cb C : ℕ}
    {Qb : Val → Prop} (ha : rcRDW P env a va W ca) (hb : CpEB P env b W Cb Qb)
    (hw : ∀ vb, Qb vb → vb.wt ≤ W → (Val.list [va, vb]).wt ≤ W)
    (h : ca + Cb + 2 * W + 7 ≤ C) :
    CpEB P env (mk2 a b) W C (fun v => ∃ vb, Qb vb ∧ v = .list [va, vb]) := by
  refine (EvalAll.mk2_last ha.1 hb).mono ?_
  rintro v c ⟨vb, cb, ⟨h1, h2, h3⟩, rfl, h4⟩
  have := hw vb h1 h2
  exact ⟨⟨vb, h1, rfl⟩, this, by omega⟩

/-- The first entry of a list value. -/
def rcRFstV : Val → Val
  | .list (a :: _) => a
  | _ => .nat 0

theorem rcR_fsts_eq {n : ℕ} (Lt : List (List (Fin n) × Perm (Fin n))) :
    (Lt.map (GI.Lang.encPair ptsKey)).map rcRFstV = (Lt.map fun p => ptsKey p.1).map natList := by
  simp only [List.map_map]; rfl

theorem rcR_length_ncard {α : Type*} [DecidableEq α] {l : List α} {s : Set α} (hnd : l.Nodup)
    (hmem : ∀ y, y ∈ l ↔ y ∈ s) : l.length = s.ncard := by
  have : s = (l.toFinset : Set α) := by
    ext y; simp [hmem]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem rcR_M3 {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M) : k * q * q ≤ (M + 1) ^ 3 := by
  have h : k * q * q ≤ (M + 1) * (M + 1) * (M + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have e : (M + 1) * (M + 1) * (M + 1) = (M + 1) ^ 3 := by ring
  omega

theorem rcR_2M {M : ℕ} : (2 * M + 1) ^ 2 ≤ 4 * (M + 1) ^ 2 := by
  have h := rcR_pow_mono (show 2 * M + 1 ≤ 2 * (M + 1) by omega) 2
  have e : (2 * (M + 1)) ^ 2 = 4 * (M + 1) ^ 2 := by ring
  omega

/-- One entry of the tuple orbit is small. -/
theorem rcR_wt_tupE {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M) (y : List (Fin (k + q)))
    (hy : y.length = 3) (g : Perm (Fin (k + q))) :
    (GI.Lang.encPair ptsKey (y, g)).wt ≤ 100 * (M + 1) ^ 2 := by
  have h1 := wt_ptsKey_le y
  have h2 := wt_encPerm_le g
  have h3 := wt_list2_le (natList (ptsKey y)) (encPerm g)
  have h4 : (k + q + 1) ^ 2 ≤ (2 * M + 1) ^ 2 := rcR_pow_mono (by omega) 2
  have h5 := rcR_2M (M := M)
  have h6 : M + 1 ≤ (M + 1) ^ 2 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
  rw [hy] at h1
  show (Val.list [natList (ptsKey y), encPerm g]).wt ≤ _
  omega

/-- **The tuple orbit is small.** -/
theorem rcR_wt_tup {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M)
    (Lt : List (List (Fin (k + q)) × Perm (Fin (k + q)))) (hl : Lt.length ≤ k * q * q)
    (hy : ∀ p ∈ Lt, p.1.length = 3) :
    (encPairs ptsKey Lt).wt ≤ 300 * (M + 1) ^ 5 := by
  have h1 := wt_list_le_of (Lt.map (GI.Lang.encPair ptsKey)) (c := 100 * (M + 1) ^ 2) (by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
    exact rcR_wt_tupE hk hq p.1 (hy p hp) p.2)
  rw [List.length_map] at h1
  have h2 := rcR_M3 hk hq
  have h3 : Lt.length * (2 * (100 * (M + 1) ^ 2) + 1) ≤ (M + 1) ^ 3 * (201 * (M + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have h4 : (M + 1) ^ 3 * (201 * (M + 1) ^ 2) = 201 * (M + 1) ^ 5 := by ring
  have h5 : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  show (Val.list (Lt.map (GI.Lang.encPair ptsKey))).wt ≤ _
  omega

/-- **The keys of the tuple orbit are small.** -/
theorem rcR_wt_keys {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M)
    (Lt : List (List (Fin (k + q)) × Perm (Fin (k + q)))) (hl : Lt.length ≤ k * q * q)
    (hy : ∀ p ∈ Lt, p.1.length = 3) :
    (Val.list ((Lt.map fun p => ptsKey p.1).map natList)).wt ≤ 300 * (M + 1) ^ 5 := by
  have h1 := wt_list_le_of ((Lt.map fun p => ptsKey p.1).map natList) (c := 100 * (M + 1) ^ 2) (by
    intro v hv
    obtain ⟨y, hy', rfl⟩ := List.mem_map.1 hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy'
    have h := wt_ptsKey_le p.1
    rw [hy p hp] at h
    have h6 : M + 1 ≤ (M + 1) ^ 2 := by
      calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
        _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
    omega)
  rw [List.length_map, List.length_map] at h1
  have h2 := rcR_M3 hk hq
  have h3 : Lt.length * (2 * (100 * (M + 1) ^ 2) + 1) ≤ (M + 1) ^ 3 * (201 * (M + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have h4 : (M + 1) ^ 3 * (201 * (M + 1) ^ 2) = 201 * (M + 1) ^ 5 := by ring
  have h5 : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The entries of a generator list are at most `B`. -/
theorem rcR_genL_le {wl rl : List ℕ} {w₀ w₁ q t B : ℕ} (h0 : w₀ ≤ B) (h1 : w₁ ≤ B) (hq : q ≤ B)
    (ht : t < q * q) : ∀ y ∈ rcRGenL wl rl w₀ w₁ q t, y ≤ B := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hj' := List.mem_range.1 hj
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at ht
    · exact h
  have ha : t / q < q := Nat.div_lt_of_lt_mul ht
  have hb : t % q < q := Nat.mod_lt _ hq0
  unfold rcRGrN
  split_ifs
  · omega
  · rcases rcR_swN_mem w₀ w₁ (rcRSwN (t / q) (t % q) j) with h | h | h <;> rw [h]
    · exact h0
    · exact h1
    · rcases rcR_swN_mem (t / q) (t % q) j with h' | h' | h' <;> rw [h'] <;> omega

/-- **The generator lists are small.** -/
theorem rcR_wt_gens {wl rl : List ℕ} {w₀ w₁ q M : ℕ} (h0 : w₀ ≤ M) (h1 : w₁ ≤ M) (hq : q ≤ M) :
    (Val.list ((List.range (q * q)).map fun t => natList (rcRGenL wl rl w₀ w₁ q t))).wt ≤
      100 * (M + 1) ^ 4 := by
  have hM2 : (M + 1) ^ 2 ≤ (M + 1) ^ 4 := rcR_pow_le_pow (by omega) (by norm_num)
  have he : ∀ t ∈ List.range (q * q),
      (natList (rcRGenL wl rl w₀ w₁ q t)).wt ≤ 5 * (M + 1) ^ 2 := fun t ht =>
    wt_natList_le_sq (rcR_genL_le h0 h1 hq (List.mem_range.1 ht))
      (by unfold rcRGenL; rw [List.length_map, List.length_range]; exact hq)
  have h := wt_list_le_of ((List.range (q * q)).map fun t => natList (rcRGenL wl rl w₀ w₁ q t))
    (c := 5 * (M + 1) ^ 2) (by
      intro v hv
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact he t ht)
  rw [List.length_map, List.length_range] at h
  have h2 : q * q * (2 * (5 * (M + 1) ^ 2) + 1) ≤ (M + 1) ^ 2 * (11 * (M + 1) ^ 2) := by
    have h3 : q * q ≤ (M + 1) ^ 2 := by
      have := Nat.mul_le_mul (show q ≤ M + 1 by omega) (show q ≤ M + 1 by omega)
      rw [← pow_two, ← pow_two] at this; exact (le_of_eq (pow_two q).symm).trans this
    have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul h3 (by omega)
  have h4 : (M + 1) ^ 2 * (11 * (M + 1) ^ 2) = 11 * (M + 1) ^ 4 := by ring
  have : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ### Stage 2 -/

theorem rcR_lin_le {W K d : ℕ} (hK : K ≤ W + 1) (hd : 2 ≤ d) : K * (W + 1) ≤ (W + 1) ^ d := by
  have h1 : K * (W + 1) ≤ (W + 1) * (W + 1) := Nat.mul_le_mul_right _ hK
  have h2 : (W + 1) * (W + 1) = (W + 1) ^ 2 := (pow_two _).symm
  have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ d := rcR_pow_le_pow (by omega) hd
  omega

/-- The generator lists of `P`, as stage 2 lists them. -/
def rcRGenLs (wl rl : List ℕ) (w₀ w₁ q : ℕ) : List (List ℕ) :=
  (List.range (q * q)).map (rcRGenL wl rl w₀ w₁ q)

/-- The value of stage 2. -/
def rcRSt2Val (d₁ d₂ : ℕ) (ts gl : List (List ℕ)) (car uno : Bool) (k : ℕ) : Val :=
  .list [.nat d₁, .nat d₂, rcTV ts, rcTV gl, .nat car.toNat, .nat uno.toNat,
    natList (List.range k)]

/-- The first point of `W`. -/
def rcRW0 (wl : List ℕ) : ℕ := wl.findIdx fun y => decide (y = 1)

/-- The second point of `W`. -/
def rcRW1 (wl : List ℕ) (q : ℕ) : ℕ :=
  (List.range q).findIdx fun j => wl.getD j 0 == 1 && !(j == rcRW0 wl)

section St2

variable {P : Program} {I : RcRIdx}

/-- **The keys of the tuple orbit.** -/
theorem rcR_mFst_spec (ok : RcROk P I) {n : ℕ} (Lt : List (List (Fin n) × Perm (Fin n))) {W : ℕ}
    (hin : (Val.list [.nat 0, encPairs ptsKey Lt]).wt ≤ W)
    (hout : (rcTV (Lt.map fun p => ptsKey p.1)).wt ≤ W) :
    FunDet P I.mFst (.list [.nat 0, encPairs ptsKey Lt]) (rcTV (Lt.map fun p => ptsKey p.1))
      (3100 * (W + 1) ^ 3) := by
  have h := rcR_mapW1 ok.mFst (c := .nat 0) (xs := Lt.map (GI.Lang.encPair ptsKey)) (g := rcRFstV)
    (K := 10) (W := W) (fun v hv => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
      exact rcR_g0_spec ok.g0 (.nat 0) (natList (ptsKey p.1)) [encPerm p.2])
    hin (by rw [rcR_fsts_eq]; exact hout)
  rw [rcR_fsts_eq] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **Stage 2.** -/
theorem rcR_st2_spec (ok : RcROk P I) {k q x : ℕ} (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (wl rl labs sm : List ℕ) (hwl : wl.length = q) (hwl1 : ∀ y ∈ wl, y ≤ 1)
    (hlab : ∀ y ∈ labs, y < q) (hlabl : labs.length = q) (hsm : ∀ y ∈ sm, y < q)
    (hsml : sm.length ≤ q) (x₀ : List (Fin (k + q)))
    (hx₀ : ptsKey x₀ = [x, k + sm.getD 0 0, k + sm.getD (sm.length - 1) 0])
    (hB : (actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀).ncard
      ≤ k * q * q) {M W : ℕ}
    (hA : (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt ≤ M)
    (hk : k ≤ M) (hq : q ≤ M) (hx : x ≤ M) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ W) :
    CpFB P I.st2 (.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
        .list [.nat x, natList labs, natList (List.range q), natList sm]]) W
      (10 ^ 11 * (W + 1) ^ 12)
      (fun w => ∃ Lt : List (List (Fin (k + q)) × Perm (Fin (k + q))),
        w = rcRSt2Val (sm.getD 0 0) (sm.getD (sm.length - 1) 0) (Lt.map fun p => ptsKey p.1)
          (rcRGenLs wl rl (rcRW0 wl) (rcRW1 wl q) q) (sm.length == 1)
          (labs.getD (sm.getD 0 0) 0 == labs.getD (sm.getD (sm.length - 1) 0) 0) k ∧
        (∀ y, y ∈ Lt.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀) ∧
        Lt.length ≤ k * q * q) := by
  obtain ⟨Av, hAv⟩ : ∃ Av : Val,
      Av = .list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl] := ⟨_, rfl⟩
  obtain ⟨Rv, hRv⟩ : ∃ Rv : Val,
      Rv = .list [.nat x, natList labs, natList (List.range q), natList sm] := ⟨_, rfl⟩
  rw [← hAv] at hA ⊢
  rw [← hRv]
  -- powers
  have hp1 : M + 1 ≤ (M + 1) ^ 2 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp2 : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp3 : (M + 1) ^ 3 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp4 : (M + 1) ^ 4 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp5 : (M + 1) ^ 5 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU : W + 1 ≤ (W + 1) ^ 12 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 12 := rcR_pow_le_pow (by omega) (by norm_num)
  have hL12 : 10 ^ 6 * (W + 1) ≤ (W + 1) ^ 12 := rcR_lin_le (by
    have : 1 ≤ (M + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega) (by norm_num)
  have hU3 : (W + 1) ^ 3 ≤ (W + 1) ^ 12 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU5 : (W + 1) ^ 5 ≤ (W + 1) ^ 12 := rcR_pow_le_pow (by omega) (by norm_num)
  -- weights of the input
  have wsv : (Val.list svs).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wqv : (Val.nat q).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wpv : (Val.list (ps.map pairV)).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wwl : (natList wl).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wrl : (natList rl).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv0)
  have wlab : (natList labs).wt ≤ 5 * (M + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := hlab y hy; omega) (by omega)
  have wsm : (natList sm).wt ≤ 5 * (M + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := hsm y hy; omega) (by omega)
  have wrq := rcR_wt_range q M hq
  have wxv := wt_nat_le x
  have wR := wt_list4_le (.nat x) (natList labs) (natList (List.range q)) (natList sm)
  rw [← hRv] at wR
  have wIn := wt_list2_le Av Rv
  have hInW : (Val.list [Av, Rv]).wt ≤ W := by omega
  have hAW : Av.wt ≤ W := by omega
  have hRW : Rv.wt ≤ W := by omega
  -- reading the input
  have dA : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (arg 0)
      (.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]) W (2 * W + 5) :=
    fun rest => (rcRDW.arg (vs := [Av, Rv]) (rest := rest) (j := 0) (v := Av) hInW rfl).cast hAv
  have dR : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (arg 1)
      (.list [.nat x, natList labs, natList (List.range q), natList sm]) W (2 * W + 6) :=
    fun rest => (rcRDW.arg (vs := [Av, Rv]) (rest := rest) (j := 1) (v := Rv) hInW rfl).cast hRv
  have dk : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.nat k) W (4 * W + 13) := fun rest =>
    ((rcRDW.get (rcRDW.get (dA rest) (j := 0) (v := .list svs) rfl) hsv0)).mono (by omega)
  have dq : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 0) (.nat 1)) (.nat q) W
      (3 * W + 10) := fun rest => (rcRDW.get (dA rest) (j := 1) (v := .nat q) rfl).mono (by omega)
  have dsm : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 1) (.nat 3)) (natList sm) W
      (3 * W + 13) := fun rest =>
    (rcRDW.get (dR rest) (j := 3) (v := natList sm) rfl).mono (by omega)
  -- `d₁` and `d₂`
  obtain ⟨d₁, hd₁⟩ : ∃ d, d = sm.getD 0 0 := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d, d = sm.getD (sm.length - 1) 0 := ⟨_, rfl⟩
  rw [← hd₁, ← hd₂] at hx₀ ⊢
  have hsm0 : ∀ i, sm.getD i 0 < q ∨ sm.getD i 0 = 0 := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : sm[i]? with
    | none => right; rfl
    | some y => left; exact hsm y (List.mem_of_getElem? h)
  have hd₁q : d₁ ≤ M := by rcases hsm0 0 with h | h <;> omega
  have hd₂q : d₂ ≤ M := by rcases hsm0 (sm.length - 1) with h | h <;> omega
  have w0v := wt_nat_le 0
  have w1v := wt_nat_le 1
  have dd1 := (rcRDW.gdN (env := [.list [Av, Rv]]) I ok.gD (dsm []) (rcRDW.nat 0 (by omega))
    (rcRDW.nat 0 (by omega))).cast (show Val.nat (sm.getD 0 0) = .nat d₁ by rw [hd₁])
  refine CpFB.intro ok.st2 (rcR_letC (Cb := (2 * 10 ^ 10 + 10 ^ 7 + 3) * (W + 1) ^ 12)
    (rcR_detC dd1 (C := (W + 1) ^ 12) (by omega) (Q := (· = .nat d₁)) rfl) ?_ (by omega))
  rintro _ rfl -
  have dlen := (rcRDW.length (dsm [.nat d₁])).cast
    (show Val.nat (sm.map Val.nat).length = .nat sm.length by rw [List.length_map])
  have wsl := wt_nat_le sm.length
  have dsub := rcRDW.arith (op := .sub) (z := sm.length - 1) dlen (rcRDW.nat 1 (by omega))
    (by simp [BinOp.eval]) (by have := wt_nat_le (sm.length - 1); omega)
  have dd2 := (rcRDW.gdN I ok.gD (dsm [.nat d₁]) dsub (rcRDW.nat 0 (by omega))).cast
    (show Val.nat (sm.getD (sm.length - 1) 0) = .nat d₂ by rw [hd₂])
  refine rcR_letC (Cb := (2 * 10 ^ 10 + 10 ^ 7 + 1) * (W + 1) ^ 12)
    (rcR_detC dd2 (C := (W + 1) ^ 12) (by omega) (Q := (· = .nat d₂)) rfl) ?_ (by omega)
  rintro _ rfl -
  -- the orbit of the base tuple
  have hx₀l : x₀.length = 3 := by
    have := congrArg List.length hx₀
    simpa [ptsKey] using this
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkd1 := wt_nat_le (k + d₁)
  have wkd2 := wt_nat_le (k + d₂)
  have wkq := wt_nat_le (k * q)
  have hkq1 : k * q ≤ (M + 1) ^ 2 := by
    have := Nat.mul_le_mul (show k ≤ M + 1 by omega) (show q ≤ M + 1 by omega)
    rw [← pow_two] at this; exact this
  have hkqq := rcR_M3 hk hq
  have wkqq := wt_nat_le (k * q * q)
  have e0 : List.length (List.map Val.nat []) = 0 := rfl
  let rest : List Val := [.nat d₁, .nat d₂]
  have dkq := rcRDW.mk2 (dk rest) (dq rest) (by have := wt_list2_le (.nat k) (.nat q); omega)
  have dps := rcRDW.get (dA rest) (j := 2) (v := .list (ps.map pairV)) rfl
  have dxx := rcRDW.get (dR rest) (j := 0) (v := .nat x) rfl
  have dk1 := rcRDW.arith (op := .add) (z := k + d₁) (dk rest)
    (rcRDW.var (env := .list [Av, Rv] :: rest) (i := 1) (v := .nat d₁) rfl (by
      have := wt_nat_le d₁; omega)) rfl (by omega)
  have dk2 := rcRDW.arith (op := .add) (z := k + d₂) (dk rest)
    (rcRDW.var (env := .list [Av, Rv] :: rest) (i := 2) (v := .nat d₂) rfl (by
      have := wt_nat_le d₂; omega)) rfl (by omega)
  have dtr := rcRDW.mk3 dxx dk1 dk2 (by
    have := wt_list3_le (.nat x) (.nat (k + d₁)) (.nat (k + d₂)); omega)
  have dB := rcRDW.arith (op := .mul) (z := k * q * q)
    (rcRDW.arith (op := .mul) (z := k * q) (dk rest) (dq rest) rfl (by omega)) (dq rest) rfl
    (by omega)
  have wTI := wt_list4_le (.list [.nat k, .nat q]) (.list (ps.map pairV))
    (.list [.nat x, .nat (k + d₁), .nat (k + d₂)]) (.nat (k * q * q))
  have wtr := wt_list3_le (.nat x) (.nat (k + d₁)) (.nat (k + d₂))
  have wk2 := wt_list2_le (.nat k) (.nat q)
  have dTI := rcRDW.mk4 dkq dps dtr dB (by omega)
  have hT := graphTup_spec ok.tup ps x₀ hB
  rw [hx₀] at hT
  have hTB : CpFB P I.tup (.list [.list [.nat k, .nat q], .list (ps.map pairV),
      .list [.nat x, .nat (k + d₁), .nat (k + d₂)], .nat (k * q * q)]) W (10 ^ 10 * (W + 1) ^ 12)
      (fun w => ∃ Lt : List (List (Fin (k + q)) × Perm (Fin (k + q))), w = encPairs ptsKey Lt ∧
        (∀ y, y ∈ Lt.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀) ∧
        Lt.length ≤ k * q * q ∧ ∀ p ∈ Lt, p.1.length = 3) := by
    refine FunAll.mono hT ?_
    rintro w c ⟨Lt, rfl, hnd, hmem, htr, hc⟩
    have hLl : Lt.length ≤ k * q * q := by
      have := rcR_length_ncard hnd hmem
      rw [List.length_map] at this; omega
    have hy : ∀ p ∈ Lt, p.1.length = 3 := fun p hp => by
      rw [← (htr p hp).2, List.length_map, hx₀l]
    refine ⟨⟨Lt, rfl, hmem, hLl, hy⟩, by have := rcR_wt_tup hk hq Lt hLl hy; omega, ?_⟩
    have hM : tupM k q ps (k * q * q) x₀.length ≤ W + 1 := by
      unfold tupM
      have := length_lt_wt_list (ps.map pairV)
      rw [List.length_map] at this
      rw [hx₀l]
      omega
    have h12 := Nat.mul_le_mul_left graphTupK (rcR_pow_mono hM 12)
    have hK : graphTupK = 10 ^ 10 := rfl
    rw [hK] at h12 hc
    omega
  have hTI := rcR_detC dTI (C := (W + 1) ^ 12) (by omega)
    (Q := (· = .list [.list [.nat k, .nat q], .list (ps.map pairV),
      .list [.nat x, .nat (k + d₁), .nat (k + d₂)], .nat (k * q * q)])) rfl
  have hwLt : ∀ Lt : List (List (Fin (k + q)) × Perm (Fin (k + q))), Lt.length ≤ k * q * q →
      (∀ p ∈ Lt, p.1.length = 3) → (Val.list [.nat 0, encPairs ptsKey Lt]).wt ≤ W ∧
        (rcTV (Lt.map fun p => ptsKey p.1)).wt ≤ W := fun Lt hl hy => by
    have h1 := rcR_wt_tup hk hq Lt hl hy
    have h2 := rcR_wt_keys hk hq Lt hl hy
    have h3 := wt_list2_le (.nat 0) (encPairs ptsKey Lt)
    exact ⟨by omega, by unfold rcTV; omega⟩
  refine rcR_letC (Cb := 10 ^ 7 * (W + 1) ^ 12)
    (rcR_callC (Ca := (10 ^ 10 + 4) * (W + 1) ^ 12) (Cb := 10 ^ 5 * (W + 1) ^ 12)
      (C := 2 * 10 ^ 10 * (W + 1) ^ 12)
      (Q := fun w => ∃ Lt : List (List (Fin (k + q)) × Perm (Fin (k + q))),
        w = rcTV (Lt.map fun p => ptsKey p.1) ∧
        (∀ y, y ∈ Lt.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair) x₀) ∧
        Lt.length ≤ k * q * q ∧ ∀ p ∈ Lt, p.1.length = 3)
      (rcR_mk2C (rcRDW.nat 0 (by omega))
        (rcR_callC (C := (10 ^ 10 + 2) * (W + 1) ^ 12) hTI (fun v hv _ => by subst hv; exact hTB)
          (by omega))
        (fun vb hvb _ => by
          obtain ⟨Lt, rfl, -, hl, hy⟩ := hvb
          exact (hwLt Lt hl hy).1) (by omega))
      (fun v hv _ => by
        obtain ⟨vb, ⟨Lt, rfl, hmem, hl, hy⟩, rfl⟩ := hv
        exact CpFB.det (rcR_mFst_spec ok Lt (hwLt Lt hl hy).1 (hwLt Lt hl hy).2) (by omega)
          (hwLt Lt hl hy).2 ⟨Lt, rfl, hmem, hl, hy⟩) (by omega)) ?_ (by omega)
  rintro _ ⟨Lt, rfl, hmem, hl, hy⟩ -
  obtain ⟨ts, hts⟩ : ∃ ts, ts = Lt.map fun p => ptsKey p.1 := ⟨_, rfl⟩
  rw [← hts]
  have wts : (rcTV ts).wt ≤ 300 * (M + 1) ^ 5 := by
    rw [hts]; unfold rcTV; exact rcR_wt_keys hk hq Lt hl hy
  have hM5 : 5 ≤ M := by
    have := length_lt_wt_list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]
    rw [← hAv] at this; simp only [List.length_cons, List.length_nil] at this; omega
  -- `w₀`
  let r2 : List Val := [.nat d₁, .nat d₂, rcTV ts]
  have dwl : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 0) (.nat 3)) (natList wl) W
      (3 * W + 12) := fun rest =>
    (rcRDW.get (dA rest) (j := 3) (v := natList wl) rfl).mono (by omega)
  have drl : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 0) (.nat 4)) (natList rl) W
      (3 * W + 13) := fun rest =>
    (rcRDW.get (dA rest) (j := 4) (v := natList rl) rfl).mono (by omega)
  have drq : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 1) (.nat 2))
      (natList (List.range q)) W (3 * W + 12) := fun rest =>
    (rcRDW.get (dR rest) (j := 2) (v := natList (List.range q)) rfl).mono (by omega)
  have hfe := findEq_spec ok.fEq (xs := wl) (j := 1) (B := M) (fun y hy => by
    have := hwl1 y hy; omega) (by omega) (by omega)
  have hfe : FunDet P I.fEq (.list [.nat 1, natList wl]) (.nat (rcRW0 wl))
      (findEqK * (M + 1) ^ 3) := hfe
  have hw0 : rcRW0 wl ≤ M := by
    have : rcRW0 wl ≤ wl.length := List.findIdx_le_length
    omega
  have ww0 := wt_nat_le (rcRW0 wl)
  have w1l := wt_list2_le (.nat 1) (natList wl)
  have dw0 := rcRDW.call (rcRDW.mk2 (rcRDW.nat (env := .list [Av, Rv] :: r2) 1 (by omega))
    (dwl r2) (by omega)) hfe (by omega)
  -- `w₁`
  let r3 : List Val := [.nat d₁, .nat d₂, rcTV ts, .nat (rcRW0 wl)]
  have hw1 : rcRW1 wl q ≤ M := by
    have : rcRW1 wl q ≤ (List.range q).length := List.findIdx_le_length
    rw [List.length_range] at this; omega
  have ww1 := wt_nat_le (rcRW1 wl q)
  have wc1 := wt_list2_le (natList wl) (.nat (rcRW0 wl))
  have wc2 := wt_list2_le (.list [natList wl, .nat (rcRW0 wl)]) (natList (List.range q))
  have hfw := rcR_findN1 ok.fW1 (c := .list [natList wl, .nat (rcRW0 wl)]) (xs := List.range q)
    (t := fun j => wl.getD j 0 == 1 && !(j == rcRW0 wl)) (K := 5000) (W := W)
    (fun j _ => rcR_w1P_spec ok.gD ok.w1P wl (rcRW0 wl) j) (by omega)
  have hfw : FunDet P I.fW1 (.list [.list [natList wl, .nat (rcRW0 wl)], natList (List.range q)])
      (.nat (rcRW1 wl q)) ((10 * 5000 + 3000) * (W + 1) ^ 3) := hfw
  have dw1 := rcRDW.call (rcRDW.mk2 (rcRDW.mk2 (dwl r3)
    (rcRDW.var (env := .list [Av, Rv] :: r3) (i := 4) (v := .nat (rcRW0 wl)) rfl (by omega))
    (by omega)) (drq r3) (by omega)) hfw (by omega)
  -- the generators
  let r4 : List Val := [.nat d₁, .nat d₂, rcTV ts, .nat (rcRW0 wl), .nat (rcRW1 wl q)]
  have wqq := wt_nat_le (q * q)
  have hqq : q * q ≤ (M + 1) ^ 2 :=
    calc q * q ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (M + 1) ^ 2 := (pow_two _).symm
  have wrqq : (natList (List.range (q * q))).wt ≤ 20 * (M + 1) ^ 4 := by
    have h := wt_natList_le_sq (xs := List.range (q * q)) (B := (M + 1) ^ 2) (fun y hy => by
      rw [List.mem_range] at hy; omega) (by rw [List.length_range]; exact hqq)
    have h2 := rcR_pow_mono (show (M + 1) ^ 2 + 1 ≤ 2 * (M + 1) ^ 2 by
      have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega) 2
    have h3 : (2 * (M + 1) ^ 2) ^ 2 = 4 * (M + 1) ^ 4 := by ring
    omega
  obtain ⟨CV, hCV⟩ : ∃ CV : Val, CV = .list [natList wl, natList rl, .nat (rcRW0 wl),
      .nat (rcRW1 wl q), .nat q, natList (List.range q)] := ⟨_, rfl⟩
  have wCV : CV.wt ≤ 100 * (M + 1) ^ 2 := by
    have := wt_list_le_of [natList wl, natList rl, .nat (rcRW0 wl), .nat (rcRW1 wl q), .nat q,
      natList (List.range q)] (c := 5 * (M + 1) ^ 2) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    rw [hCV]; simp only [List.length_cons, List.length_nil] at this; omega
  have dCV := (rcRDW.mkList (env := .list [Av, Rv] :: r4) (c := 3 * W + 13)
    [(.get (arg 0) (.nat 3), natList wl), (.get (arg 0) (.nat 4), natList rl),
      (.var 4, .nat (rcRW0 wl)), (.var 5, .nat (rcRW1 wl q)), (.get (arg 0) (.nat 1), .nat q),
      (.get (arg 1) (.nat 2), natList (List.range q))] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact (dwl r4).mono (by omega)
      · exact drl r4
      · exact (rcRDW.var (i := 4) (v := .nat (rcRW0 wl)) rfl (by omega)).mono (by omega)
      · exact (rcRDW.var (i := 5) (v := .nat (rcRW1 wl q)) rfl (by omega)).mono (by omega)
      · exact (dq r4).mono (by omega)
      · exact (drq r4).mono (by omega)) (by
        show (Val.list [natList wl, natList rl, .nat (rcRW0 wl), .nat (rcRW1 wl q), .nat q,
          natList (List.range q)]).wt ≤ W
        rw [← hCV]; omega)).cast hCV.symm
  have hrng : ∀ n : ℕ, FunDet P I.rng (.nat n) (natList (List.range n))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) := fun n =>
    (range_spec ok.rng n).mono fun w c ⟨hw, hc⟩ => ⟨hw, by rw [hw] at hc; exact hc⟩
  have hK : loopModK = 1000 := rfl
  have drng := rcRDW.call (rcRDW.arith (op := .mul) (z := q * q) (dq r4) (dq r4) rfl (by omega))
    (hrng (q * q)) (by omega)
  obtain ⟨gl, hgl⟩ : ∃ gl, gl = rcRGenLs wl rl (rcRW0 wl) (rcRW1 wl q) q := ⟨_, rfl⟩
  have wgl : (rcTV gl).wt ≤ 100 * (M + 1) ^ 4 := by
    have := rcR_wt_gens (wl := wl) (rl := rl) hw0 hw1 hq
    rw [hgl]; unfold rcTV rcRGenLs; rw [List.map_map]; exact this
  have egl : (List.range (q * q)).map (fun t => natList (rcRGenL wl rl (rcRW0 wl) (rcRW1 wl q) q t))
      = gl.map natList := by
    rw [hgl]; unfold rcRGenLs; rw [List.map_map]; rfl
  have wCt := wt_list2_le CV (natList (List.range (q * q)))
  have hmap := rcR_mapN ok.mGen (c := CV) (xs := List.range (q * q))
    (g := fun t => natList (rcRGenL wl rl (rcRW0 wl) (rcRW1 wl q) q t)) (K := 5000) (d := 3) (W := W)
    (fun t ht => by
      have wt1 := wt_nat_le t
      have ht' := List.mem_range.1 ht
      have wct := wt_list2_le CV (.nat t)
      have wCV' := wCV
      rw [hCV] at wct wCV' ⊢
      refine rcR_genF_spec ok.gD ok.genF ok.mGR ok.grF wl rl (rcRW0 wl) (rcRW1 wl q) q t ?_ ?_
      · omega
      · have := wt_natList_le_sq (rcR_genL_le (wl := wl) (rl := rl) hw0 hw1 hq ht')
          (by unfold rcRGenL; rw [List.length_map, List.length_range]; exact hq)
        omega)
    (by omega) (by rw [egl]; unfold rcTV at wgl; omega)
  rw [egl] at hmap
  have dgen := rcRDW.call (rcRDW.mk2 dCV drng (by omega)) hmap (by unfold rcTV at wgl; omega)
  have dgen' := dgen.cast (show Val.list (gl.map natList) = rcTV gl from rfl)
  -- the output
  let r5 : List Val := [.nat d₁, .nat d₂, rcTV ts, .nat (rcRW0 wl), .nat (rcRW1 wl q), rcTV gl]
  have hW2 : 2000 * (W + 1) ≤ (W + 1) ^ 2 := rcR_lin_le (by
    have : 1 ≤ (M + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega) le_rfl
  have hU2 : (W + 1) ^ 2 ≤ (W + 1) ^ 12 := rcR_pow_le_pow (by omega) (by norm_num)
  have wd1 := wt_nat_le d₁
  have wd2 := wt_nat_le d₂
  have wrk := rcR_wt_range k M hk
  have dlabs := (rcRDW.get (dR r5) (j := 1) (v := natList labs) rfl)
  have wlg1 : (Val.nat (labs.getD d₁ 0)).wt ≤ W := by
    have := wt_nat_le (labs.getD d₁ 0)
    have := rcR_getD_le (l := labs) (B := q) (fun y hy => (hlab y hy).le) d₁
    omega
  have wlg2 : (Val.nat (labs.getD d₂ 0)).wt ≤ W := by
    have := wt_nat_le (labs.getD d₂ 0)
    have := rcR_getD_le (l := labs) (B := q) (fun y hy => (hlab y hy).le) d₂
    omega
  have dl1 := rcRDW.gdN I ok.gD dlabs (rcRDW.var (i := 1) (v := .nat d₁) rfl (by omega))
    (rcRDW.nat 0 (by omega))
  have dl2 := rcRDW.gdN I ok.gD dlabs (rcRDW.var (i := 2) (v := .nat d₂) rfl (by omega))
    (rcRDW.nat 0 (by omega))
  have duno := rcRDW.arith (op := .eq)
    (z := (labs.getD d₁ 0 == labs.getD d₂ 0).toNat) dl1 dl2 (rcR_eqT _ _)
    (rcR_wt_toNat _ (by omega))
  have dlen5 := (rcRDW.length (dsm r5)).cast
    (show Val.nat (sm.map Val.nat).length = .nat sm.length by rw [List.length_map])
  have dcar := rcRDW.arith (op := .eq) (z := (sm.length == 1).toNat) dlen5
    (rcRDW.nat 1 (by omega)) (rcR_eqT _ _) (rcR_wt_toNat _ (by omega))
  have hkr : loopModK * (k + 1) * ((Val.nat k).wt + k + (natList (List.range k)).wt + 1) ≤
      1000 * (W + 1) ^ 2 := by
    rw [hK, Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (k + 1) * ((Val.nat k).wt + k + (natList (List.range k)).wt + 1) ≤ (W + 1) * (W + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = (W + 1) ^ 2 := (pow_two _).symm
  have drk := rcRDW.call (dk r5) (hrng k) (by omega)
  have wsml := wt_nat_le sm.length
  have dout := rcRDW.mkList (P := P) (W := W) (env := .list [Av, Rv] :: r5) (c := 2000 * (W + 1) ^ 2)
    [(.var 1, .nat d₁), (.var 2, .nat d₂), (.var 3, rcTV ts), (.var 6, rcTV gl),
      (rcREq (.length (.get (arg 1) (.nat 3))) (.nat 1), .nat (sm.length == 1).toNat),
      (rcREq (I.gd (.get (arg 1) (.nat 1)) (.var 1) (.nat 0))
        (I.gd (.get (arg 1) (.nat 1)) (.var 2) (.nat 0)),
        .nat (labs.getD d₁ 0 == labs.getD d₂ 0).toNat),
      (.call I.rng (.get (.get (arg 0) (.nat 0)) (.nat 0)), natList (List.range k))] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact (rcRDW.var (i := 1) (v := .nat d₁) rfl (by omega)).mono (by omega)
      · exact (rcRDW.var (i := 2) (v := .nat d₂) rfl (by omega)).mono (by omega)
      · exact (rcRDW.var (i := 3) (v := rcTV ts) rfl (by omega)).mono (by omega)
      · exact (rcRDW.var (i := 6) (v := rcTV gl) rfl (by omega)).mono (by omega)
      · exact dcar.mono (by omega)
      · exact duno.mono (by omega)
      · exact drk.mono (by omega)) (by
      show (rcRSt2Val d₁ d₂ ts gl (sm.length == 1) (labs.getD d₁ 0 == labs.getD d₂ 0) k).wt ≤ W
      have := wt_list_le_of [.nat d₁, .nat d₂, rcTV ts, rcTV gl, .nat (sm.length == 1).toNat,
        .nat (labs.getD d₁ 0 == labs.getD d₂ 0).toNat, natList (List.range k)]
        (c := 300 * (M + 1) ^ 5) (by
        have := rcR_wt_toNat (sm.length == 1) (W := 3) le_rfl
        have := rcR_wt_toNat (labs.getD d₁ 0 == labs.getD d₂ 0) (W := 3) le_rfl
        have : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
        have : (M + 1) ^ 2 ≤ (M + 1) ^ 5 := rcR_pow_le_pow (by omega) (by norm_num)
        have : (M + 1) ^ 4 ≤ (M + 1) ^ 5 := rcR_pow_le_pow (by omega) (by norm_num)
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
      unfold rcRSt2Val
      simp only [List.length_cons, List.length_nil] at this
      omega)
  have dall := rcRDW.letE dw0 (rcRDW.letE dw1 (rcRDW.letE dgen' dout))
  refine rcR_detC dall ?_ ⟨Lt, by rw [hgl, hts]; rfl, hmem, hl⟩
  -- the cost
  have hM3 : (M + 1) ^ 3 ≤ (W + 1) ^ 3 := rcR_pow_mono (by omega) 3
  have hKe : findEqK = 10 ^ 5 := rfl
  have hqr : loopModK * (q * q + 1) * ((Val.nat (q * q)).wt + q * q +
      (natList (List.range (q * q))).wt + 1) ≤ 1000 * (W + 1) ^ 2 := by
    rw [hK, Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (q * q + 1) * ((Val.nat (q * q)).wt + q * q + (natList (List.range (q * q))).wt + 1)
          ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (W + 1) ^ 2 := (pow_two _).symm
  have h35 : (W + 1) ^ (3 + 2) = (W + 1) ^ 5 := rfl
  have hfc : findEqK * (M + 1) ^ 3 ≤ 10 ^ 5 * (W + 1) ^ 3 := by
    rw [hKe]; exact Nat.mul_le_mul_left _ hM3
  simp only [List.length_cons, List.length_nil]
  omega

end St2

end GI.Impl
