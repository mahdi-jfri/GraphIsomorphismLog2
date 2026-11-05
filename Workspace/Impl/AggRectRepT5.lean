module

public import Workspace.Impl.AggRectRepT4
public import Workspace.Impl.AggKerRed

@[expose] public section

/-!
# Stage 4 of the representation program

`rcR_st4_spec`: from the Preimage output, the program keeps the first parts (`kr_spec`, with
**PointwiseStab** to shorten the list), drops the identity, reads the label part of each
generator from the orbit table (`rcRPiN`), and writes the cell of each position (`rcRCellN`).
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts encGroup gens PointwiseStab)
open Equiv

/-! ### Small facts -/

theorem rcR_getD_list_le {l : List ℕ} {B : ℕ} (h : ∀ z ∈ l, z ≤ B) (j : ℕ) : l.getD j 0 ≤ B :=
  rcR_getD_le h j

/-- The entries of a looked-up key are bounded by the entries of the table. -/
theorem rcR_look_le {Lk : List (List ℕ)} {B : ℕ} (h : ∀ y ∈ Lk, ∀ z ∈ y, z ≤ B) (i j : ℕ) :
    (rcRLook Lk i).getD j 0 ≤ B := by
  unfold rcRLook
  refine rcR_getD_le (fun z hz => ?_) j
  rw [List.getD_eq_getElem?_getD] at hz
  cases hy : Lk[Lk.findIdx fun y => y.getD 0 0 == i]? with
  | none => rw [hy] at hz; simp at hz
  | some y => rw [hy] at hz; exact h y (List.mem_of_getElem? hy) z hz

/-- **The label part is bounded** by the entries of the table. -/
theorem rcR_piN_le {Lk : List (List ℕ)} {B : ℕ} (h : ∀ y ∈ Lk, ∀ z ∈ y, z ≤ B) (k : ℕ)
    (f : ℕ → ℕ) (j : ℕ) : rcRPiN Lk k f j ≤ B := by
  unfold rcRPiN
  have h1 := rcR_look_le h (f ((rcRLook1 Lk (k + j)).getD 0 0)) 1
  have h2 := rcR_look_le h (f ((rcRLook1 Lk (k + j)).getD 0 0)) 2
  split_ifs <;> omega

theorem rcR_getD_one {l : List ℕ} {c : ℕ} (h : l.getD c 0 = 1) : c < l.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by omega)] at h
  exact absurd h (by norm_num)

/-- **The cell codes are small.** -/
theorem rcR_cellN_le {dl : List ℕ} {Lk : List (List ℕ)} {k q : ℕ} {wl rl : List ℕ}
    (hwl : wl.length = q) (hrl : rl.length = q) (car uno : Bool) (rowT : List ℕ) (i : ℕ) :
    rcRCellN dl Lk k q wl rl car uno rowT i ≤ (q + 1) ^ 2 := by
  have hsq : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
  unfold rcRCellN
  split_ifs
  · omega
  · unfold rcRCarCodeN
    split_ifs with h
    · have h1 := rcR_getD_one h.2.2
      have h2 : rowT.getD i 0 * q ≤ q * q := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
  · unfold rcRCodeN
    split_ifs with h h'
    · have h1 := rcR_getD_one h.1
      have h2 := rcR_getD_one h.2
      have h3 : ((rcRLook Lk i).getD 1 0 - k) * q ≤ q * q := Nat.mul_le_mul_right _ (by omega)
      omega
    · have h1 := rcR_getD_one h'.2.1
      have h2 := rcR_getD_one h'.2.2
      have h3 : ((rcRLook Lk i).getD 2 0 - k) * q ≤ q * q := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega

/-- An entry of the values of a budget. -/
theorem rcR_getB {P : Program} {env : List Val} {W : ℕ} {l : Expr} {Cl C : ℕ}
    {Ql Q : Val → Prop} (j : ℕ) (hl : CpEB P env l W Cl Ql)
    (hq : ∀ v, Ql v → ∃ vs w, v = .list vs ∧ vs[j]? = some w ∧ Q w)
    (h : Cl + W + j + 10 ≤ C) : CpEB P env (.get l (.nat j)) W C Q := by
  refine EvalAll.get hl (EvalAll.nat (Q := fun v c => v = .nat j ∧ c = (Val.nat j).wt + 1)
    ⟨rfl, rfl⟩) ?_
  rintro va ca vb cb ⟨h1, h2, h3⟩ ⟨rfl, rfl⟩
  obtain ⟨vs, w, rfl, hw, hQ⟩ := hq va h1
  obtain ⟨hx, hwe⟩ := List.getElem?_eq_some_iff.1 hw
  refine ⟨vs, j, rfl, rfl, hx, ?_⟩
  rw [hwe]
  have h4 : w.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hw)
  have h5 := wt_nat_le j
  exact ⟨hQ, by omega, by omega⟩

/-! ### Stage 4 -/

/-- The graph pairs the program outputs: a generator with its label part read from the table. -/
noncomputable def rcROutV (Lk : List (List ℕ)) (k q : ℕ) (h : Perm (Fin k)) : Val :=
  .list [encPerm h, natList ((List.range q).map
    (rcRPiN Lk k (fun v => (rcRL fun i => (h i : ℕ)).getD v 0)))]

section St4

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 8000000 in
/-- **Stage 4.** -/
theorem rcR_st4_spec (ok : RcROk P I) (hst : PointwiseStab)
    (hjp : P.prims[I.jp]? = some (pointwiseStabPrim hst)) {k q n : ℕ} (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (dl : List ℕ) (hsv2 : svs[2]? = some (natList dl))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (wl rl : List ℕ) (hwl : wl.length = q)
    (hrl : rl.length = q) (b0 b1 b3 c0 c1 c3 : Val) (Lk : List (List ℕ)) (car uno : Bool)
    (qs : List (Perm (Fin k) × Perm (Fin n))) (rowT : List ℕ) {M W : ℕ}
    (hLk : ∀ y ∈ Lk, ∀ z ∈ y, z ≤ 2 * M) (wLk : (rcTV Lk).wt ≤ 300 * (M + 1) ^ 5)
    (wrowT : (natList rowT).wt ≤ 5 * (M + 1) ^ 2)
    (hqs : qs.length ≤ (k + n) ^ 2) (hn : n ≤ 2 * M + 1)
    (hA : (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt ≤ M)
    (hk : k ≤ M) (hq : q ≤ M) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ W)
    (hIn : (Val.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
      .list [b0, b1, natList (List.range q), b3],
      .list [c0, c1, rcTV Lk, c3, .nat car.toNat, .nat uno.toNat, natList (List.range k)],
      .list [.list (qs.map pairV), natList rowT]]).wt ≤ W) :
    CpFB P I.st4 (.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
      .list [b0, b1, natList (List.range q), b3],
      .list [c0, c1, rcTV Lk, c3, .nat car.toNat, .nat uno.toNat, natList (List.range k)],
      .list [.list (qs.map pairV), natList rowT]]) W
      ((pointwiseStabPrim hst).boundSize W + 10 ^ 26 * (W + 1) ^ 9)
      (fun w => ∃ hs : List (Perm (Fin k)),
        w = .list [.list (hs.map (rcROutV Lk k q)),
          natList ((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT)), .list []] ∧
        gens hs = gens (qs.map Prod.fst) ∧ hs.length ≤ k ^ 2) := by
  obtain ⟨Av, hAv⟩ : ∃ Av : Val,
      Av = .list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl] := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1 : Val, R1 = .list [b0, b1, natList (List.range q), b3] := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : Val, R2 = .list [c0, c1, rcTV Lk, c3, .nat car.toNat, .nat uno.toNat,
      natList (List.range k)] := ⟨_, rfl⟩
  obtain ⟨R3, hR3⟩ : ∃ R3 : Val, R3 = .list [.list (qs.map pairV), natList rowT] := ⟨_, rfl⟩
  rw [← hAv] at hA hIn ⊢
  rw [← hR1, ← hR2, ← hR3] at hIn ⊢
  -- powers
  have hp1 : M + 1 ≤ (M + 1) ^ 2 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp2 : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp3 : (M + 1) ^ 3 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp4 : (M + 1) ^ 4 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp5 : (M + 1) ^ 5 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp6 : (M + 1) ^ 6 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp8 : (M + 1) ^ 8 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU : W + 1 ≤ (W + 1) ^ 9 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 9 := rcR_pow_le_pow (by omega) (by norm_num)
  have hL9 : 10 ^ 6 * (W + 1) ≤ (W + 1) ^ 9 := rcR_lin_le (by
    have : 1 ≤ (M + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega) (by norm_num)
  have hU2 : (W + 1) ^ 2 ≤ (W + 1) ^ 9 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU3 : (W + 1) ^ 3 ≤ (W + 1) ^ 9 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU5 : (W + 1) ^ 5 ≤ (W + 1) ^ 9 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU6 : (W + 1) ^ 6 ≤ (W + 1) ^ 9 := rcR_pow_le_pow (by omega) (by norm_num)
  have h35 : (W + 1) ^ (3 + 2) = (W + 1) ^ 5 := rfl
  -- weights of the input
  have wsv : (Val.list svs).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wqv : (Val.nat q).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wwl : (natList wl).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wrl : (natList rl).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv0)
  have wdl : (natList dl).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv2)
  have wA : Av.wt < (Val.list [Av, R1, R2, R3]).wt := wt_le_wt_list (by simp)
  have wR1 : R1.wt < (Val.list [Av, R1, R2, R3]).wt := wt_le_wt_list (by simp)
  have wR2 : R2.wt < (Val.list [Av, R1, R2, R3]).wt := wt_le_wt_list (by simp)
  have wR3 : R3.wt < (Val.list [Av, R1, R2, R3]).wt := wt_le_wt_list (by simp)
  have wqs : (Val.list (qs.map pairV)).wt < R3.wt := by rw [hR3]; exact wt_le_wt_list (by simp)
  have wrow : (natList rowT).wt < R3.wt := by rw [hR3]; exact wt_le_wt_list (by simp)
  have wrq := rcR_wt_range q M hq
  have wrk := rcR_wt_range k M hk
  have wk := wt_nat_le k
  have wcar := rcR_wt_toNat car (W := 3) le_rfl
  have wuno := rcR_wt_toNat uno (W := 3) le_rfl
  -- reading the input
  have dA : ∀ rest, rcRDW P (.list [Av, R1, R2, R3] :: rest) (arg 0)
      (.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]) W (2 * W + 5) :=
    fun rest => (rcRDW.arg (vs := [Av, R1, R2, R3]) (rest := rest) (j := 0) (v := Av) hIn
      rfl).cast hAv
  have dR1 : ∀ rest, rcRDW P (.list [Av, R1, R2, R3] :: rest) (arg 1)
      (.list [b0, b1, natList (List.range q), b3]) W (2 * W + 6) :=
    fun rest => (rcRDW.arg (vs := [Av, R1, R2, R3]) (rest := rest) (j := 1) (v := R1) hIn
      rfl).cast hR1
  have dR2 : ∀ rest, rcRDW P (.list [Av, R1, R2, R3] :: rest) (arg 2)
      (.list [c0, c1, rcTV Lk, c3, .nat car.toNat, .nat uno.toNat, natList (List.range k)]) W
      (2 * W + 7) :=
    fun rest => (rcRDW.arg (vs := [Av, R1, R2, R3]) (rest := rest) (j := 2) (v := R2) hIn
      rfl).cast hR2
  have dR3 : ∀ rest, rcRDW P (.list [Av, R1, R2, R3] :: rest) (arg 3)
      (.list [.list (qs.map pairV), natList rowT]) W (2 * W + 8) :=
    fun rest => (rcRDW.arg (vs := [Av, R1, R2, R3]) (rest := rest) (j := 3) (v := R3) hIn
      rfl).cast hR3
  have dk : ∀ rest, rcRDW P (.list [Av, R1, R2, R3] :: rest)
      (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat k) W (4 * W + 13) := fun rest =>
    (rcRDW.get (rcRDW.get (dA rest) (j := 0) (v := .list svs) rfl) hsv0).mono (by omega)
  -- the generators on positions
  have wkq := wt_list2_le (.nat k) (.list (qs.map pairV))
  have wqsB : (Val.list (qs.map pairV)).wt ≤ 204800 * (M + 1) ^ 6 := by
    have h1 := rcR_wt_qs (M := 2 * M + 1) (by omega) hn qs hqs
    have h2 := rcR_pow_mono (show 2 * M + 1 + 1 ≤ 2 * (M + 1) by omega) 6
    have h3 : (2 * (M + 1)) ^ 6 = 64 * (M + 1) ^ 6 := by ring
    omega
  have dkr := rcRDW.mk2 (dk []) (rcRDW.get (dR3 []) (j := 0) (v := .list (qs.map pairV)) rfl)
    (by omega)
  have hpM : pM k n qs ≤ 12 * (M + 1) ^ 2 := by
    unfold pM
    have h1 : (k + n) ^ 2 ≤ (3 * (M + 1)) ^ 2 := rcR_pow_mono (by omega) 2
    have h2 : (3 * (M + 1)) ^ 2 = 9 * (M + 1) ^ 2 := by ring
    omega
  have hKR : CpFB P I.kr (.list [.nat k, .list (qs.map pairV)]) W
      ((pointwiseStabPrim hst).boundSize W + 10 ^ 12 * (W + 1) ^ 9)
      (fun w => ∃ hs : List (Perm (Fin k)), w = encGroup hs ∧ gens hs = gens (qs.map Prod.fst) ∧
        hs.length ≤ k ^ 2) := by
    refine FunAll.mono (kr_spec hst ok.kr hjp qs) ?_
    rintro w c ⟨hs, rfl, hg, hl, hc⟩
    refine ⟨⟨hs, rfl, hg, hl⟩, ?_, ?_⟩
    · have := wt_encGroup_le_sq hl
      have h1 : (k + 1) ^ 6 ≤ (M + 1) ^ 6 := rcR_pow_mono (by omega) 6
      omega
    · have h1 : 100 * pM k n qs ^ 4 ≤ W := by
        have h2 := rcR_pow_mono hpM 4
        have h3 : (12 * (M + 1) ^ 2) ^ 4 = 20736 * (M + 1) ^ 8 := by ring
        have hM5 : 5 ≤ M := by
          have := length_lt_wt_list [.list svs, .nat q, .list (ps.map pairV), natList wl,
            natList rl]
          rw [← hAv] at this; simp only [List.length_cons, List.length_nil] at this; omega
        have h36 : 36 * (M + 1) ^ 8 ≤ (M + 1) ^ 10 := by
          have e : (M + 1) ^ 10 = (M + 1) ^ 2 * (M + 1) ^ 8 := by ring
          have : 36 ≤ (M + 1) ^ 2 := by
            have := rcR_pow_mono (show 6 ≤ M + 1 by omega) 2; norm_num at this; exact this
          rw [e]; exact Nat.mul_le_mul_right _ this
        omega
      have h2 := boundSize_mono (pointwiseStabPrim hst) h1
      have h3 : pM k n qs ≤ W + 1 := by omega
      have h4 := Nat.mul_le_mul_left krK (rcR_pow_mono h3 9)
      have hK : krK = 10 ^ 12 := rfl
      rw [hK] at h4 hc
      omega
  obtain ⟨F, hF⟩ : ∃ F, F = 10 ^ 25 * (W + 1) ^ 9 := ⟨_, rfl⟩
  obtain ⟨In, hIn'⟩ : ∃ In : Val, In = .list [Av, R1, R2, R3] := ⟨_, rfl⟩
  have hKRe : CpEB P [.list [Av, R1, R2, R3]] (.call I.kr (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.get (arg 3) (.nat 0)))) W ((pointwiseStabPrim hst).boundSize W + (10 ^ 12 + 1) * (W + 1) ^ 9)
      (fun w => ∃ hs : List (Perm (Fin k)), w = encGroup hs ∧ gens hs = gens (qs.map Prod.fst) ∧
        hs.length ≤ k ^ 2) :=
    rcR_callC (rcR_detC dkr (C := 20 * W + 100) (by omega)
      (Q := (· = .list [.nat k, .list (qs.map pairV)])) rfl)
      (fun v hv _ => by subst hv; exact hKR) (by omega)
  have hget : CpEB P [.list [Av, R1, R2, R3]] (.get (.call I.kr (mk2 (.get (.get (arg 0) (.nat 0))
      (.nat 0)) (.get (arg 3) (.nat 0)))) (.nat 1)) W
      ((pointwiseStabPrim hst).boundSize W + (10 ^ 12 + 2) * (W + 1) ^ 9)
      (fun w => ∃ hs : List (Perm (Fin k)), w = .list (encPerm 1 :: hs.map encPerm) ∧
        gens hs = gens (qs.map Prod.fst) ∧ hs.length ≤ k ^ 2) :=
    rcR_getB 1 hKRe (fun v hv => by
      obtain ⟨hs, rfl, hg, hl⟩ := hv
      exact ⟨[.nat k, .list ((1 :: hs).map encPerm)], _, rfl, rfl, hs, rfl, hg, hl⟩) (by omega)
  have htl : CpEB P [.list [Av, R1, R2, R3]] (.call I.tl (.get (.call I.kr
      (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (arg 3) (.nat 0)))) (.nat 1))) W
      ((pointwiseStabPrim hst).boundSize W + (10 ^ 12 + 4000) * (W + 1) ^ 9)
      (fun w => ∃ hs : List (Perm (Fin k)), w = .list (hs.map encPerm) ∧
        gens hs = gens (qs.map Prod.fst) ∧ hs.length ≤ k ^ 2) :=
    rcR_callC (Cb := 3000 * (W + 1) ^ 9) hget (fun v hv hvw => by
      obtain ⟨hs, rfl, hg, hl⟩ := hv
      have h1 : (Val.list (hs.map encPerm)).wt ≤
          (Val.list (encPerm (1 : Perm (Fin k)) :: hs.map encPerm)).wt :=
        wt_list_sublist (List.sublist_cons_self _ _)
      refine CpFB.det (GI.Lang.tail_spec ok.tl (encPerm (1 : Perm (Fin k))) (hs.map encPerm)) ?_ (by omega) ⟨hs, rfl, hg, hl⟩
      have hK : loopModK = 1000 := rfl
      have h2 : ((hs.map encPerm).length + 1) *
          (3 * (Val.list (encPerm (1 : Perm (Fin k)) :: hs.map encPerm)).wt + 1)
          ≤ 3 * ((W + 1) * (W + 1)) := by
        have := length_lt_wt_list (encPerm (1 : Perm (Fin k)) :: hs.map encPerm)
        simp only [List.length_cons] at this
        have h4 : ((hs.map encPerm).length + 1) *
            (3 * (Val.list (encPerm (1 : Perm (Fin k)) :: hs.map encPerm)).wt
            + 1) ≤ (W + 1) * (3 * (W + 1)) := Nat.mul_le_mul (by omega) (by omega)
        have h5 : (W + 1) * (3 * (W + 1)) = 3 * ((W + 1) * (W + 1)) := by ring
        omega
      have h6 : (W + 1) * (W + 1) = (W + 1) ^ 2 := (pow_two _).symm
      rw [hK, Nat.mul_assoc]
      omega) (by omega)
  refine CpFB.intro ok.st4 (rcR_letC (Cb := F) htl ?_ (by omega))
  rintro _ ⟨hs, rfl, hg, hl⟩ -
  subst hAv hR1 hR2 hR3
  -- the label parts
  let r1 : List Val := [.list (hs.map encPerm)]
  have hhs : hs.length ≤ (M + 1) ^ 2 := by
    have := rcR_pow_mono (show k ≤ M + 1 by omega) 2; omega
  have wout1 : ∀ h : Perm (Fin k), (rcROutV Lk k q h).wt ≤ 40 * (M + 1) ^ 2 := by
    intro h
    have h1 := wt_encPerm_le h
    have h2 := wt_natList_le (xs := (List.range q).map
      (rcRPiN Lk k (fun v => (rcRL fun i => (h i : ℕ)).getD v 0))) (B := 2 * M)
      (fun z hz => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
        exact rcR_piN_le hLk k _ j)
    rw [List.length_map, List.length_range] at h2
    have h3 := wt_list2_le (encPerm h) (natList ((List.range q).map
      (rcRPiN Lk k (fun v => (rcRL fun i => (h i : ℕ)).getD v 0))))
    have h4 : (k + 1) ^ 2 ≤ (M + 1) ^ 2 := rcR_pow_mono (by omega) 2
    have h5 : q * (2 * (2 * M) + 5) ≤ (M + 1) * (5 * (M + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have h6 : (M + 1) * (5 * (M + 1)) = 5 * (M + 1) ^ 2 := by ring
    unfold rcROutV
    omega
  have wout : (Val.list (hs.map (rcROutV Lk k q))).wt ≤ 100 * (M + 1) ^ 4 := by
    have h1 := wt_list_le_of (hs.map (rcROutV Lk k q)) (c := 40 * (M + 1) ^ 2) (by
      intro v hv
      obtain ⟨h, -, rfl⟩ := List.mem_map.1 hv
      exact wout1 h)
    rw [List.length_map] at h1
    have h2 : hs.length * (2 * (40 * (M + 1) ^ 2) + 1) ≤ (M + 1) ^ 2 * (81 * (M + 1) ^ 2) :=
      Nat.mul_le_mul hhs (by have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have h3 : (M + 1) ^ 2 * (81 * (M + 1) ^ 2) = 81 * (M + 1) ^ 4 := by ring
    have : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have whs : (Val.list (hs.map encPerm)).wt ≤ 100 * (M + 1) ^ 4 := by
    have h1 := wt_list_le_of (hs.map encPerm) (c := 4 * (M + 1) ^ 2) (by
      intro v hv
      obtain ⟨h, -, rfl⟩ := List.mem_map.1 hv
      have := wt_encPerm_le h
      have h4 : (k + 1) ^ 2 ≤ (M + 1) ^ 2 := rcR_pow_mono (by omega) 2
      omega)
    rw [List.length_map] at h1
    have h2 : hs.length * (2 * (4 * (M + 1) ^ 2) + 1) ≤ (M + 1) ^ 2 * (9 * (M + 1) ^ 2) :=
      Nat.mul_le_mul hhs (by have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have h3 : (M + 1) ^ 2 * (9 * (M + 1) ^ 2) = 9 * (M + 1) ^ 4 := by ring
    have : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have wc := wt_list3_le (rcTV Lk) (.nat k) (natList (List.range q))
  have wci := wt_list2_le (.list [rcTV Lk, .nat k, natList (List.range q)]) (.list (hs.map encPerm))
  have dc := rcRDW.mk2 (rcRDW.mk3 (rcRDW.get (dR2 r1) (j := 2) (v := rcTV Lk) rfl) (dk r1)
      (rcRDW.get (dR1 r1) (j := 2) (v := natList (List.range q)) rfl) (by omega))
    (rcRDW.var (env := _ :: r1) (i := 1) (v := .list (hs.map encPerm)) rfl (by omega)) (by omega)
  have hmo := mapList_spec ok.mOut hs encPerm (rcROutV Lk k q)
    (c := .list [rcTV Lk, .nat k, natList (List.range q)]) (B := 10 ^ 24 * (W + 1) ^ 5)
    (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun h hh => by
      have hw1 := rcR_wt_elem (c := .list [rcTV Lk, .nat k, natList (List.range q)])
        (ys := hs.map encPerm) (List.mem_map.2 ⟨h, hh, rfl⟩)
      have := rcR_out_spec ok.gD ok.outF ok.mPi ok.piF ok.look ok.look1 ok.look2 ok.fLk0 ok.lk0P
        ok.fLk1 ok.lk1P ok.fLk2 ok.lk2P Lk k q (rcRL fun i => (h i : ℕ)) (W := W)
        (by rw [← rcR_encPerm]; omega)
        (by have := wout1 h; unfold rcROutV at this; rw [← rcR_encPerm]; omega)
      rw [← rcR_encPerm] at this
      exact this)
  have hmK : mapK = 1000 := rfl
  have cmo : hs.length * (10 ^ 24 * (W + 1) ^ 5) + mapK * (hs.length + 1) *
      ((Val.list [.list [rcTV Lk, .nat k, natList (List.range q)], .list (hs.map encPerm)]).wt +
        (Val.list (hs.map (rcROutV Lk k q))).wt + 1) ≤ 2 * 10 ^ 24 * (W + 1) ^ 9 := by
    have h1 : hs.length * (10 ^ 24 * (W + 1) ^ 5) ≤ (W + 1) * (10 ^ 24 * (W + 1) ^ 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (W + 1) * (10 ^ 24 * (W + 1) ^ 5) = 10 ^ 24 * (W + 1) ^ 6 := by ring
    have h3 : (hs.length + 1) * ((Val.list [.list [rcTV Lk, .nat k, natList (List.range q)],
        .list (hs.map encPerm)]).wt + (Val.list (hs.map (rcROutV Lk k q))).wt + 1) ≤
        (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : (W + 1) * (W + 1) = (W + 1) ^ 2 := (pow_two _).symm
    have h5 : mapK * (hs.length + 1) * ((Val.list [.list [rcTV Lk, .nat k,
        natList (List.range q)], .list (hs.map encPerm)]).wt +
        (Val.list (hs.map (rcROutV Lk k q))).wt + 1) ≤ 1000 * (W + 1) ^ 2 := by
      rw [hmK, Nat.mul_assoc, ← h4]; exact Nat.mul_le_mul_left _ h3
    omega
  have dout := rcRDW.call dc (hmo.mono cmo) (by omega)
  -- the cells
  let r2 : List Val := [.list (hs.map encPerm), .list (hs.map (rcROutV Lk k q))]
  obtain ⟨Cv, hCv⟩ : ∃ Cv : Val, Cv = .list [natList dl, rcTV Lk, .nat k, .nat q, natList wl,
      natList rl, .nat car.toNat, .nat uno.toNat, natList rowT] := ⟨_, rfl⟩
  have wCv : Cv.wt ≤ 6000 * (M + 1) ^ 5 := by
    have hCl := wt_list_le_of [natList dl, rcTV Lk, .nat k, .nat q, natList wl,
      natList rl, .nat car.toNat, .nat uno.toNat, natList rowT] (c := 300 * (M + 1) ^ 5) (by
      have : (M + 1) ^ 2 ≤ (M + 1) ^ 5 := rcR_pow_le_pow (by omega) (by norm_num)
      have : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
      have : 5 ≤ M := by
        have := length_lt_wt_list [.list svs, .nat q, .list (ps.map pairV), natList wl,
          natList rl]
        simp only [List.length_cons, List.length_nil] at this; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    have : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    rw [hCv]; simp only [List.length_cons, List.length_nil] at hCl; omega
  have dCv := (rcRDW.mkList (P := P) (W := W) (env := _ :: r2) (c := 5 * W + 20)
    [(.get (.get (arg 0) (.nat 0)) (.nat 2), natList dl), (.get (arg 2) (.nat 2), rcTV Lk),
      (.get (.get (arg 0) (.nat 0)) (.nat 0), .nat k), (.get (arg 0) (.nat 1), .nat q),
      (.get (arg 0) (.nat 3), natList wl), (.get (arg 0) (.nat 4), natList rl),
      (.get (arg 2) (.nat 4), .nat car.toNat), (.get (arg 2) (.nat 5), .nat uno.toNat),
      (.get (arg 3) (.nat 1), natList rowT)] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact (rcRDW.get (rcRDW.get (dA r2) (j := 0) (v := .list svs) rfl) hsv2).mono (by omega)
      · exact (rcRDW.get (dR2 r2) (j := 2) (v := rcTV Lk) rfl).mono (by omega)
      · exact (dk r2).mono (by omega)
      · exact (rcRDW.get (dA r2) (j := 1) (v := .nat q) rfl).mono (by omega)
      · exact (rcRDW.get (dA r2) (j := 3) (v := natList wl) rfl).mono (by omega)
      · exact (rcRDW.get (dA r2) (j := 4) (v := natList rl) rfl).mono (by omega)
      · exact (rcRDW.get (dR2 r2) (j := 4) (v := .nat car.toNat) rfl).mono (by omega)
      · exact (rcRDW.get (dR2 r2) (j := 5) (v := .nat uno.toNat) rfl).mono (by omega)
      · exact (rcRDW.get (dR3 r2) (j := 1) (v := natList rowT) rfl).mono (by omega)) (by
      show Val.wt (.list [natList dl, rcTV Lk, .nat k, .nat q, natList wl,
        natList rl, .nat car.toNat, .nat uno.toNat, natList rowT]) ≤ W
      rw [← hCv]; omega)).cast hCv.symm
  have wcells : (natList ((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT))).wt ≤
      11 * (M + 1) ^ 3 := by
    have h1 := wt_natList_le (xs := (List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT))
      (B := (M + 1) ^ 2) (fun z hz => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
        exact (rcR_cellN_le hwl hrl car uno rowT i).trans (rcR_pow_mono (by omega) 2))
    rw [List.length_map, List.length_range] at h1
    have h0 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : k * (2 * (M + 1) ^ 2 + 5) ≤ (M + 1) * (7 * (M + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : (M + 1) * (7 * (M + 1) ^ 2) = 7 * (M + 1) ^ 3 := by ring
    have : 1 ≤ (M + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc _ ≤ k * (2 * (M + 1) ^ 2 + 5) + 4 := h1
      _ ≤ 11 * (M + 1) ^ 3 := by omega
  have ecell : (List.range k).map (fun i => Val.nat (rcRCellN dl Lk k q wl rl car uno rowT i)) =
      ((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT)).map Val.nat := by
    rw [List.map_map]; rfl
  have wCk := wt_list2_le Cv (natList (List.range k))
  have hmc := rcR_mapN ok.mCell (c := Cv) (xs := List.range k)
    (g := fun i => .nat (rcRCellN dl Lk k q wl rl car uno rowT i)) (K := 10 ^ 23) (d := 3)
    (W := W) (fun i hi => by
      rw [hCv]
      refine (rcR_cell_spec ok.gD ok.cellF ok.look ok.fLk0 ok.lk0P dl Lk k q wl rl car uno rowT
        i).mono ?_
      have h1 := rcR_wt_elemN (c := Cv) hi
      rw [hCv] at h1
      have := rcR_cube_cost (K := 10 ^ 20) (W := W)
        (a := (Val.list [.list [natList dl, rcTV Lk, .nat k, .nat q, natList wl, natList rl,
          .nat car.toNat, .nat uno.toNat, natList rowT], .nat i]).wt) (by rw [← hCv] at h1 ⊢; omega)
      norm_num at this ⊢
      omega) (by omega) (by rw [ecell]; show (natList _).wt ≤ W; omega)
  rw [ecell] at hmc
  have dcell := (rcRDW.call (rcRDW.mk2 dCv (rcRDW.get (dR2 r2) (j := 6)
    (v := natList (List.range k)) rfl) (by omega)) hmc (by show (natList _).wt ≤ W; omega)).cast
    (show Val.list (((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT)).map Val.nat) =
      natList ((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT)) from rfl)
  have wres := wt_list3_le (.list (hs.map (rcROutV Lk k q)))
    (natList ((List.range k).map (rcRCellN dl Lk k q wl rl car uno rowT))) (.list [])
  have wnil : (Val.list []).wt ≤ 4 := by simp
  have dres := rcRDW.mk3 (rcRDW.var (env := _ :: r2) (i := 2)
    (v := .list (hs.map (rcROutV Lk k q))) rfl (by omega)) dcell (rcRDW.nil (by omega))
    (by omega)
  refine rcR_detC (rcRDW.letE dout dres) ?_ ⟨hs, rfl, hg, hl⟩
  rw [hF]
  simp only [List.length_cons, List.length_nil]
  omega

end St4

end GI.Impl
