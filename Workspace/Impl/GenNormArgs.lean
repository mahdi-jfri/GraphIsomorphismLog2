import Workspace.Impl.GenNormBudget

/-! # Reading and packing the bounded records used by normalization -/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val)

/-- A record component read from a bounded stored value. -/
def normAtom (Pg : Program) (env : List Val) (T : ℕ) (e : Expr) (v : Val) : Prop :=
  v.wt ≤ T ∧ Det Pg env e v (100 * (T + 1) ^ 2)

/-- A small record, suitable as a field of another argument record. -/
def normPiece (Pg : Program) (env : List Val) (T : ℕ) (e : Expr) (v : Val) : Prop :=
  v.wt ≤ 1000 * (T + 1) ^ 2 ∧ Det Pg env e v (10 ^ 6 * (T + 1) ^ 2)

theorem normAtom_piece {Pg : Program} {env : List Val} {T : ℕ} {e : Expr} {v : Val}
    (h : normAtom Pg env T e v) : normPiece Pg env T e v := by
  have hT : T ≤ (T + 1) ^ 2 := (Nat.le_succ T).trans (Nat.le_self_pow (by norm_num) _)
  exact ⟨h.1.trans (by omega), h.2.mono (by omega)⟩

theorem normAtom_read {Pg : Program} {env : List Val} {T slot : ℕ} {root out : Val}
    (henv : normEnvBound T env) (hslot : env[slot]? = some root) (path : List ℕ)
    (hread : normReadVal root path = some out) (hlen : path.length ≤ 5) (hsum : path.sum ≤ 50)
    (hT : 100 ≤ T) : normAtom Pg env T (normReadE (.var slot) path) out :=
  normRead_env henv hslot path hread hlen hsum hT

/-- Packing at most twenty atoms gives a small record. -/
theorem normPiece_pack {Pg : Program} {env : List Val} {T : ℕ} (ps : List (Expr × Val))
    (hlen : ps.length ≤ 20) (hs : ∀ p ∈ ps, normAtom Pg env T p.1 p.2) :
    normPiece Pg env T (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd)) := by
  refine ⟨?_, normPack_det ps hlen (fun p hp => (hs p hp).1) (fun p hp => (hs p hp).2)⟩
  have h := wt_list_le_of (ps.map Prod.snd) (c := T) (by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact (hs p hp).1)
  simp only [List.length_map] at h
  have hh := Nat.mul_le_mul_right (2 * T + 1) hlen
  have hT : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- Packing at most twenty small records fits the common argument budget. -/
theorem normArg_pack {Pg : Program} {env : List Val} {T : ℕ} (ps : List (Expr × Val))
    (hlen : ps.length ≤ 20) (hs : ∀ p ∈ ps, normPiece Pg env T p.1 p.2) :
    Det Pg env (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd)) (normArgBudget T) := by
  have h := normPack_det (T := 1000 * (T + 1) ^ 2) ps hlen
    (fun p hp => (hs p hp).1) (fun p hp => (hs p hp).2.mono (by
      have hx : (T + 1) ^ 2 ≤ (T + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      nlinarith [Nat.zero_le ((T + 1) ^ 2)]))
  refine h.mono ?_
  unfold normArgBudget
  have hx : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith [sq_nonneg ((T + 1) ^ 2 : ℤ)]

/-- A deterministic argument's budget also bounds its encoded weight. -/
theorem normDet_wt {Pg : Program} {env : List Val} {e : Expr} {v : Val} {B : ℕ}
    (h : Det Pg env e v B) : v.wt ≤ B := by
  obtain ⟨w, c, he, rfl, hc⟩ := h.exists_eval
  exact he.wt_lt.le.trans hc

theorem normArg_piece {Pg : Program} {env : List Val} {T : ℕ} {e : Expr} {v : Val}
    (h : normPiece Pg env T e v) : Det Pg env e v (normArgBudget T) := by
  refine h.2.mono ?_
  have hx : (T + 1) ^ 2 ≤ (T + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold normArgBudget
  omega

theorem normAtom_nat {Pg : Program} {env : List Val} {T n : ℕ} (hn : n + 2 ≤ T) :
    normAtom Pg env T (.nat n) (.nat n) := by
  have hw := wt_nat_le n
  have hx : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact ⟨by omega, (Det.nat n).mono (by omega)⟩

theorem normPiece_length {Pg : Program} {env : List Val} {T : ℕ} {e : Expr} {vs : List Val}
    (h : normAtom Pg env T e (.list vs)) :
    normPiece Pg env T (.length e) (.nat vs.length) := by
  have hl := length_lt_wt_list vs
  have hw := wt_nat_le vs.length
  have hv := h.1
  have hx : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact ⟨by omega, (Det.length h.2).mono (by omega)⟩

theorem normPiece_flip {Pg : Program} {env : List Val} {T m k : ℕ} {em ek : Expr}
    (hm : normAtom Pg env T em (.nat m)) (hk : normAtom Pg env T ek (.nat k))
    (hkT : k ≤ T) (hT : 100 ≤ T) :
    normPiece Pg env T (.arith .lt em (.arith .mul (.nat 2) ek))
      (boolVal (decide (m < 2 * k))) := by
  have hmul := Det.arith' (op := .mul) (Det.nat (P := Pg) (env := env) 2) hk.2
    (z := 2 * k) rfl
  have hlt := Det.arith' (op := .lt) hm.2 hmul (z := (decide (m < 2 * k)).toNat) (by
    by_cases h : m < 2 * k <;> simp [GI.Machine.BinOp.eval, h])
  have wm := wt_nat_le (2 * k)
  have wb : (boolVal (decide (m < 2 * k))).wt ≤ 3 := wt_boolVal_le _
  have hx : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine ⟨by omega, hlt.mono ?_⟩
  have hb : (decide (m < 2 * k)).toNat ≤ 1 := by
    cases decide (m < 2 * k) <;> decide
  omega

/-- A one-field read also has a linear bound, used before doing the complement test. -/
theorem normRead_one {Pg : Program} {env : List Val} {T slot j : ℕ} {root out : Val}
    (henv : normEnvBound T env) (hslot : env[slot]? = some root)
    (hread : normReadVal root [j] = some out) (hj : j ≤ 20) (hT : 100 ≤ T) :
    Det Pg env (normReadE (.var slot) [j]) out (10 * (T + 1)) := by
  have hw := normEnvBound_get henv hslot
  refine (normRead_var hslot hw [j] hread).mono ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem normAtom_flip {Pg : Program} {env : List Val} {T m k : ℕ} {em ek : Expr}
    (hm : Det Pg env em (.nat m) (10 * (T + 1)))
    (hk : Det Pg env ek (.nat k) (10 * (T + 1)))
    (hkT : k ≤ T) (hT : 100 ≤ T) :
    normAtom Pg env T (.arith .lt em (.arith .mul (.nat 2) ek))
      (boolVal (decide (m < 2 * k))) := by
  have hmul := Det.arith' (op := .mul) (Det.nat (P := Pg) (env := env) 2) hk
    (z := 2 * k) rfl
  have hlt := Det.arith' (op := .lt) hm hmul (z := (decide (m < 2 * k)).toNat) (by
    by_cases h : m < 2 * k <;> simp [GI.Machine.BinOp.eval, h])
  have hw : (boolVal (decide (m < 2 * k))).wt ≤ 3 := wt_boolVal_le _
  have hb : (decide (m < 2 * k)).toNat ≤ 1 := by
    cases decide (m < 2 * k) <;> decide
  have hx : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact ⟨hw.trans (by omega), hlt.mono (by omega)⟩

end GI.Impl
