import Workspace.Lang.Lib.Tabulate

/-!
# Reading and composing the normalization stages

A stage with a known own-cost bound also bounds the weight of its result. The preparation
program uses these bounds to pay for reading fields and building the next stage's argument.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- Follow a path of list indices through a value. -/
def normReadVal : Val → List ℕ → Option Val
  | v, [] => some v
  | .nat _, _ :: _ => none
  | .list vs, j :: js => vs[j]?.bind fun v => normReadVal v js

/-- The corresponding expression, starting from any expression. -/
def normReadE : Expr → List ℕ → Expr
  | e, [] => e
  | e, j :: js => normReadE (.get e (.nat j)) js

/-- Reading a fixed path costs a polynomial in the weight of its root value. -/
theorem normRead_det {Pg : Program} {env : List Val} {expr : Expr} {root out : Val} {ca W : ℕ}
    (ha : Det Pg env expr root ca) (hw : root.wt ≤ W) (path : List ℕ)
    (hread : normReadVal root path = some out) :
    Det Pg env (normReadE expr path) out (ca + (path.map (fun j => j + W + 5)).sum) := by
  induction path generalizing root expr ca with
  | nil =>
    simp only [normReadVal, Option.some.injEq] at hread
    subst hread
    simpa only [normReadE, List.map_nil, List.sum_nil, Nat.add_zero] using ha
  | cons j js ih =>
    cases root with
    | nat a => simp [normReadVal] at hread
    | list vs =>
      simp only [normReadVal, Option.bind_eq_some_iff] at hread
      obtain ⟨v, hj, hjs⟩ := hread
      have hv : v.wt < (Val.list vs).wt := by
        obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
        exact wt_getElem_lt _ _ h
      have hg := Det.get' ha (Det.nat j) hj
      have hh := ih hg (hv.le.trans hw) hjs
      refine hh.mono ?_
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Read a field path from a known environment slot. -/
theorem normRead_var {Pg : Program} {env : List Val} {slot : ℕ} {root out : Val} {W : ℕ}
    (hslot : env[slot]? = some root) (hw : root.wt ≤ W) (path : List ℕ)
    (hread : normReadVal root path = some out) :
    Det Pg env (normReadE (.var slot) path) out
      (root.wt + 1 + (path.map (fun j => j + W + 5)).sum) :=
  normRead_det (Det.var' hslot) hw path hread

/-- Constructing a bounded list of bounded pieces has a uniform polynomial overhead. -/
theorem normPack_det {Pg : Program} {env : List Val} {T : ℕ} (ps : List (Expr × Val))
    (hlen : ps.length ≤ 20) (hw : ∀ p ∈ ps, p.2.wt ≤ T)
    (hd : ∀ p ∈ ps, Det Pg env p.1 p.2 (100 * (T + 1) ^ 2)) :
    Det Pg env (Expr.mkList (ps.map Prod.fst)) (.list (ps.map Prod.snd))
      (10 ^ 6 * (T + 1) ^ 2) := by
  have h := Det.mkList ps hd
  have wo := wt_list_le (ps.map Prod.snd)
  have hs : ((ps.map Prod.snd).map Val.wt).sum ≤ ps.length * T := by
    have h := List.sum_le_card_nsmul ((ps.map Prod.snd).map Val.wt) T (by
      intro w hw'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact hw p hp)
    simpa only [List.length_map] using h
  simp only [List.length_map] at wo
  have hp : ps.length * T ≤ 20 * T := Nat.mul_le_mul_right _ hlen
  have hT : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine h.mono ?_
  have hc : ps.length * (100 * (T + 1) ^ 2 + (Val.list (ps.map Prod.snd)).wt + 1) ≤
      20 * (100 * (T + 1) ^ 2 + 40 * T + 25) :=
    Nat.mul_le_mul hlen (by omega)
  omega

/-- A stage's own-cost bound also pays for copying its result into the calling environment. -/
theorem normBound_call {Pg : Program} {env : List Val} {expr : Expr} {f ca B : ℕ}
    {input : Val} {R : Val → Prop} (ha : Det Pg env expr input ca)
    (hf : FunAll Pg f input (fun w cost => R w ∧ cost ≤ B)) :
    EvalAll Pg env (.call f expr) (fun w cost => R w ∧ w.wt ≤ B ∧ cost ≤ ca + 2 * B + 1) := by
  refine EvalAll.call_funAll ha fun v c hv => ?_
  obtain ⟨rfl, hc⟩ := hv
  refine hf.wt_lt.mono fun w cb hw => ?_
  exact ⟨hw.1.1, by omega, by omega⟩

/-- Every stored value is within the current stage bound. -/
def normEnvBound (T : ℕ) (env : List Val) : Prop := ∀ v ∈ env, v.wt ≤ T

theorem normEnvBound_get {T : ℕ} {env : List Val} (h : normEnvBound T env)
    {slot : ℕ} {v : Val} (hv : env[slot]? = some v) : v.wt ≤ T := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hv
  exact h _ (List.getElem_mem hi)

theorem normEnvBound_snoc {T T' : ℕ} {env : List Val} {v : Val}
    (h : normEnvBound T env) (hT : T ≤ T') (hv : v.wt ≤ T') : normEnvBound T' (env ++ [v]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h w hw).trans hT
  · simp only [List.mem_singleton] at hw
    subst hw
    exact hv

theorem normReadVal_wt {root out : Val} {path : List ℕ}
    (h : normReadVal root path = some out) : out.wt ≤ root.wt := by
  induction path generalizing root with
  | nil =>
    simp only [normReadVal, Option.some.injEq] at h
    subst h
    exact le_refl _
  | cons j js ih =>
    cases root with
    | nat a => simp [normReadVal] at h
    | list vs =>
      simp only [normReadVal, Option.bind_eq_some_iff] at h
      obtain ⟨v, hj, hjs⟩ := h
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      exact (ih hjs).trans (wt_getElem_lt _ _ hi).le

private theorem normRead_sum (path : List ℕ) (T : ℕ) :
    (path.map (fun j => j + T + 5)).sum = path.sum + path.length * (T + 5) := by
  induction path with
  | nil => simp
  | cons j js ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Fixed record paths used by preparation have a uniform quadratic read bound. -/
theorem normRead_env {Pg : Program} {env : List Val} {T slot : ℕ} {root out : Val}
    (henv : normEnvBound T env) (hslot : env[slot]? = some root) (path : List ℕ)
    (hread : normReadVal root path = some out) (hlen : path.length ≤ 5) (hsum : path.sum ≤ 50)
    (hT : 100 ≤ T) :
    out.wt ≤ T ∧ Det Pg env (normReadE (.var slot) path) out (100 * (T + 1) ^ 2) := by
  have hr := normEnvBound_get henv hslot
  refine ⟨(normReadVal_wt hread).trans hr, (normRead_var hslot hr path hread).mono ?_⟩
  rw [normRead_sum]
  have hl := Nat.mul_le_mul_right (T + 5) hlen
  have hp : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

end GI.Impl
