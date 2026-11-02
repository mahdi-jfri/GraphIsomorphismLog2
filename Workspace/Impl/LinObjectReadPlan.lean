import Workspace.Impl.GenNormGlue
import Workspace.Impl.PolyBd

namespace GI.Impl
open GI.Cited GI.Lang

/-- Fixed argument-building code. Paths read stored values, and lists and
lengths only arrange those values for the next proved subroutine. -/
inductive linObjectReadPlan where
  | read (slot : ℕ) (path : List ℕ)
  | nat (n : ℕ)
  | nil
  | snoc (xs x : linObjectReadPlan)
  | length (xs : linObjectReadPlan)

def linObjectReadPlan.list (ps : List linObjectReadPlan) : linObjectReadPlan := ps.foldl .snoc .nil

def linObjectReadPlan.expr : linObjectReadPlan → Expr
  | .read i p => normReadE (.var i) p
  | .nat n => .nat n
  | .nil => .nil
  | .snoc xs x => .snoc xs.expr x.expr
  | .length xs => .length xs.expr

def linObjectReadPlan.value (env : List Val) : linObjectReadPlan → Option Val
  | .read i p => env[i]?.bind (fun v => normReadVal v p)
  | .nat n => some (.nat n)
  | .nil => some (.list [])
  | .snoc xs x => do
      let .list vs ← xs.value env | none
      let v ← x.value env
      some (.list (vs++[v]))
  | .length xs => do
      let .list vs ← xs.value env | none
      some (.nat vs.length)

def linObjectPlanBudget : linObjectReadPlan → ℕ → ℕ
  | .read _ p,C => C+1+p.sum+p.length*(C+5)
  | .nat n,_ => n+3
  | .nil,_ => 5
  | .snoc xs x,C => 10*(linObjectPlanBudget xs C+linObjectPlanBudget x C+1)^2
  | .length xs,C => 10*(linObjectPlanBudget xs C+1)^2

theorem linObjectPlanBudget_poly (plan : linObjectReadPlan) : PBU (fun _ C _ => linObjectPlanBudget plan C) := by
  induction plan with
  | read slot path =>
    exact PBU.add (PBU.add (PBU.addc PBU.W 1) (PBU.const path.sum))
      (PBU.mul (PBU.const path.length) (PBU.addc PBU.W 5))
  | nat n => exact PBU.const (n+3)
  | nil => exact PBU.const 5
  | snoc xs x ihs ihx => exact PBU.smul 10 (PBU.pow (PBU.addc (PBU.add ihs ihx) 1) 2)
  | length xs ih => exact PBU.smul 10 (PBU.pow (PBU.addc ih 1) 2)

theorem linObjectPlanListBudget_poly (plans : List linObjectReadPlan) :
    PBU (fun _ C _ => (plans.map (linObjectPlanBudget · C)).sum) := by
  induction plans with
  | nil => exact PBU.const 0
  | cons p ps ih => exact PBU.add (linObjectPlanBudget_poly p) ih

private theorem linObjectReadPath_sum (p : List ℕ) (C : ℕ) :
    (p.map (fun j => j+C+5)).sum = p.sum+p.length*(C+5) := by
  induction p with
  | nil => simp
  | cons i p ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul]; omega

set_option maxHeartbeats 300000 in
theorem linObjectReadPlan_det {P : Program} {env : List Val} {C : ℕ}
    (h : normEnvBound C env) (plan : linObjectReadPlan) {v : Val}
    (hv : plan.value env = some v) : Det P env plan.expr v (linObjectPlanBudget plan C) := by
  induction plan generalizing v with
  | read slot path =>
    simp only [linObjectReadPlan.value,Option.bind_eq_some_iff] at hv
    obtain ⟨root,hs,hr⟩ := hv
    have hw := normEnvBound_get h hs
    have hd := normRead_var (Pg:=P) hs hw path hr
    refine hd.mono ?_
    rw [linObjectReadPath_sum]
    change root.wt+1+(path.sum+path.length*(C+5)) ≤ C+1+path.sum+path.length*(C+5)
    omega
  | nat n =>
    simp only [linObjectReadPlan.value,Option.some.injEq] at hv
    subst v
    exact Det.nat n
  | nil =>
    simp only [linObjectReadPlan.value,Option.some.injEq] at hv
    subst v
    exact Det.nil
  | snoc xs x ihs ihx =>
    simp only [linObjectReadPlan.value] at hv
    cases hs : xs.value env with
    | none => simp [hs] at hv
    | some sv =>
      cases sv with
      | nat n => simp [hs] at hv
      | list vs =>
        cases hx : x.value env with
        | none => simp [hs,hx] at hv
        | some xv =>
          have he : v = .list (vs++[xv]) := by simpa [hs,hx] using hv.symm
          subst v
          have ds := ihs hs
          have dx := ihx hx
          have ws := ds.wt_lt
          have wx := dx.wt_lt
          have wout := wt_list_snoc_le vs xv
          refine (Det.snoc ds dx).mono ?_
          change _ ≤ 10*(linObjectPlanBudget xs C+linObjectPlanBudget x C+1)^2
          have hp : linObjectPlanBudget xs C+linObjectPlanBudget x C+1 ≤
              (linObjectPlanBudget xs C+linObjectPlanBudget x C+1)^2 := Nat.le_self_pow (by decide) _
          omega
  | length xs ih =>
    simp only [linObjectReadPlan.value] at hv
    cases hs : xs.value env with
    | none => simp [hs] at hv
    | some sv =>
      cases sv with
      | nat n => simp [hs] at hv
      | list vs =>
        have he : v = .nat vs.length := by simpa [hs] using hv.symm
        subst v
        have ds := ih hs
        have ws := ds.wt_lt
        have hl := length_lt_wt_list vs
        have wn := wt_nat_le vs.length
        refine (Det.length ds).mono ?_
        change _ ≤ 10*(linObjectPlanBudget xs C+1)^2
        have hp : linObjectPlanBudget xs C+1 ≤ (linObjectPlanBudget xs C+1)^2 := Nat.le_self_pow (by decide) _
        omega

end GI.Impl
