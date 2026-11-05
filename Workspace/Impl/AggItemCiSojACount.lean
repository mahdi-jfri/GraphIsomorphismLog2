module

public import Workspace.Impl.AggStructDC

@[expose] public section

/-! # Counted composition for stages with nondeterministic certified encodings -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- Every run has the stated semantic result, counted own cost, and output
weight. The last clause allows the same bound through a representation call
whose generator list may vary. -/
def itcsAC (Pg : Program) (env : List Val) (e : Expr) (P : Val → Prop) (n E W : ℕ) : Prop :=
  EvalAll Pg env e fun v cost => P v ∧ cost≤ n*(W+1)+E ∧ v.wt≤ W

private theorem itcs_ac_addcost {ca cb w na nb Ea Eb W : ℕ}
    (ha : ca≤ na*(W+1)+Ea) (hb : cb≤ nb*(W+1)+Eb) (hw : w≤ W) :
    ca+cb+w+1≤(na+nb+1)*(W+1)+(Ea+Eb) := by
  simp only [Nat.add_mul,Nat.one_mul]
  omega

namespace itcsAC

variable {Pg : Program} {env : List Val} {W : ℕ}

/-- Raise the counted structural and callee budgets. -/
theorem mono {e : Expr} {P : Val → Prop} {n E n' E' : ℕ} (h : itcsAC Pg env e P n E W)
    (hn : n≤ n') (hE : E≤ E') : itcsAC Pg env e P n' E' W :=
  EvalAll.mono h fun v cost ⟨hp,hc,hw⟩ =>
    ⟨hp,hc.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hn) hE),hw⟩

/-- A deterministic expression can be used as a certified encoding stage. -/
theorem of_dc {e : Expr} {v : Val} {P : Val → Prop} {n E : ℕ}
    (h : StDC Pg env e v n E W) (hp : P v) (hw : v.wt≤ W) : itcsAC Pg env e P n E W :=
  EvalAll.mono h fun w cost ⟨he,hc⟩ => by rw [he]; exact ⟨hp,hc,hw⟩

/-- Call an actual function whose output can have several certified encodings.
The function's cost pays for its returned value. -/
theorem call {a : Expr} {f : ℕ} {v : Val} {P : Val → Prop} {na Ea C : ℕ}
    (ha : StDC Pg env a v na Ea W) (hf : FunAll Pg f v fun w cost => P w ∧ cost≤ C)
    (hC : C≤ W) : itcsAC Pg env (.call f a) P (na+1) (Ea+C) W := by
  unfold itcsAC
  refine EvalAll.call_funAll ha ?_
  intro v' ca hv
  obtain ⟨he,hca⟩ := hv
  subst v'
  exact hf.wt_lt.mono fun w cb ⟨⟨hp,hcb⟩,hw⟩ =>
    ⟨hp,itcs_ac_addcost hca (show cb≤0*(W+1)+C by simpa only [Nat.zero_mul,Nat.zero_add] using hcb)
      (hw.le.trans (hcb.trans hC)),hw.le.trans (hcb.trans hC)⟩

/-- Bind a deterministic preparation stage. -/
theorem let_dc {a body : Expr} {v : Val} {P : Val → Prop} {na nb Ea Eb : ℕ}
    (ha : StDC Pg env a v na Ea W) (hb : itcsAC Pg (env++[v]) body P nb Eb W) :
    itcsAC Pg env (.letE a body) P (na+nb+1) (Ea+Eb) W := by
  unfold itcsAC at hb ⊢
  refine EvalAll.letE ha ?_
  intro v' ca hv
  obtain ⟨he,hca⟩ := hv
  subst v'
  exact EvalAll.mono hb fun w cb ⟨hp,hcb,hw⟩ => ⟨hp,itcs_ac_addcost hca hcb hw,hw⟩

/-- Bind a certified stage, retaining its semantic witness and paid-for weight. -/
theorem letE {a body : Expr} {R P : Val → Prop} {na nb Ea Eb : ℕ}
    (ha : itcsAC Pg env a R na Ea W)
    (hb : ∀ v, R v → v.wt≤ W → itcsAC Pg (env++[v]) body P nb Eb W) :
    itcsAC Pg env (.letE a body) P (na+nb+1) (Ea+Eb) W := by
  unfold itcsAC at ha ⊢
  refine EvalAll.letE ha ?_
  intro v ca hv
  obtain ⟨hr,hca,hw⟩ := hv
  exact EvalAll.mono (hb v hr hw) fun w cb ⟨hp,hcb,hww⟩ =>
    ⟨hp,itcs_ac_addcost hca hcb hww,hww⟩

/-- Select the literal numeric branch of the program, without replacing its test. -/
theorem ite {c t e : Expr} {x : ℕ} {P : Val → Prop} {nc nt ne Ec Et Ee : ℕ}
    (hc : StDC Pg env c (.nat x) nc Ec W)
    (ht : x≠0 → itcsAC Pg env t P nt Et W) (he : x=0 → itcsAC Pg env e P ne Ee W) :
    itcsAC Pg env (.ite c t e) P (nc+(nt+ne)+1) (Ec+(Et+Ee)) W := by
  unfold itcsAC
  refine EvalAll.ite hc ?_ ?_
  · intro v cost hv
    exact ⟨x,hv.1⟩
  · intro x' cc hv
    obtain ⟨hx,hcc⟩ := hv
    have heq : x'=x := Val.nat.inj hx
    subst x'
    by_cases hz : x=0
    · rw [if_pos hz]
      have hb := (he hz).mono (Nat.le_add_left ne nt) (Nat.le_add_left Ee Et)
      exact EvalAll.mono hb fun w cb ⟨hp,hcb,hw⟩ => ⟨hp,itcs_ac_addcost hcc hcb hw,hw⟩
    · rw [if_neg hz]
      have hb := (ht hz).mono (Nat.le_add_right nt ne) (Nat.le_add_right Et Ee)
      exact EvalAll.mono hb fun w cb ⟨hp,hcb,hw⟩ => ⟨hp,itcs_ac_addcost hcc hcb hw,hw⟩

/-- Install the actual function body and pass to its public cost bound. -/
theorem funAll {f n E C : ℕ} {body : Expr} {v : Val} {P : Val → Prop}
    (hf : Pg.funs[f]?=some body) (h : itcsAC Pg [v] body P n E W)
    (hC : n*(W+1)+E≤ C) : FunAll Pg f v fun w cost => P w ∧ cost≤ C :=
  FunAll.intro hf (EvalAll.mono h fun w cost ⟨hp,hc,_⟩ => ⟨hp,hc.trans hC⟩)

end itcsAC
end GI.Impl
