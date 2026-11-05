module

public import Workspace.Impl.AggItemCiSojWt
public import Workspace.Impl.ScriptRun

@[expose] public section

/-!
# Scheduling the at most two rectangle queries

The start asks the untwisted query. Its continuation stores the optional second
query and a list of canonical answers. The step appends the new answer, asks the
second query when present, and otherwise calls the answer finalizer. Thus both
complete answers are available when rebuilding the full item group.
-/

set_option maxRecDepth 2048

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Read one field of the continuation stored in entry zero of the step input. -/
def itcsKst (i : ℕ) : Expr := .get (arg 0) (.nat i)

/-- Ask the pending second query, keeping the complete first answer. -/
def itcsQueueAsk : Expr :=
  mk4 (.nat 1) (.nat (modeCode .cont)) (.get (itcsKst 1) (.nat 0))
    (mk3 (itcsKst 0) .nil (.var 1))

/-- The actual step program on `[[payload,pending,answers],u]`. The pending list is
empty or a singleton, because the model makes at most two rectangle calls. -/
def itcsQueueF (fin : ℕ) : Expr :=
  .letE (.snoc (itcsKst 2) (arg 1))
    (.ite (.length (itcsKst 1)) itcsQueueAsk (.call fin (mk2 (itcsKst 0) (.var 1))))

/-- Common budget for the continuation and the finalizer's deterministic result. -/
def itcsQueueW (payload : Val) (pending answers : List Val) (u : Val) (Cf : ℕ) : ℕ :=
  100 * (payload.wt + (Val.list pending).wt + (Val.list answers).wt + u.wt + Cf + 10)

/-- Every structural intermediate of a queue step fits the common budget. -/
theorem itcs_queue_weights (payload : Val) (pending answers : List Val) (u : Val) (Cf : ℕ) :
    let Bw := itcsQueueW payload pending answers u Cf
    (Val.list [.list [payload,.list pending,.list answers],u]).wt ≤ Bw ∧
      (Val.list (answers ++ [u])).wt ≤ Bw ∧
      (Val.list [payload,.list (answers ++ [u])]).wt ≤ Bw ∧
      (Val.list [payload,.list [],.list (answers ++ [u])]).wt ≤ Bw ∧
      10 ≤ Bw ∧ Cf ≤ Bw := by
  have wk := wt_list3_le payload (.list pending) (.list answers)
  have wi := wt_list2_le (.list [payload,.list pending,.list answers]) u
  have wb := wt_list_snoc_le answers u
  have wf := wt_list2_le payload (.list (answers ++ [u]))
  have wn := wt_list3_le payload (.list []) (.list (answers ++ [u]))
  simp only [wt_list_nil] at wn
  dsimp only [itcsQueueW]
  omega

/-- Step with no pending query invokes the finalizer on all canonical answers. -/
theorem itcs_queue_final {Pg : Program} {f fin Cf : ℕ} (payload u out : Val) (answers : List Val)
    (hf : Pg.funs[f]? = some (itcsQueueF fin))
    (hfin : FunDet Pg fin (.list [payload,.list (answers ++ [u])]) out Cf) :
    FunDet Pg f (.list [.list [payload,.list [],.list answers],u]) out
      (100 * (itcsQueueW payload [] answers u Cf + 1) + Cf) := by
  let Bw := itcsQueueW payload [] answers u Cf
  obtain ⟨wi,wb,wf,wn,h10,hCf⟩ := itcs_queue_weights payload [] answers u Cf
  have wo : out.wt ≤ Bw := (itcs_det_weight hfin).trans hCf
  let inp : Val := .list [.list [payload,.list [],.list answers],u]
  have wk : (Val.list [payload,.list [],.list answers]).wt ≤ Bw := (st_wt_mem (by simp)).trans wi
  have wm : payload.wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans wk
  have wa : (Val.list answers).wt ≤ Bw := (st_wt_mem (by simp)).trans wk
  have wu : u.wt ≤ Bw := (st_wt_mem (by simp)).trans wi
  have kst (rest : List Val) : StDC Pg (inp :: rest) (arg 0)
      (.list [payload,.list [],.list answers]) 3 0 Bw := StDC.arg rfl wi (by omega) wk
  have get {rest : List Val} {i : ℕ} {v : Val}
      (hi : [payload,Val.list [],.list answers][i]? = some v) (hii : i+2≤Bw) :
      StDC Pg (inp :: rest) (itcsKst i) v 5 0 Bw :=
    (StDC.get (kst rest) (StDC.nat i hii) hi ((st_wt_mem (List.mem_of_getElem? hi)).trans wk)).mono (by omega) (by omega)
  have buf := StDC.snoc (get (rest := []) (i := 2) rfl (by omega))
    (StDC.arg (P := Pg) (rest := []) (j := 1) rfl wi (by omega) wu) wb
  have v1 : StDC Pg [inp,.list (answers ++ [u])] (.var 1) (.list (answers ++ [u])) 1 0 Bw :=
    StDC.var' rfl wb
  have fc := StDC.call (StDC.mk2 (get (rest := [.list (answers ++ [u])]) (i := 0) rfl (by omega)) v1 wf (by omega)) hfin wo
  have len : StDC Pg [inp,.list (answers ++ [u])] (.length (itcsKst 1)) (.nat 0) 6 0 Bw :=
    StDC.length (get (i := 1) rfl (by omega)) (by change 0+2≤Bw; omega)
  have tail := StDC.ite (t := itcsQueueAsk) (nt := 1) (ne := 20) (Et := 0) (Ee := Cf) len
    (fun h => by omega) (fun _ => fc.mono (by omega) (by omega)) wo
  have body := StDC.letE buf tail wo
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

/-- Step with the second query returns its call request and preserves the complete answer buffer. -/
theorem itcs_queue_next {Pg : Program} {f fin : ℕ} (payload next u : Val) (answers : List Val)
    (hf : Pg.funs[f]? = some (itcsQueueF fin)) :
    FunDet Pg f (.list [.list [payload,.list [next],.list answers],u])
      (.list [.nat 1,.nat (modeCode .cont),next,
        .list [payload,.list [],.list (answers ++ [u])]])
      (100 * (itcsQueueW payload [next] answers u 0 + 1)) := by
  let Bw := itcsQueueW payload [next] answers u 0
  obtain ⟨wi,wb,wf,wn,h10,hCf⟩ := itcs_queue_weights payload [next] answers u 0
  have wk : (Val.list [payload,.list [next],.list answers]).wt ≤ Bw := (st_wt_mem (by simp)).trans wi
  have wm : payload.wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans wk
  have wp : (Val.list [next]).wt ≤ Bw := (st_wt_mem (by simp)).trans wk
  have wu : u.wt ≤ Bw := (st_wt_mem (by simp)).trans wi
  have wnext : next.wt ≤ (Val.list [next]).wt := st_wt_mem (List.mem_cons_self ..)
  have wo : (Val.list [.nat 1,.nat (modeCode .cont),next,
      .list [payload,.list [],.list (answers ++ [u])]]).wt ≤ Bw := by
    have wnextkst := wt_list3_le payload (.list []) (.list (answers ++ [u]))
    have h := wt_list4_le (.nat 1) (.nat (modeCode .cont)) next (.list [payload,.list [],.list (answers ++ [u])])
    have wb' := wt_list_snoc_le answers u
    have h1 := wt_nat_le 1
    have h2 := wt_nat_le (modeCode .cont)
    simp only [wt_list_nil,modeCode] at wnextkst h2 h
    dsimp only [Bw,itcsQueueW]
    simp only [modeCode] at *
    omega
  let inp : Val := .list [.list [payload,.list [next],.list answers],u]
  have kst (rest : List Val) : StDC Pg (inp :: rest) (arg 0)
      (.list [payload,.list [next],.list answers]) 3 0 Bw := StDC.arg rfl wi (by omega) wk
  have get {rest : List Val} {i : ℕ} {v : Val}
      (hi : [payload,Val.list [next],.list answers][i]? = some v) (hii : i+2≤Bw) :
      StDC Pg (inp :: rest) (itcsKst i) v 5 0 Bw :=
    (StDC.get (kst rest) (StDC.nat i hii) hi ((st_wt_mem (List.mem_of_getElem? hi)).trans wk)).mono (by omega) (by omega)
  have buf := StDC.snoc (get (rest := []) (i := 2) rfl (by omega))
    (StDC.arg (P := Pg) (rest := []) (j := 1) rfl wi (by omega) wu) wb
  have v1 : StDC Pg [inp,.list (answers ++ [u])] (.var 1) (.list (answers ++ [u])) 1 0 Bw :=
    StDC.var' rfl wb
  have newkst := StDC.mk3 (get (rest := [.list (answers ++ [u])]) (i := 0) rfl (by omega))
    (StDC.nil (by omega)) v1 wn (by omega)
  have nx := StDC.get (get (rest := [.list (answers ++ [u])]) (i := 1) rfl (by omega))
    (StDC.nat 0 (by omega)) rfl (wnext.trans (by dsimp only [Bw,itcsQueueW]; omega))
  have ask := StDC.mk4 (StDC.nat 1 (by omega)) (StDC.nat (modeCode .cont) (by simp only [modeCode]; omega)) nx newkst wo (by omega)
  have len : StDC Pg [inp,.list (answers ++ [u])] (.length (itcsKst 1)) (.nat 1) 6 0 Bw :=
    StDC.length (get (i := 1) rfl (by omega)) (by change 1+2≤Bw; omega)
  have tail := StDC.ite (e := .call fin (mk2 (itcsKst 0) (.var 1))) (nt := 30) (ne := 1) (Et := 0) (Ee := 0) len
    (fun _ => ask.mono (by omega) (by omega)) (fun h => by omega) wo
  have body := StDC.letE buf tail wo
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

end GI.Impl
