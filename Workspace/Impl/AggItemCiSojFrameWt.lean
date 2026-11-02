import Workspace.Impl.AggItemCiSojFrame
import Workspace.Impl.AggItemCiSojRectStart
import Workspace.Impl.AggItemCiSojBudgetL

/-! # Uniform byte-value bounds for both rectangle continuation states -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

namespace itcsQFrame

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
  (F : itcsQFrame e S L)

/-- State after the first answer, with the optional second query pending. -/
noncomputable def state0 (u : Val) : Val := .list [.list [F.payload,.list F.pending,.list []],u]

/-- State after the second answer, retaining the complete first answer. -/
noncomputable def state1 (u₀ u₁ : Val) : Val := .list [.list [F.payload,.list [],.list [u₀]],u₁]

/-- The optional pending list is a sublist of the full recorded query list. -/
theorem pending_wt : (Val.list F.pending).wt≤(Val.list F.queries).wt := by
  rw [F.queries_cons]
  exact wt_list_sublist (List.sublist_cons_self _ _)

/-- The first query value also occurs in the full recorded list. -/
theorem first_query_wt : (F.query 1).wt≤(Val.list F.queries).wt := by
  rw [F.queries_cons]
  exact st_wt_mem (List.mem_cons_self ..)

/-- The first continuation state fits its fixed frame bound for every canonical
answer, independently of the selected representative. -/
theorem state0_wt (u : Val) (hu : u.wt≤ ansW k) : (F.state0 u).wt≤ F.weight := by
  have hp := F.pending_wt
  have hk := wt_list3_le F.payload (.list F.pending) (.list [])
  have hi := wt_list2_le (.list [F.payload,.list F.pending,.list []]) u
  simp only [wt_list_nil] at hk
  unfold state0 weight
  omega

/-- The second continuation state has the same fixed bound. -/
theorem state1_wt (u₀ u₁ : Val) (h₀ : u₀.wt≤ ansW k) (h₁ : u₁.wt≤ ansW k) :
    (F.state1 u₀ u₁).wt≤ F.weight := by
  have hb := wt_list_le [u₀]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hb
  have hk := wt_list3_le F.payload (.list []) (.list [u₀])
  have hi := wt_list2_le (.list [F.payload,.list [],.list [u₀]]) u₁
  simp only [wt_list_nil] at hk
  unfold state1 weight
  omega

/-- A complete one-answer finalizer input fits the frame bound. -/
theorem final1_wt (u : Val) (hu : u.wt≤ ansW k) :
    (Val.list [F.payload,.list [u]]).wt≤ F.weight := by
  have hb := wt_list_le [u]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hb
  have hi := wt_list2_le F.payload (.list [u])
  unfold weight
  omega

/-- A complete two-answer finalizer input fits the frame bound. -/
theorem final2_wt (u₀ u₁ : Val) (h₀ : u₀.wt≤ ansW k) (h₁ : u₁.wt≤ ansW k) :
    (Val.list [F.payload,.list [u₀,u₁]]).wt≤ F.weight := by
  have hb := wt_list2_le u₀ u₁
  have hi := wt_list2_le F.payload (.list [u₀,u₁])
  unfold weight
  omega

/-- The initial encoded request and continuation fit the same frame bound. -/
theorem ask_wt : (itcsAskV (F.query 1) F.payload (.list F.pending)).wt≤ F.weight := by
  have hp := F.pending_wt
  have hq := F.first_query_wt
  have ha := itcs_ask_weight (F.query 1) F.payload (.list F.pending)
  unfold weight
  omega

/-- All payload and query bytes occur in the initial request. Its paid-for
output weight therefore controls the whole retained frame. -/
theorem weight_request : F.weight ≤
    1000*(4*(itcsAskV (F.query 1) F.payload (.list F.pending)).wt+ansW k+105) := by
  let out := itcsAskV (F.query 1) F.payload (.list F.pending)
  have hq : (F.query 1).wt ≤ out.wt := st_wt_mem
    (by simp : F.query 1∈[.nat 1,.nat 1,F.query 1,.list [F.payload,.list F.pending,.list []]])
  have hk : (Val.list [F.payload,.list F.pending,.list []]).wt ≤ out.wt := st_wt_mem
    (by simp : Val.list [F.payload,.list F.pending,.list []]∈[.nat 1,.nat 1,F.query 1,.list [F.payload,.list F.pending,.list []]])
  have hp : F.payload.wt ≤ out.wt := (st_wt_mem (List.mem_cons_self ..)).trans hk
  have hn : (Val.list F.pending).wt ≤ out.wt :=
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hk
  have hs := wt_list_le [F.query 1]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hs
  have ha := wt_list_append_le [F.query 1] F.pending
  have hall : (Val.list F.queries).wt ≤ 3*out.wt+5 := by
    rw [F.queries_cons]
    change (Val.list ([F.query 1]++F.pending)).wt ≤ _
    omega
  unfold weight
  change 1000*(F.payload.wt+(Val.list F.queries).wt+ansW k+100) ≤ 1000*(4*out.wt+ansW k+105)
  omega

/-- A paid-for initial request and canonical-answer bound control the frame by
the common linear structural envelope. -/
theorem weight_request_bound {n : ℕ}
    (hreq : (itcsAskV (F.query 1) F.payload (.list F.pending)).wt ≤ n) (ha : ansW k ≤ n) :
    F.weight ≤ 10^9*(n+100) := by
  have h := F.weight_request
  omega

end itcsQFrame

/-- The queue's exact scalar wrapper cost is linear in its five bounded inputs. -/
theorem itcs_queue_cost_scalar (payload : Val) (pending answers : List Val) (u : Val) {Cf n : ℕ}
    (hp : payload.wt≤ n) (hn : (Val.list pending).wt≤ n) (ha : (Val.list answers).wt≤ n)
    (hu : u.wt≤ n) (hc : Cf≤ n) :
    100*(itcsQueueW payload pending answers u Cf+1)+Cf≤10^9*(n+100) := by
  unfold itcsQueueW
  omega

/-- The common structural envelope dominates the queue and fixed constructor
costs at any actual input budget. -/
theorem itcs_wrapper_linear (n : ℕ) : 10^9*(n+100)≤ itcsWrapperC n := by
  have hs : n+100≤ itSVB n+n+100 := by omega
  have hp := hs.trans (Nat.le_self_pow (by decide : 8≠0) (itSVB n+n+100))
  exact (Nat.mul_le_mul_left (10^9) hp).trans (Nat.le_add_right _ _)

/-- Fixed polynomial bookkeeping costs of degree at most eight fit the common
structural envelope. -/
theorem itcs_wrapper_power (W c d a : ℕ) (hc : c ≤ 10^9) (hd : d ≤ 100) (ha : a ≤ 8) :
    c*(W+d)^a ≤ itcsWrapperC W := by
  have hb : W+d ≤ itSVB W+W+100 := by omega
  have hpos : 1 ≤ itSVB W+W+100 := by omega
  have hp := (Nat.pow_le_pow_left hb a).trans (Nat.pow_le_pow_right hpos ha)
  exact (Nat.mul_le_mul hc hp).trans (Nat.le_add_right _ _)

/-- The parent context's encoded size fits the structural envelope as well. -/
theorem itcs_wrapper_parent (W : ℕ) : itSVB W ≤ itcsWrapperC W := by
  have hs : itSVB W ≤ itSVB W+W+100 := by omega
  have hp := hs.trans (Nat.le_self_pow (by decide : 8≠0) (itSVB W+W+100))
  exact hp.trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 10^9)).trans (Nat.le_add_right _ _))

end GI.Impl
