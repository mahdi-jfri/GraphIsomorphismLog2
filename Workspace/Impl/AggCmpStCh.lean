import Workspace.Impl.AggCmpStProg

/-!
# The start of a pair: the choice for the first coset

`cm_ch_spec`: the function `cmChF` (at `b + 8`) on `[kst, [encGroup gs, encPerm a]]`, for a cache
value `(gs, a)` that stands for an entry `E`, chooses the representative of the coset of `E` with
the pick cache: the first cache value that passes `cmTest` (`cmFind_spec`, one **Membership**
call per value) gives a hit, and otherwise `(gs, a)` is appended (`cmChoice_find`). It returns the
program state at stage `0` with the new representative and cache. This is the same choice as in
the answer move (`cm_ans_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens Membership)

section Ch

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S}

set_option maxHeartbeats 4000000 in
/-- **The choice for the first coset.** -/
theorem cm_ch_spec (hm : Membership) {Pg : Program} {b jm jp : ℕ} (hat : CmMvAt0 Pg b jm)
    (hst : CmStAt Pg b jp) (hjm : Pg.prims[jm]? = some (membershipPrim hm)) {par : Val}
    {σ : CmSt k} {gs : List (Perm (Fin k))} {a : Perm (Fin k)} {E : CmEnt S.dom}
    (hE : CmEntOK e S (gs, a) E) (hgl : gs.length ≤ (k + L.q) ^ 2) {Bw Bk W : ℕ}
    (hW : 100 * Bw + 1000 ≤ W) (hWk : 10 * Bk + 1000 ≤ W)
    (hwt : (Val.list [σ.val par, cmKeyV gs a]).wt ≤ Bk)
    (hnew : ∀ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
      cache'.length ≤ σ.cache.length + 1 → (∀ p ∈ cache', p.1.length ≤ (k + L.q) ^ 2) →
      (Val.list [(⟨0, o', cache', σ.acc, 1⟩ : CmSt k).val par, .list []]).wt ≤ Bw)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2) :
    CpFB Pg (b + 8) (.list [σ.val par, cmKeyV gs a]) W (cmFindCost hm W + 1000 * (W + 20))
      (fun w => ∃ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
        CmChoice (e := e) (L := L) σ.cache (cmEntSet E) o' cache' ∧
        (∀ p ∈ cache', p.1.length ≤ (k + L.q) ^ 2) ∧
        (Val.list [(⟨0, o', cache', σ.acc, 1⟩ : CmSt k).val par, .list []]).wt ≤ Bw ∧
        w = .list [.nat 2, .list [(⟨0, o', cache', σ.acc, 1⟩ : CmSt k).val par, .list []]]) := by
  set ks := σ.vals par with hks
  set key := cmKeyV gs a with hkey
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, key]).wt ≤ W := by rw [← hsv]; omega
  have h0 : ∀ rest : List Val, (Val.list [.list ks, key] :: rest)[0]? =
      some (.list [.list ks, key]) := fun _ => rfl
  have hksB : (Val.list ks).wt < Bk := by
    have := cm_wt_lt_of_mem (vs := [.list ks, key]) (v := .list ks) (by simp)
    rw [← hsv] at this ⊢
    omega
  have hkeyB : key.wt < Bk := by
    have := cm_wt_lt_of_mem (vs := [.list ks, key]) (v := key) (by simp)
    rw [← hsv] at this
    omega
  have hcB : (Val.list (σ.cache.map cmEntV)).wt < Bk := by
    have := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.cache.map cmEntV)) (by simp [hks, CmSt.vals])
    omega
  have hpa : ∀ a : Perm (Fin k), (encPerm a).wt ≤ 4 * (k + 1) ^ 2 := fun a => wt_encPerm_le a
  have haB : (encPerm a).wt < Bk := by
    have := cm_wt_lt_of_mem (vs := [encGroup gs, encPerm a]) (v := encPerm a) (by simp)
    have : key.wt = (Val.list [encGroup gs, encPerm a]).wt := rfl
    omega
  set env : List Val := [.list [.list ks, key]] with henv
  have dU : ∀ rest, Det Pg (.list [.list ks, key] :: rest) cmU key (2 * (W + 20)) := fun rest =>
    (Det.get' (Det.var' (h0 rest)) (Det.nat 1) rfl).mono (by
      have := cm_wt_lt_of_mem (vs := [.list ks, key]) (v := key) (by simp); omega)
  have dK3 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 3)
    (v := .list (σ.cache.map cmEntV)) rfl (by omega)
  have hkW : (Val.list [key, .list (σ.cache.map cmEntV)]).wt ≤ W := by
    have := wt_list2_le key (.list (σ.cache.map cmEntV))
    omega
  have dF := Det.call (Det.mk2 (dU []) (dK3 [])) (cmFind_spec hm hat.find hjm gs a σ.cache hkW)
  set i := σ.cache.findIdx (cmTest gs a) with hi
  have hiW : (Val.nat i).wt ≤ W := by
    have h1 : i ≤ σ.cache.length := List.findIdx_le_length
    have h2 := length_lt_wt_list (σ.cache.map cmEntV)
    have h3 := wt_nat_le i
    simp only [List.length_map] at h2
    omega
  have hch := cmChoice_find (L := L) (cache := σ.cache) hE hgl
  refine CpFB.intro hst.ch ?_
  unfold cmChF
  rw [hsv]
  refine (CpEB.letE (Cb := 700 * (W + 20))
    (CpEB.det dF (le_refl _) hiW (Q := fun v => v = .nat i) rfl)
    fun v hv _ => ?_).mono (by
      have := wt_nat_le i
      have := wt_list2_le key (.list (σ.cache.map cmEntV))
      omega) fun _ h => h
  subst hv
  set env2 := env ++ [.nat i] with henv2
  have h02 : env2[0]? = some (.list [.list ks, key]) := rfl
  have dK0' := cp_rdK (P := Pg) h02 hwW (j := 0) (v := par) rfl (by omega)
  have dK3' := cp_rdK (P := Pg) h02 hwW (j := 3) (v := .list (σ.cache.map cmEntV)) rfl (by omega)
  have dK4' := cp_rdK (P := Pg) h02 hwW (j := 4) (v := .list (σ.acc.map boolVal)) rfl (by omega)
  have dU' : Det Pg env2 cmU key (2 * (W + 20)) := dU [.nat i]
  have dI : Det Pg env2 (.var 1) (.nat i) (W + 1) := (Det.var' rfl).mono (by omega)
  have dLen := Det.length dK3'
  have dLt := Det.arith' (op := .lt) dI dLen
    (z := if i < (σ.cache.map cmEntV).length then 1 else 0) (by
      simp only [GI.Machine.BinOp.eval])
  have hlenW : (σ.cache.map cmEntV).length ≤ W := by
    have := length_lt_wt_list (σ.cache.map cmEntV); omega
  have hval : ∀ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
      (⟨0, o', cache', σ.acc, 1⟩ : CmSt k).val par = .list [par, .nat 0, cmOV o',
        .list (cache'.map cmEntV), .list (σ.acc.map boolVal), .nat 1] := fun _ _ => rfl
  by_cases hhit : i < σ.cache.length
  · -- a hit
    rw [if_pos hhit, if_pos hhit] at hch
    have hhit' : i < (σ.cache.map cmEntV).length := by simpa using hhit
    rw [if_pos hhit'] at dLt
    set a' := (σ.cache.getD i ([], 1)).2 with ha'
    have hw' := hnew (some a') σ.cache le_self_add hlen
    have hgv : (σ.cache.map cmEntV)[i]? = some (cmEntV (σ.cache.getD i ([], 1))) := by
      rw [List.getD_eq_getElem _ _ hhit]; simp [hhit]
    have dEnt := Det.get' dK3' dI hgv
    have dEnt' : Det Pg env2 (.get (cpKf 3) (.var 1))
        (.list [encGroup (σ.cache.getD i ([], 1)).1, encPerm a']) _ := dEnt
    have dRep := Det.mk1 (Det.get' dEnt' (Det.nat 1) rfl)
    have hσW : ((⟨0, some a', σ.cache, σ.acc, 1⟩ : CmSt k).val par).wt ≤ W := by
      have := cm_wt_lt_of_mem (vs := [(⟨0, some a', σ.cache, σ.acc, 1⟩ : CmSt k).val par, .list []])
        (v := (⟨0, some a', σ.cache, σ.acc, 1⟩ : CmSt k).val par) (by simp)
      omega
    have hentW : (cmEntV (σ.cache.getD i ([], 1))).wt ≤ W := by
      have := cm_wt_lt_of_mem (vs := σ.cache.map cmEntV) (v := cmEntV (σ.cache.getD i ([], 1)))
        (List.mem_of_getElem? hgv)
      omega
    have dl := cp_mkList' (P := Pg) (env := env2) (W := W) (c := 20 * (W + 20))
      [(cpKf 0, par), (.nat 0, .nat 0),
        (mk1 (.get (.get (cpKf 3) (.var 1)) (.nat 1)), cmOV (some a')),
        (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
        (.nat 1, .nat 1)] (v := (⟨0, some a', σ.cache, σ.acc, 1⟩ : CmSt k).val par)
      (by rw [hval]; rfl) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact dK0'.mono (by omega)
        · exact (Det.nat 0).mono (by omega)
        · refine dRep.mono ?_
          have h1 := cm_wt_lt_of_mem (vs := [encGroup (σ.cache.getD i ([], 1)).1, encPerm a'])
            (v := encPerm a') (by simp)
          have h2 : (cmEntV (σ.cache.getD i ([], 1))).wt =
            (Val.list [encGroup (σ.cache.getD i ([], 1)).1, encPerm a']).wt := rfl
          have := wt_list1_le (encPerm a')
          omega
        · exact dK3'.mono (by omega)
        · exact dK4'.mono (by omega)
        · exact (Det.nat 1).mono (by omega)) hσW
    refine (CpEB.ite dLt (Ct := 6 * (20 * (W + 20) + W + 1) + 5 + 2 * W + 100) (Ce := 0)
      (fun _ => ?_) fun h => absurd h one_ne_zero).mono ?_ fun _ h => h
    · refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega)
        fun w hw => ?_
      exact ⟨_, _, hch, hlen, hw', hw⟩
    · have := wt_nat_le (if i < (σ.cache.map cmEntV).length then 1 else 0)
      rw [if_pos hhit'] at this
      omega
  · -- a miss
    rw [if_neg hhit, if_neg hhit] at hch
    have hhit' : ¬ i < (σ.cache.map cmEntV).length := by simpa using hhit
    rw [if_neg hhit'] at dLt
    have hlen' : ∀ p ∈ σ.cache ++ [(gs, a)], p.1.length ≤ (k + L.q) ^ 2 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hlen p hp
      · simp only [List.mem_singleton] at hp; subst hp; exact hgl
    have hw' := hnew (some a) (σ.cache ++ [(gs, a)]) (by simp) hlen'
    set σ' : CmSt k := ⟨0, some a, σ.cache ++ [(gs, a)], σ.acc, 1⟩ with hσ'
    have hσW : (σ'.val par).wt < Bw := by
      have := cm_wt_lt_of_mem (vs := [σ'.val par, .list []]) (v := σ'.val par) (by simp)
      omega
    have dA : Det Pg env2 (.get cmU (.nat 1)) (encPerm a) (3 * (W + 20)) :=
      Det.rd dU' (by omega) rfl (by omega) (by omega)
    have dRep := Det.mk1 dA
    have dNew := Det.snoc dK3' dU'
    have dNew' : Det Pg env2 (.snoc (cpKf 3) cmU)
        (.list (σ.cache.map cmEntV ++ [cmEntV (gs, a)])) _ := dNew
    have hcW : (Val.list (σ.cache.map cmEntV ++ [cmEntV (gs, a)])).wt < Bw := by
      have := cm_wt_lt_of_mem (vs := [par, .nat 0, cmOV (some a),
        .list ((σ.cache ++ [(gs, a)]).map cmEntV), .list (σ.acc.map boolVal), .nat 1])
        (v := .list ((σ.cache ++ [(gs, a)]).map cmEntV)) (by simp)
      rw [← hval, List.map_append] at this
      exact lt_trans (by simpa using this) hσW
    have dl := cp_mkList' (P := Pg) (env := env2) (W := W) (c := 20 * (W + 20))
      [(cpKf 0, par), (.nat 0, .nat 0), (mk1 (.get cmU (.nat 1)), cmOV (some a)),
        (.snoc (cpKf 3) cmU, .list (σ.cache.map cmEntV ++ [cmEntV (gs, a)])),
        (cpKf 4, .list (σ.acc.map boolVal)), (.nat 1, .nat 1)] (v := σ'.val par)
      (by rw [hσ', hval, List.map_append]; rfl) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact dK0'.mono (by omega)
        · exact (Det.nat 0).mono (by omega)
        · refine dRep.mono ?_
          have := hpa a
          have := wt_list1_le (encPerm a)
          omega
        · refine dNew'.mono ?_
          have : (Val.list (σ.cache.map cmEntV ++ [key])).wt =
            (Val.list (σ.cache.map cmEntV ++ [cmEntV (gs, a)])).wt := rfl
          omega
        · exact dK4'.mono (by omega)
        · exact (Det.nat 1).mono (by omega)) (by omega)
    refine (CpEB.ite dLt (Ct := 0) (Ce := 6 * (20 * (W + 20) + W + 1) + 5 + 2 * W + 100)
      (fun h => absurd rfl h) fun _ => ?_).mono ?_ fun _ h => h
    · refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega)
        fun w hw => ?_
      exact ⟨_, _, hch, hlen', hw', hw⟩
    · have := wt_nat_le (if i < (σ.cache.map cmEntV).length then 1 else 0)
      rw [if_neg hhit'] at this
      omega

end Ch

end GI.Impl
