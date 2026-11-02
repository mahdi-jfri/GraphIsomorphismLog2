import Workspace.Impl.AggCmpMvA

/-!
# The move program: the answer of a call

`cm_ans_spec`: from a program state that waits for the answer `u` of a call (`fl = 2`), the
function `cmAnsF` returns what a move must return (`CmMvPost`). An empty answer gives no
representative. An answer `[x, ⟨gs⟩]` gives the coset of `(gs, a₀ x)` (`cm_next_ent`); the
program computes `a₀ x` (`compose_spec`) and finds the first cache value that passes `cmTest`
(`cmFind_spec`, one **Membership** call per value). A hit keeps the cached representative, a
miss appends the new value (`cmChoice_find`). Either way the new state stands for a subset of
the candidates at stage `j + 1` (`cm_pend_rep`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens Membership)
open scoped Pointwise

/-- The cost of the answer move, for program states of weight at most `W`. -/
noncomputable def cmAnsCost (h : Membership) (W : ℕ) : ℕ :=
  cmFindCost h W + permK * (W + 1) ^ 3 + 1000 * (W + 20)

section Ret

variable {P : Program} {env : List Val}

/-- **Returning a new program state with no call.** -/
theorem cm_ret_eb {W Bw c : ℕ} {kst : Expr} {v : Val} (hd : Det P env kst v c)
    (hw : (Val.list [v, .list []]).wt ≤ Bw) (hW : 100 * Bw + 1000 ≤ W) :
    CpEB P env (cmRetE kst) W (c + 2 * W + 100)
      (fun w => w = .list [.nat 2, .list [v, .list []]]) := by
  have d := Det.mk2 (Det.nat (P := P) (env := env) 2) (Det.mk2 hd (Det.nil (P := P) (env := env)))
  have h1 := wt_list2_le (.nat 2) (.list [v, .list []])
  have h2 := wt_nat_le 2
  exact CpEB.det d (by omega) (by omega) rfl

end Ret

section Ans

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

theorem cm_wt_lt_of_mem {vs : List Val} {v : Val} (h : v ∈ vs) : v.wt < (Val.list vs).wt :=
  wt_le_wt_list h

set_option maxHeartbeats 4000000 in
/-- **The answer of a call.** -/
theorem cm_ans_spec (hm : Membership) {Pg : Program} {b jm : ℕ} (hat : CmMvAt0 Pg b jm)
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)}
    {Out : List Bool → Val → Prop} {M₀ Bw W : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)).wt k L.q M₀
      (O.tuples.length * O.tuples.length) ≤ Bw) (hW : 100 * Bw + 1000 ≤ W)
    {m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ} {ps' : List (CmPair L.q P₀.κ)} {j : ℕ}
    {A : Set (Perm S.dom)} {σ : CmSt k} {ents : List (CmEnt S.dom)}
    {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hmeq : m = cmMs (Fintype.card S.dom) (.pend acc ab ps' j A : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pend acc ab ps' j A : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hacc : σ.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps')
    (hj : σ.j + 1 = j) (hjn : j ≤ Fintype.card S.dom) {a₀ : Perm (Fin k)} (ho : σ.o = some a₀)
    (ha₀ : (toFin e).symm a₀ ∈ S.G)
    (hA : A = domOfPos e S a₀ • restrictAns S (cmCall e πd ab σ.j a₀).answer) {u : Val}
    (hu : AnsC e u (cmCall e πd ab σ.j a₀).answer)
    (hwt : (Val.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u]).wt ≤ Bw) :
    CpFB Pg (b + 3) (.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u])
      W (cmAnsCost hm W)
      (CmMvPost e Cs Ag₀ O πd (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Out Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pend acc ab ps' j A))
          '' CmCands Cs Ag₀ O rec) f) := by
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  set ks := σ.vals par with hks
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  have hk : Fintype.card S.dom ≤ k := cp_card_dom_le e
  have hBk : 80 * (k + 1) ^ 2 ≤ Bw := by
    have h2 : cmBw par.wt k L.q M₀ (O.tuples.length * O.tuples.length) ≤ Bw := hBw
    unfold cmBw ansW at h2
    omega
  have hkW : k + 1 ≤ W := by
    have h1 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hksB : (Val.list ks).wt < Bw := by
    have := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := .list ks) (by simp)
    rw [← hsv] at this ⊢
    omega
  have huB : u.wt < Bw := by
    have := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := u) (by simp)
    rw [← hsv] at this
    omega
  have hcB : (Val.list (σ.cache.map cmEntV)).wt < Bw := by
    have := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.cache.map cmEntV)) (by simp [hks, CmSt.vals])
    omega
  have hm1 : 1 ≤ m := by rw [hmeq]; simp only [cmMs]; omega
  -- the new state is light
  have hnew : ∀ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
      cache'.length ≤ σ.cache.length + 1 → (∀ p ∈ cache', p.1.length ≤ (k + L.q) ^ 2) →
      (Val.list [(⟨j, o', cache', acc, 1⟩ : CmSt k).val par, .list []]).wt ≤ Bw := by
    intro o' cache' hcl hcl'
    refine le_trans (cm_wt_state (q := L.q) (M₀ := M₀) (L := O.tuples.length * O.tuples.length)
      ?_ ?_ ?_ hcl' ?_ cm_wt_nil_le) hBw
    · show j ≤ k; omega
    · show 1 ≤ 2; omega
    · show cache'.length ≤ M₀; omega
    · show acc.length ≤ _
      by_contra hh
      rw [cm_pairs_drop_end O (by omega)] at hdrop
      simp at hdrop
  -- reading the pieces
  have dK0 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 0) (v := par) rfl (by omega)
  have dK3 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 3)
    (v := .list (σ.cache.map cmEntV)) rfl (by omega)
  have dK4 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 4)
    (v := .list (σ.acc.map boolVal)) rfl (by omega)
  have dJ1 : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (.arith .add (cpKf 1) (.nat 1))
      (.nat j) (5 * (W + 20)) := fun rest => by
    refine (Det.arith' (op := .add) (cp_rdK (P := Pg) (h0 rest) hwW (j := 1) (v := .nat σ.j) rfl
      (by omega)) (Det.nat 1) (z := j) (by simp [GI.Machine.BinOp.eval]; omega)).mono ?_
    have := wt_nat_le j
    omega
  have dOne : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (.nat 1) (.nat 1) (5 * (W + 20)) :=
    fun rest => (Det.nat 1).mono (by omega)
  have dU : ∀ rest, Det Pg (.list [.list ks, u] :: rest) cmU u (2 * (W + 20)) := fun rest =>
    (Det.get' (Det.var' (h0 rest)) (Det.nat 1) rfl).mono (by
      have := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := u) (by simp); omega)
  have hval : ∀ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
      (⟨j, o', cache', acc, 1⟩ : CmSt k).val par = .list [par, .nat j, cmOV o',
        .list (cache'.map cmEntV), .list (σ.acc.map boolVal), .nat 1] := by
    intro o' cache'; rw [hacc]; rfl
  refine CpFB.intro hat.ans ?_
  unfold cmAnsF
  rw [hsv]
  rcases cm_next_ent (L := L) (πd := πd) (ab := ab) (j := σ.j) ha₀ hu with
    ⟨rfl, hemp⟩ | ⟨x, gs, E, rfl, hgl, hE, hset⟩
  · -- an empty answer
    have dl0 : Det Pg [.list [.list ks, .list []]] (.length cmU) (.nat 0) (2 * (W + 20) + 0 + 3) :=
      Det.length (dU [])
    have hch : CmChoice (e := e) (L := L) σ.cache A none σ.cache :=
      Or.inl ⟨by rw [hA]; exact hemp, rfl, rfl⟩
    have hw' := hnew none σ.cache le_self_add hlen
    have dl := cp_mkList' (P := Pg) (env := [.list [.list ks, .list []]]) (W := W)
      (c := 10 * (W + 20))
      [(cpKf 0, par), (.arith .add (cpKf 1) (.nat 1), .nat j), (.nil, cmOV (none : Option (Perm (Fin k)))),
        (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
        (.nat 1, .nat 1)] (v := (⟨j, none, σ.cache, acc, 1⟩ : CmSt k).val par)
      (by rw [hval]; rfl) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (dK0 []).mono (by omega)
        · exact (dJ1 []).mono (by omega)
        · exact Det.nil.mono (by omega)
        · exact (dK3 []).mono (by omega)
        · exact (dK4 []).mono (by omega)
        · exact (dOne []).mono (by omega))
      (by
        have := cm_wt_lt_of_mem (vs := [(⟨j, none, σ.cache, acc, 1⟩ : CmSt k).val par, .list []])
          (v := (⟨j, none, σ.cache, acc, 1⟩ : CmSt k).val par) (by simp)
        omega)
    refine (CpEB.ite dl0 (Ct := 0) (Ce := 6 * (11 * (W + 20) + W + 1) + 5 + 2 * W + 100)
      (fun h => absurd rfl h) fun _ => ?_).mono ?_ fun _ h => h
    · refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega) fun w hw => ?_
      subst hw
      exact Or.inr ⟨_, cm_pend_rep hmeq hmf hM hc hF hlen hdrop hjn hch hw', rfl⟩
    · unfold cmAnsCost; omega
  · -- an answer `[x, ⟨gs⟩]`
    set env : List Val := [.list [.list ks, .list [encPerm x, encGroup gs]]] with henv
    have dl2 : Det Pg env (.length cmU) (.nat 2) (2 * (W + 20) + 2 + 3) := Det.length (dU [])
    have hgl' : gs.length ≤ (k + L.q) ^ 2 :=
      hgl.trans (Nat.pow_le_pow_left (by omega) 2)
    have hch := cmChoice_find (cache := σ.cache) hE hgl'
    rw [hset, ← hA] at hch
    -- pieces of the answer
    have hxB : (encPerm x).wt < Bw := by
      have := cm_wt_lt_of_mem (vs := [encPerm x, encGroup gs]) (v := encPerm x) (by simp)
      omega
    have hgB : (encGroup gs).wt < Bw := by
      have := cm_wt_lt_of_mem (vs := [encPerm x, encGroup gs]) (v := encGroup gs) (by simp)
      omega
    have hpa : ∀ a : Perm (Fin k), (encPerm a).wt ≤ 4 * (k + 1) ^ 2 := fun a => wt_encPerm_le a
    have dOV : ∀ rest, Det Pg (.list [.list ks, .list [encPerm x, encGroup gs]] :: rest)
        (.get (cpKf 2) (.nat 0)) (encPerm a₀) (4 * (W + 20)) := fun rest => by
      have hv : ks[2]? = some (.list [encPerm a₀]) := by simp [hks, CmSt.vals, ho, cmOV]
      exact Det.rd (cp_rdK (P := Pg) (h0 rest) hwW (j := 2) hv (by omega)) le_rfl rfl
        (by have := hpa a₀; omega) (by omega)
    have dX : ∀ rest, Det Pg (.list [.list ks, .list [encPerm x, encGroup gs]] :: rest)
        (.get cmU (.nat 0)) (encPerm x) (3 * (W + 20)) := fun rest =>
      Det.rd (dU rest) (by omega) rfl (by omega) (by omega)
    have dG : ∀ rest, Det Pg (.list [.list ks, .list [encPerm x, encGroup gs]] :: rest)
        (.get cmU (.nat 1)) (encGroup gs) (3 * (W + 20)) := fun rest =>
      Det.rd (dU rest) (by omega) rfl (by omega) (by omega)
    have hcomp := compose_spec hat.comp a₀ x
    have dC := Det.call (Det.mk2 (dOV []) (dX [])) hcomp
    have hpW : (encPerm (a₀ * x)).wt ≤ W := by have := hpa (a₀ * x); omega
    refine (CpEB.ite dl2 (Ct := cmFindCost hm W + permK * (W + 1) ^ 3 + 900 * (W + 20))
      (Ce := 0) (fun _ => ?_) fun h => absurd h (by omega)).mono ?_ fun _ h => h
    swap
    · unfold cmAnsCost; omega
    have hpk : permK * (k + 1) ^ 3 ≤ permK * (W + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have hm2a := wt_list2_le (encPerm a₀) (encPerm x)
    have hpa0 := hpa a₀
    refine (CpEB.letE (Cb := cmFindCost hm W + 800 * (W + 20))
      (CpEB.det dC (le_refl _) hpW (Q := fun v => v = encPerm (a₀ * x)) rfl)
      fun v hv _ => ?_).mono (by omega) fun _ h => h
    subst hv
    set env1 := env ++ [encPerm (a₀ * x)] with henv1
    have h01 : env1[0]? = some (.list [.list ks, .list [encPerm x, encGroup gs]]) := rfl
    -- the key and the cache
    have hkey : (Val.list [cmKeyV gs (a₀ * x), .list (σ.cache.map cmEntV)]).wt ≤ W := by
      have e1 := wt_list2_le (encGroup gs) (encPerm (a₀ * x))
      have e2 := wt_list2_le (cmKeyV gs (a₀ * x)) (.list (σ.cache.map cmEntV))
      have : (cmKeyV gs (a₀ * x)).wt = (Val.list [encGroup gs, encPerm (a₀ * x)]).wt := rfl
      have := hpa (a₀ * x)
      omega
    have dKey : Det Pg env1 (mk2 (mk2 (.get cmU (.nat 1)) (.var 1)) (cpKf 3))
        (.list [cmKeyV gs (a₀ * x), .list (σ.cache.map cmEntV)]) (40 * (W + 20)) := by
      have d1 := Det.mk2 (dG [encPerm (a₀ * x)]) (Det.var' (P := Pg) (env := env1) (i := 1) rfl)
      have d2 := Det.mk2 d1 (dK3 [encPerm (a₀ * x)])
      refine d2.mono ?_
      have e1 := wt_list2_le (encGroup gs) (encPerm (a₀ * x))
      have : (cmKeyV gs (a₀ * x)).wt = (Val.list [encGroup gs, encPerm (a₀ * x)]).wt := rfl
      have := cm_wt_lt_of_mem (vs := [cmKeyV gs (a₀ * x), .list (σ.cache.map cmEntV)])
        (v := cmKeyV gs (a₀ * x)) (by simp)
      have := hpa (a₀ * x)
      have : (Val.list [cmKeyV gs (a₀ * x), .list (σ.cache.map cmEntV)]).wt =
        (Val.list [.list [encGroup gs, encPerm (a₀ * x)], .list (σ.cache.map cmEntV)]).wt := rfl
      have := hkey
      omega
    have dF := Det.call dKey (cmFind_spec hm hat.find hjm gs (a₀ * x) σ.cache hkey)
    set i := σ.cache.findIdx (cmTest gs (a₀ * x)) with hi
    have hiW : (Val.nat i).wt ≤ W := by
      have h1 : i ≤ σ.cache.length := List.findIdx_le_length
      have h2 := length_lt_wt_list (σ.cache.map cmEntV)
      have h3 := wt_nat_le i
      simp only [List.length_map] at h2
      omega
    refine (CpEB.letE (Cb := 700 * (W + 20))
      (CpEB.det dF (le_refl _) hiW (Q := fun v => v = .nat i) rfl)
      fun v hv _ => ?_).mono (by have := wt_nat_le i; omega) fun _ h => h
    subst hv
    set env2 := env1 ++ [.nat i] with henv2
    have h02 : env2[0]? = some (.list [.list ks, .list [encPerm x, encGroup gs]]) := rfl
    have dK0' := cp_rdK (P := Pg) h02 hwW (j := 0) (v := par) rfl (by omega)
    have dK3' := cp_rdK (P := Pg) h02 hwW (j := 3) (v := .list (σ.cache.map cmEntV)) rfl (by omega)
    have dK4' := cp_rdK (P := Pg) h02 hwW (j := 4) (v := .list (σ.acc.map boolVal)) rfl (by omega)
    have dJ1' : Det Pg env2 (.arith .add (cpKf 1) (.nat 1)) (.nat j) (5 * (W + 20)) := by
      refine (Det.arith' (op := .add) (cp_rdK (P := Pg) h02 hwW (j := 1) (v := .nat σ.j) rfl
        (by omega)) (Det.nat 1) (z := j) (by simp [GI.Machine.BinOp.eval]; omega)).mono ?_
      have := wt_nat_le j
      omega
    have dI : Det Pg env2 (.var 2) (.nat i) (W + 1) := (Det.var' rfl).mono (by omega)
    have dLen := Det.length dK3'
    have dLt := Det.arith' (op := .lt) dI dLen
      (z := if i < (σ.cache.map cmEntV).length then 1 else 0) (by
        simp only [GI.Machine.BinOp.eval])
    have hlenW : (σ.cache.map cmEntV).length ≤ W := by
      have := length_lt_wt_list (σ.cache.map cmEntV); omega
    by_cases hhit : i < σ.cache.length
    · -- a hit
      rw [if_pos hhit, if_pos hhit] at hch
      have hhit' : i < (σ.cache.map cmEntV).length := by simpa using hhit
      rw [if_pos hhit'] at dLt
      set a' := (σ.cache.getD i ([], 1)).2 with ha'
      have hw' := hnew (some a') σ.cache le_self_add hlen
      have hgv : (σ.cache.map cmEntV)[i]? = some (cmEntV (σ.cache.getD i ([], 1))) := by
        rw [List.getD_eq_getElem _ _ hhit]; simp [hhit]
      have hentW : (cmEntV (σ.cache.getD i ([], 1))).wt ≤ W := by
        have := cm_wt_lt_of_mem (vs := σ.cache.map cmEntV) (v := cmEntV (σ.cache.getD i ([], 1)))
          (List.mem_of_getElem? hgv)
        omega
      have dEnt := Det.get' dK3' dI hgv
      have dEnt' : Det Pg env2 (.get (cpKf 3) (.var 2))
          (.list [encGroup (σ.cache.getD i ([], 1)).1, encPerm a']) _ := dEnt
      have dRep := Det.mk1 (Det.get' dEnt' (Det.nat 1) rfl)
      have hrep : (Val.list [encPerm a']).wt ≤ W := by
        have := wt_list_le [encPerm a']
        have := hpa a'
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at *
        omega
      have hσW : ((⟨j, some a', σ.cache, acc, 1⟩ : CmSt k).val par).wt ≤ W := by
        have := cm_wt_lt_of_mem (vs := [(⟨j, some a', σ.cache, acc, 1⟩ : CmSt k).val par, .list []])
          (v := (⟨j, some a', σ.cache, acc, 1⟩ : CmSt k).val par) (by simp)
        omega
      have dl := cp_mkList' (P := Pg) (env := env2) (W := W) (c := 20 * (W + 20))
        [(cpKf 0, par), (.arith .add (cpKf 1) (.nat 1), .nat j),
          (mk1 (.get (.get (cpKf 3) (.var 2)) (.nat 1)), cmOV (some a')),
          (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
          (.nat 1, .nat 1)] (v := (⟨j, some a', σ.cache, acc, 1⟩ : CmSt k).val par)
        (by rw [hval]; rfl) (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact dK0'.mono (by omega)
          · exact dJ1'.mono (by omega)
          · refine dRep.mono ?_
            have := hpa a'
            omega
          · exact dK3'.mono (by omega)
          · exact dK4'.mono (by omega)
          · exact (Det.nat 1).mono (by omega)) hσW
      refine (CpEB.ite dLt (Ct := 6 * (20 * (W + 20) + W + 1) + 5 + 2 * W + 100) (Ce := 0)
        (fun _ => ?_) fun h => absurd h one_ne_zero).mono ?_ fun _ h => h
      · refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega)
          fun w hw => ?_
        subst hw
        exact Or.inr ⟨_, cm_pend_rep hmeq hmf hM hc hF hlen hdrop hjn hch hw', rfl⟩
      · have := wt_nat_le (if i < (σ.cache.map cmEntV).length then 1 else 0)
        rw [if_pos hhit'] at this
        omega
    · -- a miss
      rw [if_neg hhit, if_neg hhit] at hch
      have hhit' : ¬ i < (σ.cache.map cmEntV).length := by simpa using hhit
      rw [if_neg hhit'] at dLt
      have hlen' : ∀ p ∈ σ.cache ++ [(gs, a₀ * x)], p.1.length ≤ (k + L.q) ^ 2 := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hlen p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact hgl'
      have hw' := hnew (some (a₀ * x)) (σ.cache ++ [(gs, a₀ * x)]) (by simp) hlen'
      set σ' : CmSt k := ⟨j, some (a₀ * x), σ.cache ++ [(gs, a₀ * x)], acc, 1⟩ with hσ'
      have hσW : (σ'.val par).wt < Bw := by
        have := cm_wt_lt_of_mem (vs := [σ'.val par, .list []]) (v := σ'.val par) (by simp)
        omega
      have hcW : (Val.list (σ.cache.map cmEntV ++ [cmEntV (gs, a₀ * x)])).wt < Bw := by
        have := cm_wt_lt_of_mem (vs := [par, .nat j, cmOV (some (a₀ * x)),
          .list ((σ.cache ++ [(gs, a₀ * x)]).map cmEntV), .list (σ.acc.map boolVal), .nat 1])
          (v := .list ((σ.cache ++ [(gs, a₀ * x)]).map cmEntV)) (by simp)
        rw [← hval, List.map_append] at this
        exact lt_trans (by simpa using this) hσW
      have dV1 : Det Pg env2 (.var 1) (encPerm (a₀ * x)) (W + 1) :=
        (Det.var' rfl).mono (by omega)
      have dRep := Det.mk1 dV1
      have hrep : (Val.list [encPerm (a₀ * x)]).wt ≤ W := by
        have := wt_list_le [encPerm (a₀ * x)]
        have := hpa (a₀ * x)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at *
        omega
      have dNew := Det.snoc dK3' (Det.mk2 (dG [encPerm (a₀ * x), .nat i]) dV1)
      have dNew' : Det Pg env2 (.snoc (cpKf 3) (mk2 (.get cmU (.nat 1)) (.var 1)))
          (.list (σ.cache.map cmEntV ++ [cmEntV (gs, a₀ * x)])) _ := dNew
      have hkv : (Val.list [encGroup gs, encPerm (a₀ * x)]).wt ≤ W := by
        have := wt_list2_le (encGroup gs) (encPerm (a₀ * x))
        have := hpa (a₀ * x)
        omega
      have dl := cp_mkList' (P := Pg) (env := env2) (W := W) (c := 20 * (W + 20))
        [(cpKf 0, par), (.arith .add (cpKf 1) (.nat 1), .nat j),
          (mk1 (.var 1), cmOV (some (a₀ * x))),
          (.snoc (cpKf 3) (mk2 (.get cmU (.nat 1)) (.var 1)),
            .list (σ.cache.map cmEntV ++ [cmEntV (gs, a₀ * x)])),
          (cpKf 4, .list (σ.acc.map boolVal)), (.nat 1, .nat 1)] (v := σ'.val par)
        (by rw [hσ', hval, List.map_append]; rfl) (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact dK0'.mono (by omega)
          · exact dJ1'.mono (by omega)
          · exact dRep.mono (by omega)
          · refine dNew'.mono ?_
            have : (Val.list (σ.cache.map cmEntV ++ [cmEntV (gs, a₀ * x)])).wt =
              (Val.list (σ.cache.map cmEntV ++ [.list [encGroup gs, encPerm (a₀ * x)]])).wt := rfl
            omega
          · exact dK4'.mono (by omega)
          · exact (Det.nat 1).mono (by omega)) (by omega)
      refine (CpEB.ite dLt (Ct := 0) (Ce := 6 * (20 * (W + 20) + W + 1) + 5 + 2 * W + 100)
        (fun h => absurd rfl h) fun _ => ?_).mono ?_ fun _ h => h
      · refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega)
          fun w hw => ?_
        subst hw
        exact Or.inr ⟨_, cm_pend_rep hmeq hmf hM hc hF hlen hdrop hjn hch hw', rfl⟩
      · have := wt_nat_le (if i < (σ.cache.map cmEntV).length then 1 else 0)
        rw [if_neg hhit'] at this
        omega

end Ans

end GI.Impl
