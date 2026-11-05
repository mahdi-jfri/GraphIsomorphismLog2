module

public import Workspace.Impl.AggCmpProg
public import Workspace.Impl.AggCertMvEnd

@[expose] public section

/-!
# The move program: stage `j` without a call

`cm_stage_spec`: from a program state at stage `j` of a pair (`fl = 1`), the function `cmStageF`
returns what a move must return (`CmMvPost`): at `j = n` the end of the pair
(`cm_stage_end_rep`), for an empty coset the next stage (`cm_stage_none_rep`), and otherwise
whatever the call function at `b + 4` returns (a hypothesis here).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

section Post

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} (Cs : Set (Aggregation P₀ S L.toGiantLabels))
  (Ag₀ : Aggregation P₀ S L.toGiantLabels) (O : TestTupleOrder L.q P₀.κ)
  (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **What a move returns**: what the step returns, or `[2, st']` for a program state `st'` of
smaller measure that stands for a subset of the candidates. -/
def CmMvPost (par : Val) (Out : List Bool → Val → Prop) (Bw M₀ m : ℕ)
    (Ss : Set (Script (List Bool))) (f : ℕ) (w : Val) : Prop :=
  Iface.StepPostC (measure P₀ .giant S) Out
      (fun st Ss f => ∃ m, CmRep e par Cs Ag₀ O πd Bw M₀ m st Ss f) Ss f w ∨
    ∃ st', CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m Ss f st' ∧
      w = .list [.nat 2, st']

end Post

/-! ### Reading the program state -/

section Read

variable {k : ℕ}

/-- The entries of `kst`. -/
def CmSt.vals (par : Val) (σ : CmSt k) : List Val :=
  [par, .nat σ.j, cmOV σ.o, .list (σ.cache.map cmEntV), .list (σ.acc.map boolVal), .nat σ.fl]

theorem CmSt.val_eq (par : Val) (σ : CmSt k) : σ.val par = .list (σ.vals par) := rfl

theorem cm_oV_length (o : Option (Perm (Fin k))) :
    ∃ l, cmOV o = .list l ∧ boolVal o.isSome = .nat l.length := by
  rcases o with _ | a
  · exact ⟨[], rfl, rfl⟩
  · exact ⟨[encPerm a], rfl, rfl⟩

theorem cm_wt_nil_le : (Val.list []).wt ≤ ansW k := by
  have := wt_list_le ([] : List Val)
  simp only [List.map_nil, List.sum_nil, List.length_nil] at this
  unfold ansW
  omega

end Read

section Stage

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

set_option maxHeartbeats 2000000 in
/-- **Stage `j` without a call.** -/
theorem cm_stage_spec {Pg : Program} {b jm : ℕ} (hat : CmMvAt0 Pg b jm)
    {sv : Val} {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)}
    {Out : List Bool → Val → Prop} {M₀ Bw W : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)).wt k L.q M₀
      (O.tuples.length * O.tuples.length) ≤ Bw) (hW : 100 * Bw + 1000 ≤ W)
    {m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ} {ps' : List (CmPair L.q P₀.κ)} {j : ℕ}
    {o : Option (Perm S.dom)} {σ : CmSt k} {ents : List (CmEnt S.dom)}
    {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pos (.stage acc ab ps' j o) : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pos (.stage acc ab ps' j o) : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hfl : σ.fl = 1) (hacc : σ.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps')
    (hσj : σ.j = j) (hjn : j ≤ Fintype.card S.dom) (ho : CmOK e σ.o o) {u : Val}
    (hwt : (Val.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u]).wt ≤ Bw)
    {Ccall : ℕ}
    (hcall : j < Fintype.card S.dom → σ.o ≠ none →
      CpFB Pg (b + 4) (.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u])
        W Ccall (CmMvPost e Cs Ag₀ O πd (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom))
          Out Bw M₀ m ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
            (.pos (.stage acc ab ps' j o))) '' CmCands Cs Ag₀ O rec) f)) :
    CpFB Pg (b + 2) (.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u])
      W (Ccall + 200 * (W + 20))
      (CmMvPost e Cs Ag₀ O πd (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Out Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
          (.pos (.stage acc ab ps' j o))) '' CmCands Cs Ag₀ O rec) f) := by
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  set ks := σ.vals par with hks
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  have hp0 : ks[0]? = some (.list [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
    .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), .list (O.tuples.map stTT),
    .nat (Fintype.card S.dom), .nat O.tuples.length]) := rfl
  -- the pair index is below `N²`, so one more result fits
  have hlt : acc.length < O.tuples.length * O.tuples.length := by
    by_contra hh
    rw [cm_pairs_drop_end O (by omega)] at hdrop
    simp at hdrop
  have hk : Fintype.card S.dom ≤ k := cp_card_dom_le e
  have hkW : k + 1 ≤ W := by
    have h1 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have h2 : cmBw par.wt k L.q M₀ (O.tuples.length * O.tuples.length) ≤ Bw := hBw
    unfold cmBw ansW at h2
    omega
  refine CpFB.intro hat.stage ?_
  rw [hsv]
  unfold cmStageF
  have dj := cp_rdK (P := Pg) (h0 []) hwW (j := 1) (v := .nat σ.j) rfl (by omega)
  have dn := cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 7) (v := .nat (Fintype.card S.dom)) rfl
    (by omega)
  by_cases hjE : σ.j = Fintype.card S.dom
  · -- the end of the pair
    have dc := Det.arith' (op := .eq) dj dn (z := 1) (by simp only [GI.Machine.BinOp.eval, hjE, ite_true])
    obtain ⟨l, hl, hb⟩ := cm_oV_length σ.o
    set σ' : CmSt k := { σ with acc := σ.acc ++ [σ.o.isSome], fl := 0 } with hσ'
    have hw' : (Val.list [σ'.val par, .list []]).wt ≤ Bw := by
      refine le_trans (cm_wt_state (q := L.q) (M₀ := M₀) (L := O.tuples.length * O.tuples.length)
        ?_ ?_ ?_ hlen ?_ ?_) hBw
      · show σ.j ≤ k; omega
      · show 0 ≤ 2; omega
      · show σ.cache.length ≤ M₀; omega
      · show (σ.acc ++ [σ.o.isSome]).length ≤ _; rw [hacc]; simp; omega
      · exact cm_wt_nil_le
    have hv : σ'.val par = .list [par, .nat σ.j, cmOV σ.o, .list (σ.cache.map cmEntV),
        .list (σ.acc.map boolVal ++ [.nat l.length]), .nat 0] := by
      rw [CmSt.val, ← hb]; simp [hσ']
    have dacc := cp_rdK (P := Pg) (h0 []) hwW (j := 4) (v := .list (σ.acc.map boolVal)) rfl
      (by omega)
    have doV := cp_rdK (P := Pg) (h0 []) hwW (j := 2) (v := cmOV σ.o) rfl (by omega)
    rw [hl] at doV
    have dsn := Det.snoc dacc (Det.length doV)
    have hsW : (Val.list (σ.acc.map boolVal ++ [.nat l.length])).wt ≤ W := by
      have h1 : (Val.list (σ.acc.map boolVal ++ [.nat l.length])).wt < (σ'.val par).wt := by
        rw [hv]; exact wt_le_wt_list (by simp)
      have h2 : (σ'.val par).wt < (Val.list [σ'.val par, .list []]).wt := wt_le_wt_list (by simp)
      omega
    have hlW : l.length ≤ W := by
      have h1 := length_lt_wt_list l
      have h2 : (cmOV σ.o).wt < (Val.list ks).wt := wt_le_wt_list (by simp [hks, CmSt.vals])
      have h3 : (Val.list ks).wt < (Val.list [.list ks, u]).wt := wt_le_wt_list (by simp)
      rw [hl] at h2
      omega
    have hks' : (Val.list ks).wt ≤ W := by
      have : (Val.list ks).wt < (Val.list [.list ks, u]).wt := wt_le_wt_list (by simp)
      omega
    have dl := cp_mkList' (P := Pg) (env := [.list [.list ks, u]]) (W := W) (c := 10 * (W + 20))
      [(cpKf 0, par), (cpKf 1, .nat σ.j), (cpKf 2, cmOV σ.o), (cpKf 3, .list (σ.cache.map cmEntV)),
        (.snoc (cpKf 4) (.length (cpKf 2)), .list (σ.acc.map boolVal ++ [.nat l.length])),
        (.nat 0, .nat 0)] (v := σ'.val par) (by rw [hv]; rfl) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (cp_rdK (h0 []) hwW (j := 0) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (h0 []) hwW (j := 1) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (h0 []) hwW (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (h0 []) hwW (j := 3) rfl (by omega)).mono (by omega)
      · exact dsn.mono (by omega)
      · exact (Det.nat 0).mono (by omega))
      (by
        have : (σ'.val par).wt < (Val.list [σ'.val par, .list []]).wt := wt_le_wt_list (by simp)
        omega)
    have dr := Det.mk2 (Det.nat (P := Pg) (env := [.list [.list ks, u]]) 2)
      (Det.mk2 dl (Det.nil (P := Pg) (env := [.list [.list ks, u]])))
    refine CpEB.det (Det.ite_pos dc one_ne_zero dr) ?_ ?_ ?_
    · have h1 := wt_list2_le (σ'.val par) (.list [])
      have h2 := wt_list2_le (.nat 2) (.list [σ'.val par, .list []])
      have h3 := wt_nat_le 2
      simp only [List.length_cons, List.length_nil] at *
      omega
    · have h2 := wt_list2_le (.nat 2) (.list [σ'.val par, .list []])
      have h3 := wt_nat_le 2
      omega
    · refine Or.inr ⟨_, ?_, rfl⟩
      have hjn' : j = Fintype.card S.dom := by omega
      subst hjn'
      exact cm_stage_end_rep hm hmf hM hc hF hlen hacc hdrop ho hw'
  · have dc := Det.arith' (op := .eq) dj dn (z := 0) (by simp only [GI.Machine.BinOp.eval, hjE, if_false])
    have hjlt : j < Fintype.card S.dom := by omega
    obtain ⟨l, hl, -⟩ := cm_oV_length σ.o
    have doV := cp_rdK (P := Pg) (h0 []) hwW (j := 2) (v := cmOV σ.o) rfl (by omega)
    rw [hl] at doV
    have dlen := Det.length doV
    have hlW : l.length ≤ W := by
      have h1 := length_lt_wt_list l
      have h2 : (cmOV σ.o).wt < (Val.list ks).wt := wt_le_wt_list (by simp [hks, CmSt.vals])
      have h3 : (Val.list ks).wt < (Val.list [.list ks, u]).wt := wt_le_wt_list (by simp)
      rw [hl] at h2
      omega
    refine (CpEB.ite dc (Ct := 0) (Ce := Ccall + 150 * (W + 20)) (fun h => absurd rfl h)
      fun _ => ?_).mono (by omega) fun _ h => h
    rcases hσo : σ.o with _ | a
    · -- an empty coset
      rw [hσo] at hl
      simp only [cmOV] at hl
      cases hl
      have hoN : o = none := by rw [hσo] at ho; rcases o with _ | g <;> simp_all [CmOK]
      subst hoN
      set σ' : CmSt k := { σ with j := σ.j + 1 } with hσ'
      have hw' : (Val.list [σ'.val par, .list []]).wt ≤ Bw := by
        refine le_trans (cm_wt_state (q := L.q) (M₀ := M₀) (L := O.tuples.length * O.tuples.length)
          ?_ ?_ ?_ hlen ?_ ?_) hBw
        · show σ.j + 1 ≤ k; omega
        · show σ.fl ≤ 2; omega
        · show σ.cache.length ≤ M₀; omega
        · show σ.acc.length ≤ _; rw [hacc]; omega
        · exact cm_wt_nil_le
      have hv : σ'.val par = .list [par, .nat (σ.j + 1), cmOV σ.o, .list (σ.cache.map cmEntV),
          .list (σ.acc.map boolVal), .nat σ.fl] := rfl
      have dl := cp_mkList' (P := Pg) (env := [.list [.list ks, u]]) (W := W) (c := 10 * (W + 20))
        [(cpKf 0, par), (.arith .add (cpKf 1) (.nat 1), .nat (σ.j + 1)), (cpKf 2, cmOV σ.o),
          (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
          (cpKf 5, .nat σ.fl)] (v := σ'.val par) (by rw [hv]; rfl) (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (cp_rdK (h0 []) hwW (j := 0) rfl (by omega)).mono (by omega)
        · refine (Det.arith' (op := .add) (cp_rdK (h0 []) hwW (j := 1) rfl (by omega)) (Det.nat 1)
            (z := σ.j + 1) rfl).mono ?_
          have := wt_nat_le (σ.j + 1)
          omega
        · exact (cp_rdK (h0 []) hwW (j := 2) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (h0 []) hwW (j := 3) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (h0 []) hwW (j := 4) rfl (by omega)).mono (by omega)
        · exact (cp_rdK (h0 []) hwW (j := 5) rfl (by omega)).mono (by omega))
        (by
          have : (σ'.val par).wt < (Val.list [σ'.val par, .list []]).wt := wt_le_wt_list (by simp)
          omega)
      have dr := Det.mk2 (Det.nat (P := Pg) (env := [.list [.list ks, u]]) 2)
        (Det.mk2 dl (Det.nil (P := Pg) (env := [.list [.list ks, u]])))
      have dz : Det Pg [.list [.list ks, u]] (.length (cpKf 2)) (.nat 0)
          (3 * (W + 20) + 0 + 3) := dlen
      refine CpEB.det (Det.ite_zero dz dr) ?_ ?_ ?_
      · have h1 := wt_list2_le (σ'.val par) (.list [])
        have h2 := wt_list2_le (.nat 2) (.list [σ'.val par, .list []])
        have h3 := wt_nat_le 2
        simp only [List.length_cons, List.length_nil] at *
        omega
      · have h2 := wt_list2_le (.nat 2) (.list [σ'.val par, .list []])
        have h3 := wt_nat_le 2
        omega
      · refine Or.inr ⟨_, ?_, rfl⟩
        exact cm_stage_none_rep hjlt hm hmf hM hc hF hlen hfl hacc hdrop hσj hσo hw'
    · -- the call
      rw [hσo] at hl
      simp only [cmOV] at hl
      cases hl
      have dz : Det Pg [.list [.list ks, u]] (.length (cpKf 2)) (.nat 1)
          (3 * (W + 20) + 1 + 3) := dlen
      refine (CpEB.ite dz (Ct := Ccall + 140 * (W + 20)) (Ce := 0) (fun _ => ?_)
        fun h => absurd h one_ne_zero).mono (by omega) fun _ h => h
      refine (CpEB.call (Cb := Ccall) (CpEB.det (Det.rv (P := Pg)
        (env := [.list [.list ks, u]]) (i := 0) rfl hwW) le_rfl hwW
        (Q := fun v => v = .list [.list ks, u]) rfl) fun v hv _ => ?_).mono (by omega)
        fun _ h => h
      subst hv
      rw [← hsv]
      exact hcall hjlt (by rw [hσo]; exact Option.some_ne_none a)

end Stage

end GI.Impl
