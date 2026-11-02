import Workspace.Impl.AggCertFzLoop

/-!
# The graph forms of the certificate groups: the whole program

`cp_fz_spec`: on `[par, out, s]`, where `par` is the parent data of the certificate phase and
`out` the output of its runner, `cpFzFuns` returns a graph form of the lift of the certificate
group `F_z` (`z = x` for `s = 0`, `z = y` for `s = 1`), with at most `(k + q)²` pairs, at cost at
most `cpFzB W`.

The steps: the graph form of `G_(dom)` starts the list of pairs (`cp_pairGens_ker`); the loop over
the test sets keeps `CpFzInv` (`cp_fz_step`); at the end the first parts generate the lift of
`F_z` on positions (`cp_fz_final`), and the closure call turns them into the graph form
(`cp_pairGens_clos`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The budget of the program. -/
noncomputable def cpFzB (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) : ℕ :=
  W * cpFzStepB hst hpre hm W + 3 * cpG hst hpre hm W + 3000 * (W + 1) ^ 2 + 300 * (W + 20)

/-- The weight bound that the program asks: the input weight `B`, the number `NT` of test sets
and `D`. -/
def cpFzW (k q B NT D : ℕ) : ℕ :=
  20 * (B + NT + 50 * (NT + 1) * (k + q + 1) ^ 4 + 10) + 10 ^ 10 * (k + q + 1) ^ 12 + D

section Spec

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {col : C → ℕ} {S : State Ω C}
  [Fintype S.dom] {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- A graph form with at most `n (k + q)²` pairs. -/
theorem cp_wt_gpN {q n : ℕ} {ps : GPairs k q} (h : ps.length ≤ n * (k + q) ^ 2) :
    (gpV ps).wt ≤ 50 * n * (k + q + 1) ^ 4 + 4 := by
  obtain ⟨h1, h2, -, -, -, e4, -⟩ := cp_pow_facts k q
  have := cp_wt_list (vs := ps.map pairV) (n := n * (k + q + 1) ^ 2) (c := 22 * (k + q + 1) ^ 2)
    (by simp only [List.length_map]; exact h.trans (Nat.mul_le_mul_left _ h2)) (by
      simp only [List.mem_map]; rintro _ ⟨p, -, rfl⟩; exact wt_pairV_le p)
  have a : n * (k + q + 1) ^ 2 * (2 * (22 * (k + q + 1) ^ 2) + 1) ≤
      n * (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have b : n * (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) = 45 * n * (k + q + 1) ^ 4 := by
    rw [← e4]; ring
  have c : 45 * n * (k + q + 1) ^ 4 ≤ 50 * n * (k + q + 1) ^ 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  unfold gpV
  omega

/-- The first parts of a graph form with at most `n (k + q)²` pairs. -/
theorem cp_wt_fstN {q n : ℕ} {ps : GPairs k q} (h : ps.length ≤ n * (k + q) ^ 2) :
    (Val.list ((ps.map Prod.fst).map encPerm)).wt ≤ 50 * n * (k + q + 1) ^ 4 + 4 := by
  obtain ⟨h1, h2, h3, -, -, e4, -⟩ := cp_pow_facts k q
  have := cp_wt_list (vs := (ps.map Prod.fst).map encPerm) (n := n * (k + q + 1) ^ 2)
    (c := 4 * (k + q + 1) ^ 2)
    (by simp only [List.length_map]; exact h.trans (Nat.mul_le_mul_left _ h2)) (by
      simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩
      have := wt_encPerm_le a; omega)
  have a : n * (k + q + 1) ^ 2 * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤
      n * (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have b : n * (k + q + 1) ^ 2 * (45 * (k + q + 1) ^ 2) = 45 * n * (k + q + 1) ^ 4 := by
    rw [← e4]; ring
  have c : 45 * n * (k + q + 1) ^ 4 ≤ 50 * n * (k + q + 1) ^ 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

set_option maxHeartbeats 4000000 in
/-- **The graph form of the lift of `F_z`.** -/
theorem cp_fz_spec {Pg : Program} {f b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hfz : CpFzAt Pg f b) (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e col S L πd sv gp osA D)
    {res : List (GPairs k L.q × GPairs k L.q)}
    {logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))}
    (hin : CpFzIn e S L πd res logs) {s : ℕ} (hs : s ≤ 1) {W : ℕ}
    (hW : cpFzW k L.q (Val.list [cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA),
      cpOutV res logs, .nat s]).wt logs.length D ≤ W) :
    CpFB Pg f (.list [cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA),
      cpOutV res logs, .nat s]) W (cpFzB hst hpre hm W)
      (fun w => ∃ fz : GPairs k L.q, w = gpV fz ∧ fz.length ≤ (k + L.q) ^ 2 ∧
        PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S (cpSel s S.x S.y)))) fz) := by
  obtain ⟨osL, hnd, hall, hosA⟩ := ctx.hosA
  have hosL : osL.length ≤ k := cp_os_length_le e hnd
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  set z := cpSel s S.x S.y with hz
  set NT := logs.length with hNT
  set B := Val.list [par, cpOutV res logs, .nat s] with hB
  have hrl : res.length = NT := hin.length
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k L.q
  have w12 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w12' : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW' : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W := by unfold cpFzW at hW; omega
  -- the reads
  set pvs : List Val := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)] with hpvs
  have ep : (Val.list pvs).wt = par.wt := rfl
  have eB : (Val.list [par, cpOutV res logs, .nat s]).wt = B.wt := rfl
  have hpB : par.wt < B.wt := cp_wt_get (vs := [par, cpOutV res logs, .nat s]) (j := 0) rfl
  have hoB : (cpOutV res logs).wt < B.wt :=
    cp_wt_get (vs := [par, cpOutV res logs, .nat s]) (j := 1) rfl
  have hkqw : (Val.list [.nat k, .nat L.q]).wt < par.wt := cp_wt_get (vs := pvs) (j := 1) rfl
  have hgpw : (gpV gp).wt < par.wt := cp_wt_get (vs := pvs) (j := 2) rfl
  have hosw : (encPts osA).wt < par.wt := cp_wt_get (vs := pvs) (j := 5) rfl
  have h0o : (Val.list (res.map resV)).wt < (cpOutV res logs).wt :=
    cp_wt_get (vs := [.list (res.map resV), .list (logs.map cpLogV)]) (j := 0) rfl
  have eo : (Val.list [.list (res.map resV), .list (logs.map cpLogV)]).wt =
    (cpOutV res logs).wt := rfl
  have gP := fun rest : List Val => Det.get' (Det.arg' (P := Pg) (vs := [par, cpOutV res logs,
    .nat s]) (rest := rest) (j := 0) (v := .list pvs) rfl) (Det.nat 1)
    (v := .list [.nat k, .nat L.q]) rfl
  have gG := fun rest : List Val => Det.get' (Det.arg' (P := Pg) (vs := [par, cpOutV res logs,
    .nat s]) (rest := rest) (j := 0) (v := .list pvs) rfl) (Det.nat 2) (v := gpV gp) rfl
  have gO := fun rest : List Val => Det.get' (Det.arg' (P := Pg) (vs := [par, cpOutV res logs,
    .nat s]) (rest := rest) (j := 0) (v := .list pvs) rfl) (Det.nat 5) (v := encPts osA) rfl
  have w1 : 1 ≤ (k + L.q + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have enil : (Val.list []).wt = 4 := wt_list_nil
  have hY : 50 * (NT + 1) * (k + L.q + 1) ^ 4 = 50 * ((NT + 1) * (k + L.q + 1) ^ 4) := by ring
  have hR : ∀ x : ℕ, x ≤ 100 * B.wt + 3 * D + 1000 * (k + L.q + 1) ^ 12 +
      1000 * ((NT + 1) * (k + L.q + 1) ^ 4) + 200 →
      x ≤ 40 * (W + 20) := fun x hx => by
    unfold cpFzW at hW; omega
  -- the kernel `G_(dom)`
  have dK := Det.mk3 (gP []) (gG []) (gO [])
  have w3k := wt_list3_le (.list [.nat k, .nat L.q]) (gpV gp) (encPts osA)
  have hK := CpEB.call (W := W) (CpEB.det dK (hR _ (by omega)) (by unfold cpFzW at hW; omega)
      (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV gp, encPts osA]) rfl)
    fun v hv _ => by
      subst hv
      exact cp_bud_stabP hst hpre hm hat.stab hjp ctx.hgpl
        (by rw [hosA, List.length_map]; omega) hW'
  -- the loop
  have hI : ∀ qk : GPairs k L.q, qk.length ≤ (k + L.q) ^ 2 →
      Subgroup.closure {p | p ∈ qk} = Subgroup.closure {p | p ∈ gp} ⊓ fixPts k L.q osA →
      CpEB Pg [B, gpV qk] (.call (f + 1) (mk3 (.var 0) (.length (.get (arg 1) (.nat 0))) (.var 1)))
        W (40 * (W + 20) + (W * cpFzStepB hst hpre hm W + 3000 * (W + 1) ^ 2) + W + 1)
        (CpFzInv e S L πd logs z NT) := by
    intro qk hql hqcl
    have hker : PairGens e L (S.liftGroup ⊥) qk :=
      cp_pairGens_ker ctx.hgp hall (by rw [hqcl, hosA])
    have dL := Det.length (Det.get' (Det.arg' (P := Pg) (vs := [par, cpOutV res logs, .nat s])
      (rest := [gpV qk]) (j := 1) (v := .list [.list (res.map resV), .list (logs.map cpLogV)])
      rfl) (Det.nat 0) (v := .list (res.map resV)) rfl)
    have dIn := Det.mk3 (Det.var' (P := Pg) (env := [B, gpV qk]) (i := 0) rfl) dL
      (Det.var' (P := Pg) (env := [B, gpV qk]) (i := 1) rfl)
    rw [List.length_map, hrl] at dIn
    have hqkw := cp_wt_gp hql
    have hnw := wt_nat_le NT
    have hNTB : NT ≤ B.wt := by
      have := length_lt_wt_list (res.map resV)
      rw [List.length_map, hrl] at this; omega
    have w3i := wt_list3_le B (.nat NT) (gpV qk)
    have hM : ∀ i acc, i ≤ NT → CpFzInv e S L πd logs z i acc →
        acc.wt ≤ 50 * (NT + 1) * (k + L.q + 1) ^ 4 + 4 := by
      rintro i _ hi ⟨qs, rfl, hl, -, -⟩
      exact (cp_wt_gpN (hl.trans (Nat.mul_le_mul_right ((k + L.q) ^ 2)
        (show i + 1 ≤ NT + 1 by omega)))).trans
        (by have := Nat.mul_le_mul_right ((k + L.q + 1) ^ 4)
              (Nat.mul_le_mul_left 50 (show i + 1 ≤ NT + 1 by omega)); omega)
    have hit := iter_spec hfz.iter (c := B) (k := NT) (acc0 := gpV qk)
      (Inv := CpFzInv e S L πd logs z) (M := 50 * (NT + 1) * (k + L.q + 1) ^ 4 + 4)
      (B := fun _ => cpFzStepB hst hpre hm W)
      ⟨qk, rfl, by omega, fun p hp => cp_fst_mem_G hker hp,
        by rw [cp_gens_lift hker, cpFzGrp_zero]⟩ hM
      (fun i acc hi hacc => by
        have hw := hM i acc hi.le hacc
        have w3 := wt_list3_le B (.nat i) acc
        have := wt_nat_le i
        exact FunAll.mono (cp_fz_step hst hpre hm hat hfz hjp ctx hin hs hi hacc
          (by change 10 * (Val.list [B, .nat i, acc]).wt + 10 ^ 10 * (k + L.q + 1) ^ 12 + D ≤ W
              unfold cpFzW at hW; omega)) fun w c h => ⟨h.1, h.2.2⟩)
    refine CpEB.call (CpEB.det dIn (hR _ (by omega)) (by unfold cpFzW at hW; omega)
      (Q := fun v => v = .list [B, .nat NT, gpV qk]) rfl) fun v hv _ => ?_
    subst hv
    refine FunAll.mono hit fun w c h => ⟨h.1, (hM _ _ le_rfl h.1).trans
      (by unfold cpFzW at hW; omega), ?_⟩
    have h2 := h.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have hNW : NT ≤ W := by unfold cpFzW at hW; omega
    have a1 : NT * cpFzStepB hst hpre hm W ≤ W * cpFzStepB hst hpre hm W :=
      Nat.mul_le_mul_right _ hNW
    have a2 : loopModK * (NT + 1) * ((Val.list [B, .nat NT, gpV qk]).wt + NT +
        (50 * (NT + 1) * (k + L.q + 1) ^ 4 + 4) + 1) ≤ 1000 * (W + 1) * (3 * (W + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by unfold cpFzW at hW; omega)
    have a3 : 1000 * (W + 1) * (3 * (W + 1)) = 3000 * (W + 1) ^ 2 := by ring
    have e1 : loopModK = 1000 := rfl
    omega
  -- the first parts and the closure
  have hTs : ∀ T, T ∈ logs.map Prod.fst ↔ T.card = P₀.κ := by
    obtain ⟨O, hO⟩ := hin.ord
    intro T; rw [hO]; exact O.mem T
  have hEnd : ∀ qk qF : GPairs k L.q, qF.length ≤ (NT + 1) * (k + L.q) ^ 2 →
      (∀ p ∈ qF, ∃ g ∈ S.G, toFin e g = p.1) →
      gens (qF.map Prod.fst) = (S.liftGroup (certGroup S πd P₀.κ (dstr S z))).map
        (toFin e).toMonoidHom →
      CpEB Pg [B, gpV qk, gpV qF] (.letE (.call (cpMapFst b) (mk2 (.nat 0) (.var 2)))
          (.call (cpClos b) (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.var 3)))) W
        ((40 * (W + 20) + cpG hst hpre hm W + W + 1) +
          (40 * (W + 20) + cpG hst hpre hm W + W + 1) + W + 1)
        (fun w => ∃ fz : GPairs k L.q, w = gpV fz ∧ fz.length ≤ (k + L.q) ^ 2 ∧
          PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S z))) fz) := by
    intro qk qF hql hmem hgens
    set ms := qF.map Prod.fst with hms
    have hqFw := cp_wt_gpN hql
    have hmsw := cp_wt_fstN hql
    have ems : (Val.list (ms.map encPerm)).wt = (Val.list ((qF.map Prod.fst).map encPerm)).wt := by
      rw [hms]
    have hNW : NT ≤ W := by unfold cpFzW at hW; omega
    have hqFl : qF.length ≤ W := by
      have : (NT + 1) * (k + L.q) ^ 2 ≤ (NT + 1) * (k + L.q + 1) ^ 4 :=
        Nat.mul_le_mul_left _ (f2.trans f24)
      unfold cpFzW at hW; omega
    have dF := Det.mk2 (Det.nat (P := Pg) (env := [B, gpV qk, gpV qF]) 0)
      (Det.var' (P := Pg) (env := [B, gpV qk, gpV qF]) (i := 2) rfl)
    have w2f := wt_list2_le (.nat 0) (gpV qF)
    have := wt_nat_le 0
    have hF := mapList_spec hat.mapFst qF pairV (fun p => encPerm p.1) (c := .nat 0)
      (B := 300 * (k + L.q + 1) ^ 2) (fun a _ a' _ he => by rw [pairV_injective he])
      (fun p _ => krFst_step hat.fstF p)
    have hFo : (qF.map fun p => encPerm p.1) = ms.map encPerm := by rw [hms, List.map_map]; rfl
    rw [hFo] at hF
    have hbF : CpFB Pg (cpMapFst b) (.list [.nat 0, gpV qF]) W (cpG hst hpre hm W)
        (fun v => v = .list (ms.map encPerm)) := by
      have ePv : (Val.list [.nat 0, .list (qF.map pairV)]).wt = (Val.list [.nat 0, gpV qF]).wt :=
        rfl
      refine CpFB.det hF ?_ (by unfold cpFzW at hW; omega) rfl
      have c1 : qF.length * (300 * (k + L.q + 1) ^ 2) ≤ (W + 1) * (300 * (W + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have c2 : mapK * (qF.length + 1) * ((Val.list [.nat 0, .list (qF.map pairV)]).wt +
          (Val.list (ms.map encPerm)).wt + 1) ≤ 1000 * (W + 1) * (W + 1) := by
        have hmk : mapK = 1000 := rfl
        rw [hmk]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by unfold cpFzW at hW; omega)
      have c3 : (W + 1) * (300 * (W + 1)) + 1000 * (W + 1) * (W + 1) = 1300 * (W + 1) ^ 2 := by
        ring
      have hp := cp_poly_le (W := W) (K := 1300) (d := 2) (by norm_num) (by norm_num)
        (by omega)
      have := cpG_poly hst hpre hm (W := W)
      omega
    refine CpEB.letE (CpEB.call (CpEB.det dF (hR _ (by omega)) (by unfold cpFzW at hW; omega)
      (Q := fun v => v = .list [.nat 0, gpV qF]) rfl) fun v hv _ => by subst hv; exact hbF) ?_
    rintro v rfl hvw
    have hmsG : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ gp.map Prod.swap},
        MonoidHom.snd _ _ p = m := by
      intro m hm'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm'
      exact cp_hms ctx.hgp (hmem p hp)
    have dC := Det.mk3 (gP [gpV qk, gpV qF, .list (ms.map encPerm)])
      (gG [gpV qk, gpV qF, .list (ms.map encPerm)])
      (Det.var' (P := Pg) (env := [B, gpV qk, gpV qF, .list (ms.map encPerm)]) (i := 3) rfl)
    have w3c := wt_list3_le (.list [.nat k, .nat L.q]) (gpV gp) (.list (ms.map encPerm))
    have hmsl : ms.length = qF.length := by rw [hms, List.length_map]
    refine CpEB.call (CpEB.det dC (hR _ (by omega)) (by unfold cpFzW at hW; omega)
      (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV gp, .list (ms.map encPerm)]) rfl)
      fun v hv _ => ?_
    subst hv
    refine CpFB.mono (cp_bud_clos hst hpre hm hat.clos hjpre gp ms hmsG
      (by
        have := ctx.hgpl
        have : (NT + 1) * (k + L.q) ^ 2 ≤ (NT + 1) * (k + L.q + 1) ^ 4 :=
          Nat.mul_le_mul_left _ (f2.trans f24)
        unfold cpFzW at hW; omega) hW') le_rfl ?_
    rintro w ⟨fz, rfl, hfl, hcl⟩
    exact ⟨fz, rfl, hfl, cp_pairGens_clos ctx.hgp (S.liftGroup_le _) hgens hcl⟩
  have hTop : ∀ qk : GPairs k L.q, qk.length ≤ (k + L.q) ^ 2 →
      Subgroup.closure {p | p ∈ qk} = Subgroup.closure {p | p ∈ gp} ⊓ fixPts k L.q osA →
      CpEB Pg [B, gpV qk]
        (.letE (.call (f + 1) (mk3 (.var 0) (.length (.get (arg 1) (.nat 0))) (.var 1)))
        (.letE (.call (cpMapFst b) (mk2 (.nat 0) (.var 2)))
          (.call (cpClos b) (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.var 3))))) W
        ((40 * (W + 20) + (W * cpFzStepB hst hpre hm W + 3000 * (W + 1) ^ 2) + W + 1) +
          ((40 * (W + 20) + cpG hst hpre hm W + W + 1) +
            (40 * (W + 20) + cpG hst hpre hm W + W + 1) + W + 1) + W + 1)
        (fun w => ∃ fz : GPairs k L.q, w = gpV fz ∧ fz.length ≤ (k + L.q) ^ 2 ∧
          PairGens e L (S.liftGroup (certGroup S πd P₀.κ (dstr S z))) fz) := by
    intro qk hql hqcl
    refine CpEB.letE (hI qk hql hqcl) ?_
    rintro v ⟨qF, rfl, hqFl, hmem, hgens⟩ _
    have hfin := cp_fz_final (e := e) πd (logs.map Prod.fst) hTs z
    rw [List.length_map] at hfin
    rw [hfin] at hgens
    exact hEnd qk qF hqFl hmem hgens
  refine CpFB.intro hfz.entry ?_
  unfold cpFzE
  refine (CpEB.letE hK (Cb := (40 * (W + 20) + (W * cpFzStepB hst hpre hm W + 3000 * (W + 1) ^ 2) +
      W + 1) + ((40 * (W + 20) + cpG hst hpre hm W + W + 1) +
        (40 * (W + 20) + cpG hst hpre hm W + W + 1) + W + 1) + W + 1)
      fun v hv _ => ?_).mono ?_ fun _ h => h
  · obtain ⟨qk, rfl, hql, hqcl⟩ := hv
    exact hTop qk hql hqcl
  · unfold cpFzB
    omega

end Spec

end GI.Impl
