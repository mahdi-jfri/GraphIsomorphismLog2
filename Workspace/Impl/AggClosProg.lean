module

public import Workspace.Impl.AggClos
public import Workspace.Impl.AggPre

@[expose] public section

/-!
# The new stage of a round, in `GI.Lang`

Two modules for the coset closure `A_{t+1}` (`Workspace/Impl/AggClos.lean`).

* `ansGensFuns`: on `[a, u]`, with `a` the positions of a lift of a representative and `u` the
  answer value of its window call, the generators `ansGens a o` (`ansGens_spec`): none for the
  empty answer, and `a x` and `a x h` (`h ∈ gs`) for the answer `x ⟨gs⟩`. One composition and
  one map of compositions over the encoded group, whose first entry is the identity.
* `closFuns`: on `[[k, q], pairs of G, ms]`, the pairs that generate the part of the graph of
  `G` whose first part lies in `⟨ms⟩` (`clos_spec`). It swaps the two parts of each pair, runs the
  preimage module of `AggPre.lean` (which works on the second part), and swaps back.

With `pairGens_newStage` the output of `closFuns` on the collected `ansGens` is a graph form of
the lift of the new stage.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {k q : ℕ}

/-! ### Swapping the parts of the pairs -/

/-- On `[c, [a, b]]`: `[b, a]`. -/
def clSwapF : Expr := mk2 (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 0))

/-- `map clSwap` at base `b` (four functions). -/
def clSwapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [clSwapF]

theorem clSwap_step {P : Program} {f : ℕ} (hf : P.funs[f]? = some clSwapF)
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [.nat 0, pairV p]) (pairV p.swap) (300 * (k + q + 1) ^ 2) := by
  have g1 := Det.arg' (P := P) (vs := [.nat 0, pairV p]) (rest := []) (j := 1) rfl
  have d1 := Det.get' g1 (Det.nat 1) (v := encPerm p.2) rfl
  have d0 := Det.get' g1 (Det.nat 0) (v := encPerm p.1) rfl
  refine FunDet.intro hf ((Det.mk2 d1 d0).mono ?_)
  have w1 := wt_pairV_le p
  have w2 := wt_list2_le (.nat 0) (pairV p)
  have w3 := wt_nat_le 0
  have w4 := wt_encPerm_le p.2
  have w5 := wt_encPerm_le p.1
  have w6 := wt_list2_le (encPerm p.2) (encPerm p.1)
  have w7 := wt_nat_le 1
  have a1 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a2 : (k + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e1 : (pairV p).wt = (Val.list [encPerm p.1, encPerm p.2]).wt := rfl
  have a3 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The cost constant of the swap map. -/
def clSwapK : ℕ := 10 ^ 7

/-- **Swapping the parts of a list of pairs.** -/
theorem clSwap_spec {P : Program} {b : ℕ} (h : P.HasAt b (clSwapFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [.nat 0, .list (ps.map pairV)]) (.list ((ps.map Prod.swap).map pairV))
      (clSwapK * pM k q ps ^ 4) := by
  have hf : P.funs[b + 3]? = some clSwapF := by
    simpa using (h.block 3 (gs := [clSwapF]) (by rfl)).single
  have hm := mapList_spec (h.block 0 (by rfl)) ps pairV (fun p => pairV p.swap)
    (c := .nat 0) (B := 300 * (k + q + 1) ^ 2)
    (fun a _ a' _ he => by rw [pairV_injective he]) (fun p _ => clSwap_step hf p)
  have e : (ps.map Prod.swap).map pairV = ps.map fun p => pairV p.swap := by simp
  rw [e]
  refine hm.mono ?_
  set M := pM k q ps with hM
  have hl : ps.length + 1 ≤ M := by rw [hM]; unfold pM; omega
  have hN : k + q + 1 ≤ M := by rw [hM]; unfold pM; omega
  have w1 := wt_pairList_le ps
  rw [← hM] at w1
  have w2 : (Val.list (ps.map fun p => pairV p.swap)).wt ≤ 50 * M ^ 3 := by
    have h1 := wt_pairList_le (ps.map Prod.swap)
    rw [e] at h1
    have h2 : pM q k (ps.map Prod.swap) = M := by rw [hM]; unfold pM; simp; omega
    rw [h2] at h1
    exact h1
  have w3 := wt_list2_le (.nat 0) (.list (ps.map pairV))
  have w4 := wt_nat_le 0
  have a1 : 1 ≤ M := by omega
  have a2 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right a1 (by omega)
  have a3 : (k + q + 1) ^ 2 ≤ M ^ 3 :=
    (Nat.pow_le_pow_left hN 2).trans (Nat.pow_le_pow_right a1 (by omega))
  have a4 : ps.length * (300 * (k + q + 1) ^ 2) ≤ M * (300 * M ^ 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a5 : M * (300 * M ^ 3) = 300 * M ^ 4 := by ring
  have a9 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ a1
  have a7 : mapK * (ps.length + 1) * ((Val.list [Val.nat 0, Val.list (ps.map pairV)]).wt +
      (Val.list (ps.map fun p => pairV p.swap)).wt + 1) ≤ mapK * M * (300 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) (by omega)
  have a8 : mapK * M * (300 * M ^ 3) = 300000 * M ^ 4 := by simp only [mapK]; ring
  simp only [clSwapK] at *
  omega

/-! ### The closure module -/

/-- On `[[k, q], pairs, ms]`: swap the pairs, run the preimage module on `[[q, k], swapped,
ms]`, and swap its output back. -/
def closEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (.nat 0) (arg 1)))
    (.letE (.call (b + 5) (mk3 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 0))) (.var 1)
      (arg 2)))
      (.call (b + 1) (mk2 (.nat 0) (.var 2))))

/-- The closure module at base `b` (fifty-five functions), with the cited primitive at `jpre`. -/
def closFuns (b jpre : ℕ) : List Expr :=
  [closEntry b] ++ clSwapFuns (b + 1) ++ graphPreFuns (b + 5) jpre

/-- The swap of the pairs moves closures. -/
theorem clClosure_swap (ps : List (Perm (Fin k) × Perm (Fin q))) :
    Subgroup.closure {p | p ∈ ps.map Prod.swap} =
      (Subgroup.closure {p | p ∈ ps}).map (MulEquiv.prodComm).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext p
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_prodComm]

theorem clMem_closure_swap {k' q' : ℕ} (l : List (Perm (Fin q') × Perm (Fin k')))
    (x : Perm (Fin k') × Perm (Fin q')) :
    x ∈ Subgroup.closure {p | p ∈ l.map Prod.swap} ↔ x.swap ∈ Subgroup.closure {p | p ∈ l} := by
  rw [clClosure_swap]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨x.swap, hx, by simp⟩

open GI.Cited (Preimage) in
/-- **The closure module.** For generators `ms` of a subgroup of the first projection of the
group of the pairs `ps`, it returns pairs `qs` that generate the part of that group whose first
part lies in `⟨ms⟩`. -/
theorem clos_spec (h : Preimage) {P : Program} {b jpre : ℕ}
    (hb : P.HasAt b (closFuns b jpre)) (hj : P.prims[jpre]? = some (preimagePrim h))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (ms : List (Perm (Fin k)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps.map Prod.swap},
      MonoidHom.snd _ _ p = m) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), .list (ms.map encPerm)])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.fst _ _) ∧
        c ≤ (preimagePrim h).bound (preimageEnc (pairInst (MonoidHom.snd _ _)
          (ps.map Prod.swap) ms hms)) + 2 * graphPreK * preM q k (ps.map Prod.swap) ms ^ 8) := by
  have hentry : P.funs[b]? = some (closEntry b) := by
    simpa using (hb.block 0 (gs := [closEntry b]) (by rfl)).single
  have hsw : P.HasAt (b + 1) (clSwapFuns (b + 1)) := hb.block 1 (by rfl)
  have hpre : P.HasAt (b + 5) (graphPreFuns (b + 5) jpre) := hb.block 5 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), .list (ms.map encPerm)]
    with hA
  set ps' := ps.map Prod.swap with hps'
  set SW : Val := .list (ps'.map pairV) with hSW
  have d1 := Det.call (Det.mk2 (Det.nat (P := P) (env := [A]) 0)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      .list (ms.map encPerm)]) (rest := []) (j := 1) rfl)) (clSwap_spec hsw ps)
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  have gkq := Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
    .list (ms.map encPerm)]) (rest := [SW]) (j := 0) rfl
  have dqk := Det.mk2 (Det.get' gkq (Det.nat 1) (v := .nat q) rfl)
    (Det.get' gkq (Det.nat 0) (v := .nat k) rfl)
  have dms := Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
    .list (ms.map encPerm)]) (rest := [SW]) (j := 2) rfl
  have din := Det.mk3 dqk (Det.var' (P := P) (env := [A, SW]) (i := 1) rfl) dms
  set M := preM q k ps' ms with hM
  set Rb := (preimagePrim h).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps' ms hms))
    with hRb
  refine EvalAll.letE (Ra := fun w c => ∃ qs' : List (Perm (Fin q) × Perm (Fin k)),
      w = .list (qs'.map pairV) ∧ qs'.length ≤ (q + k) ^ 2 ∧
      Subgroup.closure {p | p ∈ qs'} =
        Subgroup.closure {p | p ∈ ps'} ⊓ (gens ms).comap (MonoidHom.snd _ _) ∧
      c ≤ Rb + graphPreK * M ^ 8 + 10 ^ 9 * M ^ 6)
    (EvalAll.call_funAll din fun v ca hv => ?_) fun w2 c2 h2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (graphPre_spec h hpre hj ps' ms hms).mono fun w c hw => ?_
    obtain ⟨qs', rfl, hl', hcl', hc'⟩ := hw
    refine ⟨qs', rfl, hl', hcl', ?_⟩
    clear d1 hc1 gkq dqk dms din
    have hsum : q + k + ps'.length + ms.length + 2 = M := by rw [hM]; rfl
    have hpl : ps'.length = ps.length := by rw [hps']; simp
    have hlM : ps'.length + 2 ≤ M := by rw [hM]; unfold preM; omega
    have hkM : q + k + 1 ≤ M := by rw [hM]; unfold preM; omega
    have hmM : ms.length + 2 ≤ M := by rw [hM]; unfold preM; omega
    have m1 : 1 ≤ M := by omega
    have p2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
    have p3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right m1 (by omega)
    have p4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right m1 (by omega)
    have p6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right m1 (by omega)
    -- weights
    have wps : (Val.list (ps'.map pairV)).wt ≤ 50 * M ^ 3 := by
      have := wt_pairList_le ps'
      have h3 : pM q k ps' ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by unfold pM; omega) 3
      omega
    have wms : (Val.list (ms.map encPerm)).wt ≤ 9 * M ^ 3 + 4 := by
      have h1 := wt_list_map_le ms encPerm (W := 4 * (k + 1) ^ 2) fun m _ => wt_encPerm_le m
      have h2 : ms.length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
        Nat.mul_le_mul (by omega) (by have := Nat.pow_le_pow_left (show k + 1 ≤ M by omega) 2; omega)
      have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
      omega
    have wqs : (Val.list (qs'.map pairV)).wt ≤ 400 * M ^ 6 := by
      have h1 := wt_pairList_le qs'
      have hq2 : qs'.length ≤ M ^ 2 := hl'.trans (Nat.pow_le_pow_left (by omega) 2)
      have h2 : pM q k qs' ≤ 2 * M ^ 2 := by unfold pM; omega
      have h3 := Nat.pow_le_pow_left h2 3
      have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
      omega
    have wqk := wt_list2_le (.nat q) (.nat k)
    have wq := wt_nat_le q
    have wk := wt_nat_le k
    have wkq := wt_list2_le (.nat k) (.nat q)
    have wA := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (.list (ms.map encPerm))
    have wps0 : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
      have := wt_pairList_le ps
      have h3 : pM k q ps ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by unfold pM; omega) 3
      omega
    have wv := wt_list3_le (.list [.nat q, .nat k]) SW (.list (ms.map encPerm))
    have eSW : SW.wt = (Val.list (ps'.map pairV)).wt := rfl
    have hca' : ca ≤ 10000 * M ^ 3 + 10000 := by
      clear hc'
      omega
    clear wA
    have e8 : preM q k ps' ms ^ 8 = M ^ 8 := by rw [hM]
    rw [e8] at hc'
    have m6 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ (by omega)
    clear * - hc' hca' wqs p3 p4 p6 m6
    omega
  · obtain ⟨qs', rfl, hl', hcl', hc2⟩ := h2
    have d3 := Det.call (Det.mk2 (Det.nat (P := P) (env := [A, SW, .list (qs'.map pairV)]) 0)
      (Det.var' (P := P) (env := [A, SW, .list (qs'.map pairV)]) (i := 2) rfl))
      (clSwap_spec hsw qs')
    refine d3.post fun c hc => ⟨qs'.map Prod.swap, rfl, by simp only [List.length_map]; rw [Nat.add_comm k q]; exact hl', ?_, ?_⟩
    · ext p
      rw [clMem_closure_swap, hcl', Subgroup.mem_inf, Subgroup.mem_inf, hps', clMem_closure_swap,
        Prod.swap_swap]
      simp
    · clear d1 d3 gkq dqk dms din
      have hsum : q + k + ps'.length + ms.length + 2 = M := by rw [hM]; rfl
      have hpl : ps'.length = ps.length := by rw [hps']; simp
      have hlM : ps'.length + 2 ≤ M := by rw [hM]; unfold preM; omega
      have hkM : q + k + 1 ≤ M := by rw [hM]; unfold preM; omega
      have m1 : 1 ≤ M := by omega
      have p2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
      have p3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right m1 (by omega)
      have p4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right m1 (by omega)
      have p6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right m1 (by omega)
      have p8 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right m1 (by omega)
      have c1' : clSwapK * pM k q ps ^ 4 ≤ clSwapK * M ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold pM; omega) 4)
      have c3' : clSwapK * pM q k qs' ^ 4 ≤ clSwapK * (16 * M ^ 8) := by
        have hq2 : qs'.length ≤ M ^ 2 := hl'.trans (Nat.pow_le_pow_left (by omega) 2)
        have h2 : pM q k qs' ≤ 2 * M ^ 2 := by unfold pM; omega
        have h3 := Nat.pow_le_pow_left h2 4
        have e : (2 * M ^ 2) ^ 4 = 16 * M ^ 8 := by ring
        exact Nat.mul_le_mul_left _ (e ▸ h3)
      have wqs : (Val.list (qs'.map pairV)).wt ≤ 400 * M ^ 6 := by
        have h1 := wt_pairList_le qs'
        have hq2 : qs'.length ≤ M ^ 2 := hl'.trans (Nat.pow_le_pow_left (by omega) 2)
        have h2 : pM q k qs' ≤ 2 * M ^ 2 := by unfold pM; omega
        have h3 := Nat.pow_le_pow_left h2 3
        have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
        omega
      have wqs2 : (Val.list ((qs'.map Prod.swap).map pairV)).wt ≤ 400 * M ^ 6 := by
        have h1 := wt_pairList_le (qs'.map Prod.swap)
        have hq2 : qs'.length ≤ M ^ 2 := hl'.trans (Nat.pow_le_pow_left (by omega) 2)
        have h2 : pM k q (qs'.map Prod.swap) ≤ 2 * M ^ 2 := by unfold pM; simp; omega
        have h3 := Nat.pow_le_pow_left h2 3
        have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
        omega
      have wps : SW.wt ≤ 50 * M ^ 3 := by
        have := wt_pairList_le ps'
        have h3 : pM q k ps' ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by unfold pM; omega) 3
        exact this.trans (by omega)
      have w0 := wt_nat_le 0
      have wa := wt_list2_le (.nat 0) (.list (qs'.map pairV))
      have wb := wt_list2_le (.nat 0) (.list (ps.map pairV))
      have wps0 : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
        have := wt_pairList_le ps
        have h3 : pM k q ps ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by unfold pM; omega) 3
        omega
      have wA := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (.list (ms.map encPerm))
      have wkq := wt_list2_le (.nat k) (.nat q)
      have wq := wt_nat_le q
      have wk := wt_nat_le k
      have wms : (Val.list (ms.map encPerm)).wt ≤ 9 * M ^ 3 + 4 := by
        have h1 := wt_list_map_le ms encPerm (W := 4 * (k + 1) ^ 2) fun m _ => wt_encPerm_le m
        have hmM : ms.length + 2 ≤ M := by rw [hM]; unfold preM; omega
        have h2 : ms.length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
          Nat.mul_le_mul (by omega) (by have := Nat.pow_le_pow_left (show k + 1 ≤ M by omega) 2; omega)
        have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
        omega
      have eSW : SW.wt = (Val.list ((ps.map Prod.swap).map pairV)).wt := rfl
      have m8 : 1 ≤ M ^ 8 := Nat.one_le_pow _ _ (by omega)
      have hA' : (Val.list [Val.list [Val.nat k, Val.nat q], Val.list (List.map pairV ps),
          Val.list (List.map encPerm ms)]).wt ≤ 1000 * M ^ 3 := by
        clear hc1 hc2 hc c1' c3'
        omega
      have hx1 : c1 ≤ 10 ^ 8 * M ^ 8 := by
        clear hc2 hc c3'
        simp only [clSwapK] at c1' hc1
        omega
      have hcc : c ≤ 10 ^ 9 * M ^ 8 := by
        clear hc2 hc1 c1'
        simp only [clSwapK] at c3' hc
        omega
      have e8 : preM q k ps' ms ^ 8 = M ^ 8 := by rw [hM]
      clear * - hx1 hcc hc2 wqs2 p8 m8
      simp only [graphPreK] at *
      omega

/-! ### The generators of one window answer -/

/-- An answer value in the form of `AnsSet`: `[]` for `none`, and `[x, encGroup gs]` with at
most `k²` generators for `some (x, gs)`. -/
def AnsOV (u : Val) : Option (Perm (Fin k) × List (Perm (Fin k))) → Prop
  | none => u = .list []
  | some (x, gs) => u = .list [encPerm x, encGroup gs] ∧ gs.length ≤ k ^ 2

/-- A canonical answer is an answer value of this form. -/
theorem AnsC.ansOV {Ω : Type} {e : Ω ≃ Fin k} {u : Val} {B : Set (Perm Ω)} (h : AnsC e u B) :
    ∃ o, AnsOV u o ∧ AnsSet e o B := by
  rcases h with ⟨rfl, rfl⟩ | ⟨x, gs, rfl, hl, hB⟩
  · exact ⟨none, rfl, rfl⟩
  · exact ⟨some (x, gs), ⟨rfl, hl⟩, hB⟩

/-- On `[a, u]`: nothing for `u = []`, else the map of `compose (a x)` over the generator list
of `u = [x, [k, [1, h₁, …]]]`. -/
def ansGensF (b : ℕ) : Expr :=
  .ite (.length (arg 1))
    (.call (b + 5) (mk2 (.call (b + 1) (mk2 (arg 0) (.get (arg 1) (.nat 0))))
      (.get (.get (arg 1) (.nat 1)) (.nat 1))))
    .nil

/-- The answer-generator module at base `b` (eight functions). -/
def ansGensFuns (b : ℕ) : List Expr := [ansGensF b] ++ composeFuns (b + 1) ++ mapFuns (b + 5) (b + 1)

/-- The cost constant of `ansGens_spec`. -/
def ansGK : ℕ := 10 ^ 9

theorem cosGens_map (c : Perm (Fin k)) (gs : List (Perm (Fin k))) :
    (1 :: gs).map (fun h => encPerm (c * h)) = (cosGens c gs).map encPerm := by
  simp [cosGens]

/-- **The generators of one window answer**, at cost at most `ansGK (k + 1)⁸`. -/
theorem ansGens_spec {P : Program} {b : ℕ} (h : P.HasAt b (ansGensFuns b)) (a : Perm (Fin k))
    {u : Val} {o : Option (Perm (Fin k) × List (Perm (Fin k)))} (hu : AnsOV u o) :
    FunDet P b (.list [encPerm a, u]) (.list ((ansGens a o).map encPerm)) (ansGK * (k + 1) ^ 8) := by
  have hentry : P.funs[b]? = some (ansGensF b) := by
    simpa using (h.block 0 (gs := [ansGensF b]) (by rfl)).single
  have hcomp : P.HasAt (b + 1) (composeFuns (b + 1)) := h.block 1 (by rfl)
  have hmap : P.HasAt (b + 5) (mapFuns (b + 5) (b + 1)) := h.block 5 (by rfl)
  have p1 : 1 ≤ (k + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  match o, hu with
  | none, hu =>
    simp only [AnsOV] at hu
    subst hu
    have g1 := Det.arg' (P := P) (vs := [encPerm a, .list []]) (rest := []) (j := 1) rfl
    refine FunDet.intro hentry ((Det.ite_zero (Det.length g1) Det.nil).mono ?_)
    have w1 := wt_encPerm_le a
    have w2 := wt_list2_le (encPerm a) (.list [])
    have w3 : (Val.list []).wt ≤ 5 := by simp
    have a1 : (k + 1) ^ 2 ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [List.length_nil, ansGK] at *
    omega
  | some (x, gs), ⟨hu, hl⟩ =>
    subst hu
    set U : Val := .list [encPerm x, encGroup gs] with hU
    have g0 := Det.arg' (P := P) (vs := [encPerm a, U]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [encPerm a, U]) (rest := []) (j := 1) rfl
    have gx := Det.get' g1 (Det.nat 0) (v := encPerm x) rfl
    have dc := Det.call (Det.mk2 g0 gx) (compose_spec hcomp a x)
    have gg := Det.get' (Det.get' g1 (Det.nat 1) (v := encGroup gs) rfl) (Det.nat 1)
      (v := .list ((1 :: gs).map encPerm)) rfl
    have hm := mapList_spec hmap (1 :: gs) encPerm (fun h => encPerm (a * x * h))
      (c := encPerm (a * x)) (B := permK * (k + 1) ^ 3)
      (fun _ _ _ _ he => by rw [encPerm_injective he])
      (fun h _ => compose_spec hcomp (a * x) h)
    have dm := Det.call (Det.mk2 dc gg) hm
    have hlen : Det P [Val.list [encPerm a, U]] (.length (arg 1)) (.nat 2) _ := Det.length g1
    rw [show (ansGens a (some (x, gs))).map encPerm = (1 :: gs).map (fun h => encPerm (a * x * h))
      by rw [ansGens, cosGens_map]]
    refine FunDet.intro hentry ((Det.ite_pos hlen (by norm_num) dm).mono ?_)
    -- the cost
    have hlg : (1 :: gs).length ≤ k ^ 2 + 1 := by simp; omega
    have k2 : k ^ 2 + 2 ≤ 2 * (k + 1) ^ 2 := by
      have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega
    have wa := wt_encPerm_le a
    have wx := wt_encPerm_le x
    have wax := wt_encPerm_le (a * x)
    have wG : (encGroup gs).wt ≤ 160 * (k + 1) ^ 6 := by
      have h1 := wt_encGroup_le gs
      have h2 : (gs.length + 2) * (k + 1) ≤ 2 * (k + 1) ^ 3 := by
        have := Nat.mul_le_mul_right (k + 1) (show gs.length + 2 ≤ 2 * (k + 1) ^ 2 by omega)
        have e : 2 * (k + 1) ^ 2 * (k + 1) = 2 * (k + 1) ^ 3 := by ring
        omega
      have h3 := Nat.pow_le_pow_left h2 2
      have e : (2 * (k + 1) ^ 3) ^ 2 = 4 * (k + 1) ^ 6 := by ring
      omega
    have wL : (Val.list ((1 :: gs).map encPerm)).wt ≤ 22 * (k + 1) ^ 6 := by
      have h1 := wt_list_map_le (1 :: gs) encPerm (W := 4 * (k + 1) ^ 2) fun m _ => wt_encPerm_le m
      have h2 : (1 :: gs).length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ (2 * (k + 1) ^ 2) * (9 * (k + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e : (2 * (k + 1) ^ 2) * (9 * (k + 1) ^ 2) = 18 * (k + 1) ^ 4 := by ring
      rw [e] at h2
      have h4 : (k + 1) ^ 4 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      have h5 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    have wR : (Val.list ((1 :: gs).map fun h => encPerm (a * x * h))).wt ≤ 22 * (k + 1) ^ 6 := by
      have h1 := wt_list_map_le (1 :: gs) (fun h => encPerm (a * x * h)) (W := 4 * (k + 1) ^ 2)
        fun m _ => wt_encPerm_le _
      have h2 : (1 :: gs).length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ (2 * (k + 1) ^ 2) * (9 * (k + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e : (2 * (k + 1) ^ 2) * (9 * (k + 1) ^ 2) = 18 * (k + 1) ^ 4 := by ring
      rw [e] at h2
      have h4 : (k + 1) ^ 4 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      have h5 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    have eR : (Val.list ((ansGens a (some (x, gs))).map encPerm)).wt =
        (Val.list ((1 :: gs).map fun h => encPerm (a * x * h))).wt := by
      rw [ansGens, cosGens_map]
    have wU := wt_list2_le (encPerm x) (encGroup gs)
    have wAU := wt_list2_le (encPerm a) U
    have eU : U.wt = (Val.list [encPerm x, encGroup gs]).wt := rfl
    have w2 := wt_list2_le (encPerm a) (encPerm x)
    have w3 := wt_list2_le (encPerm (a * x)) (.list ((1 :: gs).map encPerm))
    have w4 := wt_nat_le 2
    have w5 := wt_nat_le 0
    have w6 := wt_nat_le 1
    have p2 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have p3 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have p6 : (k + 1) ^ 6 ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have c1 : (1 :: gs).length * (permK * (k + 1) ^ 3) ≤ (2 * (k + 1) ^ 2) * (permK * (k + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) le_rfl
    have c1e : (2 * (k + 1) ^ 2) * (permK * (k + 1) ^ 3) = 2 * permK * (k + 1) ^ 5 := by ring
    have p5 : (k + 1) ^ 5 ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have c2 : mapK * ((1 :: gs).length + 1) *
        ((Val.list [encPerm (a * x), .list ((1 :: gs).map encPerm)]).wt +
          (Val.list ((1 :: gs).map fun h => encPerm (a * x * h))).wt + 1) ≤
        mapK * (2 * (k + 1) ^ 2) * (100 * (k + 1) ^ 6) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have c2e : mapK * (2 * (k + 1) ^ 2) * (100 * (k + 1) ^ 6) = 200000 * (k + 1) ^ 8 := by
      simp only [mapK]; ring
    have p3' : (k + 1) ^ 3 ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have hl2 : [encPerm x, encGroup gs].length = 2 := rfl
    clear dm dc gg hm hlen g0 g1 gx
    simp only [ansGK, permK] at *
    omega

end GI.Impl
