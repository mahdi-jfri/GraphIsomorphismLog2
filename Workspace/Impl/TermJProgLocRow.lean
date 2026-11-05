module

public import Workspace.Impl.TermJProgLocPi

@[expose] public section

/-!
# The local transporter of a class (program, part 3: rows and local elements)

* `tmJLRowF`: on `[inp, a]`, row `a` of the tests (`tmJL_row_spec`);
* `tmJLDF`: on `[[inp, σ, ⟨σN⟩], a]`, with the entry `[g, gs]` of `(a, σ a)`: NormalizedFactor
  of `g⁻¹ h` in `⟨gs⟩ ⟨σN⟩` gives `g⁻¹ h = s n`, and the result is `(g s)⁻¹`
  (`tmJL_d_spec`).

Costs are stated in `Y = wt inp + 1`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {m q : ℕ}

/-! ### One row of tests -/

/-- On `[inp, a]`: row `a` of the tests. -/
def tmJLRowF (rg mB : ℕ) : Expr :=
  .call mB (mk2 (mk2 (arg 0) (arg 1)) (.call rg (.get (arg 0) (.nat 3))))

/-- The cost bound of one row, in `Y = wt inp + 1`. -/
def tmJLRowC (pm : Prim) (Y : ℕ) : ℕ := Y * tmJLBitC pm Y + 10 ^ 6 * Y ^ 3

/-- The range program gives the points. -/
theorem tmJL_range {P : Program} {rg : ℕ} (hrg : P.HasAt rg (rangeFuns rg)) (n : ℕ) :
    FunDet P rg (.nat n) (tmJLIds n)
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) := by
  rw [tmJLIds, encFun_id]
  exact FunAll.mono (range_spec hrg n) fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩

theorem tmJL_range_le (n : ℕ) :
    loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
      10 ^ 4 * (n + 1) ^ 3 := by
  have h1 : (natList (List.range n)).wt ≤ 4 * (n + 1) ^ 2 := by
    rw [← encFun_id]; exact wt_ids_le n
  have h2 := wt_nat_le n
  have h3 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  calc loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)
      ≤ 1000 * (n + 1) * (10 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
    _ = 10 ^ 4 * (n + 1) ^ 3 := by ring

section Setting

variable {C : Type} {H N : Subgroup (Perm (Fin m))} {σN : List (Perm (Fin m))}
  {x y : Fin q → Fin m → C} {A : Fin q × Fin q → Set (Perm (Fin m))} {vs : List Val}

/-- **One row of tests.** -/
theorem tmJL_row_spec (hm : GI.Cited.Membership) {P : Program} {f rg mB fb jm ap cp iv : ℕ}
    (hf : P.funs[f]? = some (tmJLRowF rg mB)) (hrg : P.HasAt rg (rangeFuns rg))
    (hmB : P.HasAt mB (mapFuns mB fb)) (hfb : P.funs[fb]? = some (tmJLBitF jm ap cp iv))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) (hap : P.HasAt ap (appendFuns ap))
    (hcp : P.HasAt cp (composeFuns cp)) (hiv : P.HasAt iv (invFuns iv))
    (hn : GI.Multicoset.Normalizes H N) (hσN : gens σN = N)
    (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j})
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (A ij)) vs (tmCosets q))
    (h : Perm (Fin m)) (a : Fin q) :
    FunDet P f (.list [tmJLInp h vs σN q, .nat a]) (tmJLRowV (tmJLMat N h A) a)
      (tmJLRowC (membershipPrim hm) ((tmJLInp h vs σN q).wt + 1)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  obtain ⟨wm, wqq, wq, wh, wvs, wσ, wnq, wnm⟩ := tmJL_inp_wt h σN hq hlen
  set inp := tmJLInp h vs σN q with hinp
  set Y := inp.wt + 1 with hY
  set M := tmJLMat N h A with hM
  have d0 := Det.arg' (P := P) (vs := [inp, .nat a]) (rest := []) (j := 0) (v := inp) rfl
  have d1 := Det.arg' (P := P) (vs := [inp, .nat a]) (rest := []) (j := 1) (v := .nat a) rfl
  have dq := Det.get' d0 (Det.nat 3) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := .nat q) rfl
  have crg := Det.call dq (tmJL_range hrg q)
  have hT := tabulate_spec hmB (c := .list [inp, .nat a]) (F := fun j => boolVal (M a j))
    (fun j => tmJL_bit_spec hm hfb hjm hap hcp hiv hn hσN hAdef hvs h a j)
  have c := Det.call (Det.mk2 (Det.mk2 d0 d1) crg) hT
  rw [← tmJLRowV_eq] at c
  refine FunDet.intro hf (c.mono ?_)
  -- the cost
  have hrl := tmJL_range_le q
  have wrow := tmJL_wt_row M a
  have wids : (tmJLIds q).wt ≤ 4 * (q + 1) ^ 2 := wt_ids_le q
  have wa := wt_nat_le a
  have ha := a.2
  have wia := wt_list2_le inp (.nat a)
  have wc := wt_list2_le (.list [inp, .nat a]) (tmJLIds q)
  have hqY : q + 1 ≤ Y := by omega
  have hq2 : (q + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hqY 2
  have hq3 : (q + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hqY 3
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have l1 : mapK * (q + 1) * ((Val.list [.list [inp, .nat a], tmJLIds q]).wt +
      (tmJLRowV M a).wt + 1) ≤ 1000 * Y * (100 * Y ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hqY) (by omega)
  have l2 : 1000 * Y * (100 * Y ^ 2) = 10 ^ 5 * Y ^ 3 := by ring
  have l3 : q * tmJLBitC (membershipPrim hm) ((tmJLInp h vs σN q).wt + 1) ≤
      Y * tmJLBitC (membershipPrim hm) Y := Nat.mul_le_mul_right _ (by omega)
  have l1' : mapK * (q + 1) * ((Val.list [.list [inp, .nat a], encFun fun i : Fin q => (i : ℕ)]).wt +
      (tmJLRowV M a).wt + 1) ≤ 1000 * Y * (100 * Y ^ 2) := l1
  unfold tmJLRowC
  omega

/-! ### The group `⟨σN⟩` as a value -/

theorem tmJL_wt_σG {σN : List (Perm (Fin m))} {W : ℕ} (hm : m < W)
    (hσ : (Val.list (σN.map encPerm)).wt < W) : (encGroup σN).wt ≤ 40 * (W + 1) ^ 2 := by
  have e : encGroup σN = .list [.nat m, .list (encPerm (1 : Perm (Fin m)) :: σN.map encPerm)] :=
    rfl
  rw [e]
  have h1 := wt_list2_le (.nat m) (.list (encPerm (1 : Perm (Fin m)) :: σN.map encPerm))
  have h2 := wt_list_cons_le (encPerm (1 : Perm (Fin m))) (σN.map encPerm)
  have h3 := wt_encPerm_le (1 : Perm (Fin m))
  have h4 := wt_nat_le m
  have h5 : (m + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h6 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-! ### One local element -/

/-- On `[[inp, σ, ⟨σN⟩], a]`: with the entry `[g, gs]` of `(a, σ a)`, factor `g⁻¹ h = s n` in
`⟨gs⟩ ⟨σN⟩` and return `(g s)⁻¹`. -/
def tmJLDF (jf cp iv : ℕ) : Expr :=
  .letE (.get (.get (.get (arg 0) (.nat 0)) (.nat 1))
      (.arith .add (.arith .mul (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 3)))
        (.get (.get (arg 0) (.nat 1)) (arg 1))))
  (.letE (.call iv (.get (.var 1) (.nat 0)))
  (.letE (.prim jf (mk3 (.get (.var 1) (.nat 1)) (.get (arg 0) (.nat 2))
      (.call cp (mk2 (.var 2) (.get (.get (arg 0) (.nat 0)) (.nat 0))))))
  (.call cp (mk2 (.call iv (.get (.var 3) (.nat 0))) (.var 2)))))

/-- The cost bound of one local element, in `Y = wt inp + 1`. -/
def tmJLDC (pf : Prim) (Y : ℕ) : ℕ := pf.c * (200 * Y ^ 2 + 2) ^ pf.k + 10 ^ 7 * Y ^ 4

/-- **One local element.** -/
theorem tmJL_d_spec (hfac : GI.Cited.NormalizedFactor) {P : Program} {f jf cp iv : ℕ}
    (hf : P.funs[f]? = some (tmJLDF jf cp iv))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    (hcp : P.HasAt cp (composeFuns cp)) (hiv : P.HasAt iv (invFuns iv))
    (hn : GI.Multicoset.Normalizes H N) (hσN : gens σN = N)
    (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j})
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (A ij)) vs (tmCosets q))
    (h : Perm (Fin m)) (σ : Perm (Fin q)) (a : Fin q) (hT : tmJLTest N h (A (a, σ a))) :
    FunAll P f (.list [.list [tmJLInp h vs σN q, encPerm σ, encGroup σN], .nat a])
      (fun w cost => (∃ d, (d ∈ A (a, σ a) ∧ h⁻¹ * d ∈ N) ∧ w = encPerm d⁻¹) ∧
        cost ≤ tmJLDC (normalizedFactorPrim hfac) ((tmJLInp h vs σN q).wt + 1)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  obtain ⟨wm, wqq, wq, wh, wvs, wσ, wnq, wnm⟩ := tmJL_inp_wt h σN hq hlen
  set inp := tmJLInp h vs σN q with hinp
  set Y := inp.wt + 1 with hY
  set cD := Val.list [inp, encPerm σ, encGroup σN] with hcD
  set av := Val.list [cD, .nat a] with hav
  obtain ⟨v, hv, hans⟩ := tmJL_entry hvs a (σ a)
  have wv : v.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hv)
  rcases tmJL_ans hans with ⟨rfl, hA0⟩ | ⟨g, gs, rfl, hgl, hAg⟩
  · exfalso
    obtain ⟨u, hu, -⟩ := hT
    rw [hA0] at hu; exact hu
  have hsub : g • (gens gs : Set (Perm (Fin m))) ⊆ H := fun u hu => by
    rw [← hAg, hAdef] at hu; exact hu.1
  have hgs := tmJL_gs_mem hsub
  have hx : ∃ s ∈ gens gs, ∃ n ∈ gens σN, g⁻¹ * h = s * n := by
    have := (tmJL_test_iff h hn hσN hgs).1 (by rw [← hAg]; exact hT)
    exact (tmJL_fac_iff hn hσN hgs).1 this
  set ve := Val.list [encPerm g, encGroup gs] with hve
  -- step 1: the entry
  have d0 := Det.arg' (P := P) (vs := [cD, .nat a]) (rest := []) (j := 0) (v := cD) rfl
  have d1 := Det.arg' (P := P) (vs := [cD, .nat a]) (rest := []) (j := 1) (v := .nat a) rfl
  have dinp := Det.get' d0 (Det.nat 0) (vs := [inp, encPerm σ, encGroup σN]) (v := inp) rfl
  have dpi := Det.get' d0 (Det.nat 1) (vs := [inp, encPerm σ, encGroup σN]) (v := encPerm σ) rfl
  have dvs := Det.get' dinp (Det.nat 1) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := .list vs) rfl
  have dq := Det.get' dinp (Det.nat 3) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := .nat q) rfl
  have dmul := Det.arith' (op := .mul) d1 dq (z := a * q) rfl
  have hsa : ((List.finRange q).map fun i => Val.nat (σ i))[(a : ℕ)]? = some (.nat (σ a)) := by
    simp [a.2]
  have dsa := Det.get' dpi d1 hsa
  have dadd := Det.arith' (op := .add) dmul dsa (z := a * q + σ a) rfl
  have dent := Det.get' dvs dadd hv
  refine FunAll.intro hf (EvalAll.letE dent fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: `g⁻¹`
  have e1 := Det.var' (P := P) (env := [av, ve]) (i := 1) (v := ve) rfl
  have eg := Det.get' e1 (Det.nat 0) (vs := [encPerm g, encGroup gs]) (v := encPerm g) rfl
  have cinv := Det.call eg (inv_spec hiv g)
  refine EvalAll.letE cinv fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- step 3: the factorization
  have f1 := Det.var' (P := P) (env := [av, ve, encPerm g⁻¹]) (i := 1) (v := ve) rfl
  have fG := Det.get' f1 (Det.nat 1) (vs := [encPerm g, encGroup gs]) (v := encGroup gs) rfl
  have f0 := Det.arg' (P := P) (vs := [cD, .nat a]) (rest := [ve, encPerm g⁻¹]) (j := 0)
    (v := cD) rfl
  have fσG := Det.get' f0 (Det.nat 2) (vs := [inp, encPerm σ, encGroup σN]) (v := encGroup σN) rfl
  have finp := Det.get' f0 (Det.nat 0) (vs := [inp, encPerm σ, encGroup σN]) (v := inp) rfl
  have fh := Det.get' finp (Det.nat 0) (vs := [encPerm h, .list vs, .list (σN.map encPerm),
    .nat q, .nat m]) (v := encPerm h) rfl
  have fgi := Det.var' (P := P) (env := [av, ve, encPerm g⁻¹]) (i := 2) (v := encPerm g⁻¹) rfl
  have fx := Det.call (Det.mk2 fgi fh) (compose_spec hcp g⁻¹ h)
  have farg := Det.mk3 fG fσG fx
  have hcall := normalizedFactor_call hfac hjf farg (G := gens gs) (N := gens σN)
    ⟨gs, rfl, rfl⟩ ⟨σN, rfl, rfl⟩ (tmJL_norm hn hσN hgs) hx
  refine EvalAll.letE hcall fun w3 c3 h3 => ?_
  obtain ⟨⟨s, hs, n, hn', hxe, rfl⟩, hc3⟩ := h3
  -- step 4: `(g s)⁻¹ = s⁻¹ g⁻¹`
  have k3 := Det.var' (P := P) (env := [av, ve, encPerm g⁻¹, .list [encPerm s, encPerm n]])
    (i := 3) (v := .list [encPerm s, encPerm n]) rfl
  have ks := Det.get' k3 (Det.nat 0) (vs := [encPerm s, encPerm n]) (v := encPerm s) rfl
  have kinv := Det.call ks (inv_spec hiv s)
  have k2 := Det.var' (P := P) (env := [av, ve, encPerm g⁻¹, .list [encPerm s, encPerm n]])
    (i := 2) (v := encPerm g⁻¹) rfl
  have kc := Det.call (Det.mk2 kinv k2) (compose_spec hcp s⁻¹ g⁻¹)
  rw [← mul_inv_rev] at kc
  have hfac' := tmJL_fac h hs (hσN ▸ hn') hxe
  refine kc.post fun c4 hc4 => ⟨⟨g * s, ⟨by rw [hAg]; exact hfac'.1, hfac'.2⟩, rfl⟩, ?_⟩
  -- the cost
  have wG : (encGroup gs).wt < ve.wt := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < ve.wt := wt_le_wt_list (by simp)
  have wσG := tmJL_wt_σG wm wσ
  rw [← hY] at wσG
  have wpi := wt_encPerm_le σ
  have wcD : cD.wt ≤ 2 * (inp.wt + (encPerm σ).wt + (encGroup σN).wt) + 7 := wt_list3_le _ _ _
  have wav := wt_list2_le cD (.nat a)
  have wa := wt_nat_le a
  have ha := a.2
  have hsaq := (σ a).2
  have haq : (a : ℕ) * q + σ a < q * q :=
    calc (a : ℕ) * q + σ a < a * q + q := by omega
      _ = (a + 1) * q := by ring
      _ ≤ q * q := Nat.mul_le_mul_right _ ha
  have wmul := wt_nat_le (a * q)
  have wadd := wt_nat_le (a * q + σ a)
  have wsa := wt_nat_le (σ a)
  have wgi := wt_encPerm_le g⁻¹
  have wgh := wt_encPerm_le (g⁻¹ * h)
  have whh := wt_encPerm_le h
  have ws := wt_encPerm_le s
  have wn := wt_encPerm_le n
  have wsi := wt_encPerm_le s⁻¹
  have wgs := wt_encPerm_le (g * s)⁻¹
  have wsn := wt_list2_le (encPerm s) (encPerm n)
  have wih := wt_list2_le (encPerm g⁻¹) (encPerm h)
  have wsg := wt_list2_le (encPerm s⁻¹) (encPerm g⁻¹)
  have warg := wt_list3_le (encGroup gs) (encGroup σN) (encPerm (g⁻¹ * h))
  have hmY : m + 1 ≤ Y := by omega
  have hqY : q + 1 ≤ Y := by omega
  have hm2 : (m + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hmY 2
  have hq2 : (q + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hqY 2
  have hm3 : (m + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hmY 3
  have hm4 : (m + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hmY 4
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hW : (Val.list [encGroup gs, encGroup σN, encPerm (g⁻¹ * h)]).wt ≤ 200 * Y ^ 2 := by omega
  have hpb := tmJL_prim_le (normalizedFactorPrim hfac) hW
  have hpk : permK * (m + 1) ^ 3 ≤ 30000 * Y ^ 3 := by
    rw [show permK = 30000 from rfl]; omega
  have hik : invK * (m + 1) ^ 4 ≤ 100000 * Y ^ 4 := by
    rw [show invK = 100000 from rfl]; omega
  unfold tmJLDC
  omega

end Setting

end GI.Impl
