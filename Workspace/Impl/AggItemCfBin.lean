import Workspace.Impl.AggItemCfLk
import Workspace.Impl.AggStructCol

/-!
# Case 2b: the objects of a branch, with one binary refinement call

In the branch of `b`, the program of Case 2b

1. computes the orbital coloring `c_Y = orbColOut H_Y b` of the target structure (object stage,
   `ItCfObjSpec.col`);
2. looks `c_Y` up in the cache (`it_cfLk_spec`). If an entry is there, it takes its values
   `(d, d')`. Otherwise it calls `KaryRefinement 2` on `(c_X, c_Y)` (`stRef_spec`, Section A.3:
   "apply the canonical coherent refinement from Helfgott's exposition to this binary coloring")
   and appends the entry `(c_Y, d, d')`;
3. computes the two objects `orbitalOut d H_X src` and `orbitalOut d' H_Y b` (object stage,
   `ItCfObjSpec.orb`).

`itCfO2F` is this program, on `[K.v, stTv b, wO]` with the object part of the kept value
`wO = [⟨H_X⟩, ⟨H_Y⟩, ⟨c_X⟩, ⟨cache⟩]` (`itCfWO`). It returns `[⟨oX⟩, ⟨oY⟩, wO']`
(`it_cfO2_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKColoring gens encGroup KaryRefinement JointRefinement)

variable {q : ℕ}

/-- **The object part of the kept value**: `[⟨H_X⟩, ⟨H_Y⟩, ⟨c_X⟩, ⟨cache⟩]`. -/
def itCfWO (hx hy : List (Perm (Fin q))) (cX : (Fin 2 → Fin q) → ℕ)
    (cache : List (ItCfEnt q)) : Val :=
  .list [encGroup hx, encGroup hy, encKColoring cX, .list (cache.map itCfEntV)]

/-- The program of the objects of Case 2b. -/
def itCfO2F (fcol fd ref forb : ℕ) : Expr :=
  .letE (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1))
  (.letE (.call fcol (mk3 (.var 1) (.get (arg 2) (.nat 1)) (arg 1)))
  (.letE (.call fd (mk2 (.var 2) (.get (arg 2) (.nat 3))))
  (.letE (.ite (.arith .lt (.var 3) (.length (.get (arg 2) (.nat 3))))
      (mk2 (.get (.get (.get (arg 2) (.nat 3)) (.var 3)) (.nat 1)) (.get (arg 2) (.nat 3)))
      (.letE (.call ref (mk2 (.var 1) (mk2 (.get (arg 2) (.nat 2)) (.var 2))))
        (mk2 (.var 4) (.snoc (.get (arg 2) (.nat 3)) (mk2 (.var 2) (.var 4))))))
  (.letE (.call forb (mk4 (.var 1) (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 3))
      (.get (.get (.var 4) (.nat 0)) (.nat 0))))
  (.letE (.call forb (mk4 (.var 1) (.get (arg 2) (.nat 1)) (arg 1)
      (.get (.get (.var 4) (.nat 0)) (.nat 1))))
    (mk3 (.var 5) (.var 6) (mk4 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
      (.get (arg 2) (.nat 2)) (.get (.var 4) (.nat 1)))))))))

/-- The cost bound of `itCfO2F`, for a weight bound `V` and a bound `B` on the callees. -/
def itCfO2C (V B : ℕ) : ℕ := 10 ^ 6 * (V + B + 1)

/-- **What the binary step does with the cache**: either the key was there with the values
`(d, d')`, or it was not, and the entry `(c_Y, d, d')` with a joint refinement is appended. -/
def ItCfBinStep (cX cY : (Fin 2 → Fin q) → ℕ) (cache cache' : List (ItCfEnt q))
    (d d' : (Fin 2 → Fin q) → ℕ) : Prop :=
  (cache' = cache ∧ (cY, d, d') ∈ cache) ∨
  (cache' = cache ++ [(cY, d, d')] ∧ (∀ a ∈ cache, a.1 ≠ cY) ∧ JointRefinement cX cY d d' ∧
    (∀ z, d z < 2 * q ^ 2) ∧ (∀ z, d' z < 2 * q ^ 2))

set_option maxHeartbeats 4000000 in
/-- **The objects of Case 2b as a program.** -/
theorem it_cfO2_spec {P : Program} {f fcol forb fdes fd kt eqn ref brep j Co Do : ℕ}
    (hf : P.funs[f]? = some (itCfO2F fcol fd ref forb)) (hobj : ItCfObjSpec P fcol forb fdes Co Do)
    (hfd : P.HasAt fd (findFuns fd kt)) (hkt : P.funs[kt]? = some (itCfKeyF eqn))
    (heqn : P.HasAt eqn (eqNatsFuns eqn)) (h2 : KaryRefinement 2)
    (href : P.funs[ref]? = some (stRefF brep j)) (hrep : P.HasAt brep (replicateFuns brep))
    (hj : P.prims[j]? = some (karyRefinementPrim h2))
    (sv psV fxV fyV cv dd cd : Val) (k : ℕ) {ℓ ℓ' : ℕ} (src : Fin ℓ → Fin q) (b : Fin ℓ' → Fin q)
    (hx hy : List (Perm (Fin q))) (cX : (Fin 2 → Fin q) → ℕ) (cache : List (ItCfEnt q))
    (hq : 3 ≤ q) (hcX : ∀ z, cX z ≤ q ^ 2)
    (hcache : ∀ a ∈ cache, (∀ z, a.2.1 z < 2 * q ^ 2) ∧ (∀ z, a.2.2 z < 2 * q ^ 2)) {V B : ℕ}
    (hV : (Val.list [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd,
      stTv src], stTv b, itCfWO hx hy cX cache]).wt + 100 * (q ^ 2 + 1) ^ 2 ≤ V)
    (hB1 : itCfB Co Do (itCfColIn hy b).wt ≤ B) (hBl : itCfLkC (4 * V + 6) ≤ B)
    (hBr : (karyRefinementPrim h2).bound (karyEnc cX (orbColOut (gens hy) b)) +
      30 * (q ^ 2 + 1) ^ 2 + stRefK * (6 * V + 20 + 1) ^ 2 ≤ B)
    (hBo : ∀ r : (Fin 2 → Fin q) → ℕ, (∀ z, r z < 2 * q ^ 2) →
      itCfB Co Do (itCfOrbIn hx src r).wt ≤ B ∧ itCfB Co Do (itCfOrbIn hy b r).wt ≤ B) :
    FunAll P f (.list [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd,
      stTv src], stTv b, itCfWO hx hy cX cache]) (fun w cost =>
      ∃ (d d' : (Fin 2 → Fin q) → ℕ) (cache' : List (ItCfEnt q)),
        ItCfBinStep cX (orbColOut (gens hy) b) cache cache' d d' ∧
        w = .list [itCfOutV (orbitalOut (fun _ => d) (gens hx) src),
          itCfOutV (orbitalOut (fun _ => d') (gens hy) b), itCfWO hx hy cX cache'] ∧
        cost ≤ itCfO2C V B) := by
  -- names
  set st : Val := .list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv] with hst
  set Kv : Val := .list [st, dd, cd, stTv src] with hKv
  set wO := itCfWO hx hy cX cache with hwO
  set cvV : Val := .list (cache.map itCfEntV) with hcvV
  set x : Val := .list [Kv, stTv b, wO] with hx'
  obtain ⟨W, hW⟩ : ∃ W, W = 200 * (V + B) + 400 := ⟨_, rfl⟩
  -- weights of the input
  have ex : (Val.list [Kv, stTv b, wO]).wt = x.wt := rfl
  have wKv : Kv.wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wtb : (stTv b).wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wwO : wO.wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wst : st.wt < Kv.wt := wt_le_wt_list (by simp [hKv])
  have wsrc : (stTv src).wt < Kv.wt := wt_le_wt_list (by simp [hKv])
  have wkq : (Val.list [.nat k, .nat q]).wt < st.wt := wt_le_wt_list (by simp [hst])
  have wq : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have ewO : wO = .list [encGroup hx, encGroup hy, encKColoring cX, cvV] := rfl
  have wgx : (encGroup hx).wt < wO.wt := by rw [ewO]; exact wt_le_wt_list (by simp)
  have wgy : (encGroup hy).wt < wO.wt := by rw [ewO]; exact wt_le_wt_list (by simp)
  have wcX : (encKColoring cX).wt < wO.wt := by rw [ewO]; exact wt_le_wt_list (by simp)
  have wcv : cvV.wt < wO.wt := by rw [ewO]; exact wt_le_wt_list (by simp)
  have ecv : cvV.wt = (Val.list (cache.map itCfEntV)).wt := rfl
  have hlen : cache.length < cvV.wt := by
    have := length_lt_wt_list (cache.map itCfEntV); simpa [hcvV] using this
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
  have hqq : (q ^ 2 + 1) ≤ (q ^ 2 + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcY7 : ∀ z, (orbColOut (gens hy) b) z ≤ q ^ 2 := itCf_orbColOut_le_sq hq _ _
  have hq9 : 9 ≤ q ^ 2 := by nlinarith
  have hcYlt : ∀ z, (orbColOut (gens hy) b) z < 2 * q ^ 2 := fun z => by have := hcY7 z; omega
  have wcY : (encKColoring (orbColOut (gens hy) b)).wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hcYlt
  have hBo1 := fun r hr => (hBo r hr).1
  have hBo2 := fun r hr => (hBo r hr).2
  -- the first three values
  have d1 := StDC.get (StDC.get (StDC.arg (P := P) (W := W) (vs := [Kv, stTv b, wO]) (rest := []) (j := 0)
      (v := Kv) rfl (by omega) (by omega) (by omega)) (StDC.nat 0 (by omega)) (v := st)
      (vs := [st, dd, cd, stTv src]) rfl (by omega))
    (StDC.nat 1 (by omega)) (v := .list [.nat k, .nat q]) (vs := [sv, .list [.nat k, .nat q], psV,
      fxV, fyV, cv]) rfl (by omega)
  have d1' := StDC.get d1 (StDC.nat 1 (by omega)) (v := .nat q) (vs := [.nat k, .nat q]) rfl
    (by omega)
  suffices hs : EvalAll P [x] (itCfO2F fcol fd ref forb) (fun w cost =>
      (∃ (d d' : (Fin 2 → Fin q) → ℕ) (cache' : List (ItCfEnt q)),
        ItCfBinStep cX (orbColOut (gens hy) b) cache cache' d d' ∧
        w = .list [itCfOutV (orbitalOut (fun _ => d) (gens hx) src),
          itCfOutV (orbitalOut (fun _ => d') (gens hy) b), itCfWO hx hy cX cache']) ∧
        cost ≤ itCfO2C V B) from
    FunAll.intro hf (hs.mono fun w c ⟨⟨d, d', c', h1, h2⟩, h3⟩ => ⟨d, d', c', h1, h2, h3⟩)
  unfold itCfO2F
  refine EvalAll.letE (d1'.mono (n' := 20) (E' := 0) (by omega) (by omega)).det
    fun v1 c1 ⟨hv1, hc1⟩ => ?_
  subst hv1
  -- the orbital coloring of the target
  have hcol := hobj.col hy b
  have wcin : (itCfColIn hy b).wt ≤ 6 * V + 7 := by
    unfold itCfColIn
    have := wt_list3_le (.nat q) (encGroup hy) (stTv b)
    omega
  have d2 := StDC.call (StDC.mk3 (W := W) (StDC.var' (P := P) (env := [x, .nat q]) (i := 1) (v := .nat q) rfl
      (by omega)) (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega)
        (by omega) (by omega)) (StDC.nat 1 (by omega)) (v := encGroup hy)
        (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega))
      (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 1) (v := stTv b) rfl (by omega) (by omega)
        (by omega)) (by show (itCfColIn hy b).wt ≤ W; omega) (by omega))
    (hcol.mono fun w c h => ⟨h.1, h.2.trans hB1⟩) (by omega)
  refine EvalAll.letE (d2.mono (n' := 40) (E' := B) (by omega) (by omega)).det
    fun v2 c2 ⟨hv2, hc2⟩ => ?_
  subst hv2
  -- the lookup
  have wlk : (Val.list [encKColoring (orbColOut (gens hy) b), cvV]).wt ≤ 4 * V + 6 := by
    have := wt_list2_le (encKColoring (orbColOut (gens hy) b)) cvV; omega
  have hlk := it_cfLk_spec hfd hkt heqn (orbColOut (gens hy) b) cache wlk
  have hidx := itCfIdx_spec cache (orbColOut (gens hy) b)
  have hidxle : itCfIdx cache (orbColOut (gens hy) b) ≤ cache.length := List.findIdx_le_length
  have d3 := StDC.call (StDC.mk2 (W := W) (StDC.var' (P := P) (env := [x, .nat q, encKColoring (orbColOut (gens hy) b)]) (i := 2)
      (v := encKColoring (orbColOut (gens hy) b)) rfl (by omega)) (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2)
        (v := wO) rfl (by omega) (by omega) (by omega)) (StDC.nat 3 (by omega)) (v := cvV)
        (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega))
      (by omega) (by omega)) (hlk.mono hBl)
    (by have := wt_nat_le (itCfIdx cache (orbColOut (gens hy) b)); omega)
  refine EvalAll.letE (d3.mono (n' := 40) (E' := B) (by omega) (by omega)).det
    fun v3 c3 ⟨hv3, hc3⟩ => ?_
  subst hv3
  -- the values of the branch
  set env4 : List Val := [x, .nat q, encKColoring (orbColOut (gens hy) b), .nat (itCfIdx cache (orbColOut (gens hy) b))] with henv4
  have g2 : StDC P env4 (.get (arg 2) (.nat 3)) cvV 7 0 W :=
    (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega) (by omega)
      (by omega)) (StDC.nat 3 (by omega)) (v := cvV)
      (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega)).mono
      (by omega) (by omega)
  have dc := StDC.arith' (op := .lt) (StDC.var' (P := P) (env := env4) (i := 3)
      (v := .nat (itCfIdx cache (orbColOut (gens hy) b))) rfl (by have := wt_nat_le (itCfIdx cache (orbColOut (gens hy) b)); omega))
    (StDC.length g2 (by rw [List.length_map]; omega))
    (z := if itCfIdx cache (orbColOut (gens hy) b) < cache.length then 1 else 0) (by simp [GI.Machine.BinOp.eval])
    (by split_ifs <;> omega)
  -- the value of the cache entry, its weight
  refine EvalAll.letE (Ra := fun v c => (∃ (d d' : (Fin 2 → Fin q) → ℕ)
      (cache' : List (ItCfEnt q)), ItCfBinStep cX (orbColOut (gens hy) b) cache cache' d d' ∧
      (∀ z, d z < 2 * q ^ 2) ∧ (∀ z, d' z < 2 * q ^ 2) ∧
      v = .list [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)] ∧
      (Val.list (cache'.map itCfEntV)).wt ≤ 8 * V + 20) ∧ c ≤ 60 * (W + 1) + B) ?_
    fun v c4 hv4 => ?_
  · refine EvalAll.ite dc.det (fun vc cc h => ⟨_, h.1⟩) fun z cc ⟨hz, hcc⟩ => ?_
    simp only [Val.nat.injEq] at hz
    subst hz
    rcases hidx with ⟨hlt, hkey⟩ | ⟨heq, hnone⟩
    · -- the key is in the cache
      rw [if_pos hlt]
      simp only [one_ne_zero, if_false]
      obtain ⟨a, ha⟩ : ∃ a, a = cache[itCfIdx cache (orbColOut (gens hy) b)]'hlt := ⟨_, rfl⟩
      have hmem : a ∈ cache := ha ▸ List.getElem_mem hlt
      have hget : (cache.map itCfEntV)[itCfIdx cache (orbColOut (gens hy) b)]? = some (itCfEntV a) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt, ha]; rfl
      have eea : (itCfEntV a).wt = (Val.list [encKColoring a.1,
          .list [encKColoring a.2.1, encKColoring a.2.2]]).wt := rfl
      have wa : (itCfEntV a).wt < cvV.wt := wt_le_wt_list (List.mem_map_of_mem hmem)
      have wa2 : (Val.list [encKColoring a.2.1, encKColoring a.2.2]).wt < (itCfEntV a).wt :=
        wt_le_wt_list (by simp [itCfEntV])
      have dt := StDC.mk2 (W := W) (StDC.get (StDC.get g2 (StDC.var' (P := P) (env := env4) (i := 3)
          (v := .nat (itCfIdx cache (orbColOut (gens hy) b))) rfl (by have := wt_nat_le (itCfIdx cache (orbColOut (gens hy) b)); omega))
          hget (by omega)) (StDC.nat 1 (by omega))
          (v := .list [encKColoring a.2.1, encKColoring a.2.2])
          (vs := [encKColoring a.1, .list [encKColoring a.2.1, encKColoring a.2.2]]) rfl
          (by omega)) g2 (by have := wt_list2_le (Val.list [encKColoring a.2.1,
            encKColoring a.2.2]) cvV; omega) (by omega)
      refine EvalAll.mono dt.det fun w cb ⟨hw, hcb⟩ => ⟨⟨a.2.1, a.2.2, cache, Or.inl ⟨rfl, ?_⟩,
        (hcache a hmem).1, (hcache a hmem).2, hw, by omega⟩, ?_⟩
      · have : a = ((orbColOut (gens hy) b), a.2.1, a.2.2) := by rw [← hkey, ha]
        rw [← this]; exact hmem
      · have := wt_list2_le (Val.list [encKColoring a.2.1, encKColoring a.2.2]) cvV
        have hc0 : cc ≤ 10 * (W + 1) := by omega
        rw [hw] at *
        omega
    · -- a new key: the refinement call
      have hnlt : ¬ itCfIdx cache (orbColOut (gens hy) b) < cache.length := by omega
      rw [if_neg hnlt]
      simp only [if_true]
      have wsr : (Val.list [.nat q, .list [encKColoring cX, encKColoring (orbColOut (gens hy) b)]]).wt ≤ 6 * V + 20 := by
        have := wt_list2_le (encKColoring cX) (encKColoring (orbColOut (gens hy) b))
        have := wt_list2_le (.nat q) (.list [encKColoring cX, encKColoring (orbColOut (gens hy) b)])
        omega
      have hsr := stRef_spec h2 href hrep hj cX (orbColOut (gens hy) b) hcX (fun z => by have := hcY7 z; omega) wsr
        (by omega)
      have darg := StDC.mk2 (W := W) (StDC.var' (P := P) (env := env4) (i := 1) (v := .nat q) rfl
          (by omega)) (StDC.mk2 (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO)
            rfl (by omega) (by omega) (by omega)) (StDC.nat 2 (by omega)) (v := encKColoring cX)
            (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega))
          (StDC.var' (P := P) (env := env4) (i := 2) (v := encKColoring (orbColOut (gens hy) b)) rfl (by omega))
          (by have := wt_list2_le (encKColoring cX) (encKColoring (orbColOut (gens hy) b)); omega) (by omega))
          (by omega) (by omega)
      refine EvalAll.letE (Ra := fun w c => KaryOut cX (orbColOut (gens hy) b) w ∧ c ≤ 20 * (W + 1) + B)
        (EvalAll.call_funAll darg.det fun v ca ⟨hv, hca⟩ => by
          subst hv
          exact hsr.mono fun w c ⟨hw, hc⟩ => ⟨hw, by
            obtain ⟨d, d', rfl, hd, hd', -⟩ := hw
            have : (encKColoring d).wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd
            have : (encKColoring d').wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd'
            have := wt_list2_le (encKColoring d) (encKColoring d')
            omega⟩) fun r cr ⟨hr, hcr⟩ => ?_
      obtain ⟨d, d', rfl, hd, hd', hJ⟩ := hr
      have wr : (encKColoring d).wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd
      have wr' : (encKColoring d').wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd'
      have wrr := wt_list2_le (encKColoring d) (encKColoring d')
      set env5 := env4 ++ [.list [encKColoring d, encKColoring d']] with henv5
      have g2' : StDC P env5 (.get (arg 2) (.nat 3)) cvV 7 0 W :=
        (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega)
          (by omega) (by omega)) (StDC.nat 3 (by omega)) (v := cvV)
          (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega)).mono
          (by omega) (by omega)
      have went : (itCfEntV ((orbColOut (gens hy) b), d, d')).wt ≤ 2 * (5 * (q ^ 2 + 1) ^ 2 +
          (Val.list [encKColoring d, encKColoring d']).wt) + 6 :=
        (wt_list2_le _ _).trans (by simp only; omega)
      have wsn := wt_list_snoc_le (cache.map itCfEntV) (itCfEntV ((orbColOut (gens hy) b), d, d'))
      have em : (cache ++ [((orbColOut (gens hy) b), d, d')]).map itCfEntV = cache.map itCfEntV ++
          [itCfEntV ((orbColOut (gens hy) b), d, d')] := by simp
      have dt := StDC.mk2 (W := W) (StDC.var' (P := P) (env := env5) (i := 4)
          (v := .list [encKColoring d, encKColoring d']) rfl (by omega))
        (StDC.snoc g2' (StDC.mk2 (StDC.var' (P := P) (env := env5) (i := 2) (v := encKColoring (orbColOut (gens hy) b)) rfl
          (by omega)) (StDC.var' (P := P) (env := env5) (i := 4)
          (v := .list [encKColoring d, encKColoring d']) rfl (by omega)) (by
            show (itCfEntV ((orbColOut (gens hy) b), d, d')).wt ≤ W; omega) (by omega)) (by
            show (Val.list (cache.map itCfEntV ++ [itCfEntV ((orbColOut (gens hy) b), d, d')])).wt ≤ W
            omega))
        (by
          show (Val.list [Val.list [encKColoring d, encKColoring d'],
            Val.list (cache.map itCfEntV ++ [itCfEntV ((orbColOut (gens hy) b), d, d')])]).wt ≤ W
          have := wt_list2_le (Val.list [encKColoring d, encKColoring d'])
              (Val.list (cache.map itCfEntV ++ [itCfEntV ((orbColOut (gens hy) b), d, d')])); omega) (by omega)
      refine EvalAll.mono dt.det fun w cb ⟨hw, hcb⟩ => ⟨⟨d, d', cache ++ [((orbColOut (gens hy) b), d, d')],
        Or.inr ⟨rfl, hnone, hJ, hd, hd'⟩, hd, hd', by rw [hw, em]; rfl, by rw [em]; omega⟩, ?_⟩
      have := wt_list2_le (Val.list [encKColoring d, encKColoring d'])
        (Val.list (cache.map itCfEntV ++ [itCfEntV ((orbColOut (gens hy) b), d, d')]))
      have eu : w.wt = (Val.list [Val.list [encKColoring d, encKColoring d'],
          Val.list (cache.map itCfEntV ++ [itCfEntV ((orbColOut (gens hy) b), d, d')])]).wt := by
        rw [hw]; rfl
      omega
  -- the two objects
  obtain ⟨⟨d, d', cache', hstep, hd, hd', hv, hcw⟩, hc4⟩ := hv4
  subst hv
  have hb1 := hBo1 d hd
  have hb2 := hBo2 d' hd'
  have wdd := wt_list2_le (encKColoring d) (encKColoring d')
  have wd : (encKColoring d).wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd
  have wd' : (encKColoring d').wt ≤ 5 * (q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd'
  have wres := wt_list2_le (Val.list [encKColoring d, encKColoring d'])
    (.list (cache'.map itCfEntV))
  set env5 : List Val := env4 ++ [(Val.list [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)])] with henv5
  have wio1 : (itCfOrbIn hx src d).wt ≤ 8 * V + 8 := by
    unfold itCfOrbIn
    have := wt_list4_le (.nat q) (encGroup hx) (stTv src) (encKColoring d)
    omega
  have wio2 : (itCfOrbIn hy b d').wt ≤ 8 * V + 8 := by
    unfold itCfOrbIn
    have := wt_list4_le (.nat q) (encGroup hy) (stTv b) (encKColoring d')
    omega
  have ho1 : FunDet P forb (itCfOrbIn hx src d) (itCfOutV (orbitalOut (fun _ => d) (gens hx) src))
      B := (hobj.orb hx src (fun _ => d)).mono fun w c h => ⟨h.1, h.2.trans hb1⟩
  have ho2 : FunDet P forb (itCfOrbIn hy b d') (itCfOutV (orbitalOut (fun _ => d') (gens hy) b))
      B := (hobj.orb hy b (fun _ => d')).mono fun w c h => ⟨h.1, h.2.trans hb2⟩
  have wo1 := FunDet.wt_lt ho1
  have wo2 := FunDet.wt_lt ho2
  have gd : StDC P env5 (.get (.var 4) (.nat 0)) (.list [encKColoring d, encKColoring d']) 3 0 W :=
    (StDC.get (StDC.var' (P := P) (env := env5) (i := 4) (v := (Val.list [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)])) rfl (by omega)) (StDC.nat 0 (by omega))
      (vs := [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)]) rfl
      (by omega)).mono (by omega) (by omega)
  have do1 := StDC.call (StDC.mk4 (W := W) (StDC.var' (P := P) (env := env5) (i := 1) (v := .nat q) rfl
      (by omega)) (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega)
        (by omega) (by omega)) (StDC.nat 0 (by omega)) (v := encGroup hx)
        (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega))
      (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 0) (v := Kv) rfl (by omega) (by omega)
        (by omega)) (StDC.nat 3 (by omega)) (v := stTv src) (vs := [st, dd, cd, stTv src]) rfl
        (by omega))
      (StDC.get gd (StDC.nat 0 (by omega)) (v := encKColoring d)
        (vs := [encKColoring d, encKColoring d']) rfl (by omega))
      (by show (itCfOrbIn hx src d).wt ≤ W; omega) (by omega)) ho1 (by omega)
  refine EvalAll.letE (do1.mono (n' := 40) (E' := B) (by omega) (by omega)).det fun o1 c5 ⟨ho1e, hc5⟩ => ?_
  subst ho1e
  set env6 : List Val := env5 ++ [itCfOutV (orbitalOut (fun _ => d) (gens hx) src)] with henv6
  have gd6 : StDC P env6 (.get (.var 4) (.nat 0)) (.list [encKColoring d, encKColoring d']) 3 0
      W :=
    (StDC.get (StDC.var' (P := P) (env := env6) (i := 4) (v := (Val.list [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)])) rfl (by omega)) (StDC.nat 0 (by omega))
      (vs := [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)]) rfl
      (by omega)).mono (by omega) (by omega)
  have do2 := StDC.call (StDC.mk4 (W := W) (StDC.var' (P := P) (env := env6) (i := 1) (v := .nat q) rfl
      (by omega)) (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega)
        (by omega) (by omega)) (StDC.nat 1 (by omega)) (v := encGroup hy)
        (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) rfl (by omega))
      (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 1) (v := stTv b) rfl (by omega) (by omega)
        (by omega))
      (StDC.get gd6 (StDC.nat 1 (by omega)) (v := encKColoring d')
        (vs := [encKColoring d, encKColoring d']) rfl (by omega))
      (by show (itCfOrbIn hy b d').wt ≤ W; omega) (by omega)) ho2 (by omega)
  refine EvalAll.letE (do2.mono (n' := 40) (E' := B) (by omega) (by omega)).det fun o2 c6 ⟨ho2e, hc6⟩ => ?_
  subst ho2e
  set oXv := itCfOutV (orbitalOut (fun _ => d) (gens hx) src) with hoXv
  set oYv := itCfOutV (orbitalOut (fun _ => d') (gens hy) b) with hoYv
  set env7 : List Val := env6 ++ [oYv] with henv7
  have wwO' : (itCfWO hx hy cX cache').wt ≤ 8 * (V + 8 * V + 20) + 8 := by
    unfold itCfWO
    have := wt_list4_le (encGroup hx) (encGroup hy) (encKColoring cX)
      (.list (cache'.map itCfEntV))
    omega
  have gw : ∀ (i : ℕ) (u : Val), i < 3 →
      [encGroup hx, encGroup hy, encKColoring cX, cvV][i]? = some u →
      StDC P env7 (.get (arg 2) (.nat i)) u 7 0 W := by
    intro i u hi hu
    have wu : u.wt ≤ wO.wt := by
      rw [ewO]; exact (wt_le_wt_list (List.mem_of_getElem? hu)).le
    exact (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl (by omega)
      (by omega) (by omega)) (StDC.nat i (by omega)) (v := u)
      (vs := [encGroup hx, encGroup hy, encKColoring cX, cvV]) hu (by omega)).mono
      (by omega) (by omega)
  have dfin := StDC.mk3 (W := W) (StDC.var' (P := P) (env := env7) (i := 5) (v := oXv) rfl (by omega))
    (StDC.var' (P := P) (env := env7) (i := 6) (v := oYv) rfl (by omega))
    (StDC.mk4 (gw 0 _ (by omega) rfl) (gw 1 _ (by omega) rfl) (gw 2 _ (by omega) rfl)
      (StDC.get (StDC.var' (P := P) (env := env7) (i := 4) (v := (Val.list [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)])) rfl (by omega))
        (StDC.nat 1 (by omega)) (v := .list (cache'.map itCfEntV))
        (vs := [.list [encKColoring d, encKColoring d'], .list (cache'.map itCfEntV)]) rfl
        (by omega))
      (by show (itCfWO hx hy cX cache').wt ≤ W; omega) (by omega))
    (by
      show (Val.list [oXv, oYv, itCfWO hx hy cX cache']).wt ≤ W
      have := wt_list3_le oXv oYv (itCfWO hx hy cX cache'); omega) (by omega)
  refine EvalAll.mono (dfin.mono (n' := 60) (E' := 0) (by omega) (by omega)).det
    fun w cb ⟨hw, hcb⟩ => ?_
  refine ⟨⟨d, d', cache', hstep, hw⟩, ?_⟩
  have := wt_list3_le oXv oYv (itCfWO hx hy cX cache')
  have eu : w.wt = (Val.list [oXv, oYv, itCfWO hx hy cX cache']).wt := by rw [hw]; rfl
  unfold itCfO2C
  omega

end GI.Impl
