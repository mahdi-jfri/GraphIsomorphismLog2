module

public import Workspace.Impl.TermJProgYg3
public import Workspace.Impl.TermJProgFlat

@[expose] public section

/-!
# Generators of `N^q` (program)

The lift step needs generators of the base group `N^q` inside `N ≀ Sym(q)`. For a generating
list `ns` of `N`, they are the local elements `(s⁻¹ at a; 1)` for every row `a` and `s ∈ ns`.

* `tmJNq_mem_iff`: these generate exactly the pairs `(d; 1)` with every `d i` in `⟨ns⟩`.
* `tmJ_nq_spec`: on `[ns, lc]` (with `lc = tmJLocCtx m q`) the program returns the list
  `tmJPermsVal (tmJNqList ns)`, on `Fin (m q)` through `finProdFinEquiv`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

section Math

variable {B : Type} {q : ℕ}

/-- The local elements of all rows. -/
def tmJNqList (ns : List (Perm B)) : List (Perm (B × Fin q)) :=
  ((List.finRange q).map fun a => ns.map fun s => tmJLoc a s⁻¹).flatten

/-- **The local elements generate `N^q`.** -/
theorem tmJNq_mem_iff (ns : List (Perm B)) (σ : Perm (B × Fin q)) :
    σ ∈ Subgroup.closure {τ | τ ∈ tmJNqList (q := q) ns} ↔
      ∃ d : Fin q → Perm B, (∀ i, d i ∈ Subgroup.closure {s | s ∈ ns}) ∧ σ = tmJP (d, 1) := by
  set K := Subgroup.closure {s | s ∈ ns}
  constructor
  · intro hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      rw [Set.mem_setOf_eq, tmJNqList, List.mem_flatten] at hτ
      obtain ⟨l, hl, hτl⟩ := hτ
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hτl
      refine ⟨Pi.mulSingle a s⁻¹, fun i => ?_, rfl⟩
      by_cases hi : i = a
      · subst hi; simpa using K.inv_mem (Subgroup.subset_closure hs)
      · simp [Pi.mulSingle_eq_of_ne hi, K.one_mem]
    | one => exact ⟨1, fun i => K.one_mem, tmJP_one.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨d', hd', rfl⟩ := hy
      refine ⟨fun i => d' i * d i, fun i => K.mul_mem (hd' i) (hd i), ?_⟩
      rw [tmJP_mul]
      simp
    | inv x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨fun i => (d i)⁻¹, fun i => K.inv_mem (hd i), ?_⟩
      rw [tmJP_inv]
      simp
  · rintro ⟨d, hd, rfl⟩
    let ψ : (Fin q → Perm B) →* Perm (B × Fin q) :=
      { toFun := fun d => tmJP (d⁻¹, 1)
        map_one' := by simpa using tmJP_one (B := B) (q := q)
        map_mul' := fun d d' => by
          rw [tmJP_mul]; congr 1 }
    have hle : Subgroup.pi Set.univ (fun _ : Fin q => K) ≤
        (Subgroup.closure {τ | τ ∈ tmJNqList (q := q) ns}).comap ψ := by
      rw [Subgroup.pi_le_iff]
      intro i
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change ψ (Pi.mulSingle i g) ∈ _
      have : ψ (Pi.mulSingle i g) = tmJLoc i g⁻¹ := by
        change tmJP ((Pi.mulSingle i g)⁻¹, 1) = tmJP (Pi.mulSingle i g⁻¹, 1)
        congr 2
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.mulSingle_eq_of_ne hj]
      rw [this]
      refine Subgroup.subset_closure ?_
      rw [Set.mem_setOf_eq, tmJNqList, List.mem_flatten]
      exact ⟨_, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩, List.mem_map.2 ⟨g, hg, rfl⟩⟩
    have hd' : d⁻¹ ∈ Subgroup.pi Set.univ (fun _ : Fin q => K) :=
      fun i _ => K.inv_mem (hd i)
    have := Subgroup.mem_comap.1 (hle hd')
    change tmJP ((d⁻¹)⁻¹, 1) ∈ _ at this
    rwa [inv_inv] at this

end Math

variable {m q : ℕ}

/-! ### The program -/

/-- On `[[ns, lc], a]`: map `tmJLocAF` (at row `a`) over the list `ns`. -/
def tmJNqRowF (mp : ℕ) : Expr :=
  .call mp (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 0)))

/-- On `[ns, lc]`: tabulate the rows `0, …, q - 1` and flatten. -/
def tmJNqF (rg tbR fl : ℕ) : Expr :=
  .call fl (.call tbR (mk2 (mk2 (arg 0) (arg 1)) (.call rg (.get (arg 1) (.nat 2)))))

/-- The value of the list of encoded permutations. -/
def tmJNqIn (ns : List (Perm (Fin m))) : Val := .list (ns.map encPerm)

/-- The cost of one row, in `W = wt ns + (m + 1) (q + 1)`. -/
def tmJNqRowK (W : ℕ) : ℕ := 10 ^ 15 * W ^ 9

theorem tmJ_nqRow_spec {P : Program} {f mp locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJNqRowF mp)) (hmp : P.HasAt mp (mapFuns mp locA))
    (hlocA : P.funs[locA]? = some (tmJLocAF dsA pr))
    (hds : P.funs[dsA]? = some (tmJDsAF rg tbA)) (hrg : P.HasAt rg (rangeFuns rg))
    (htb : P.HasAt tbA (mapFuns tbA tbe)) (htbe : P.funs[tbe]? = some tmJDsAEF)
    (hpr : TmJPairAt P pr prg prt prte) (ns : List (Perm (Fin m))) (a : Fin q) :
    FunDet P f (.list [.list [tmJNqIn ns, tmJLocCtx m q], .nat a])
      (tmJPermsVal (ns.map fun s => tmJLoc a s⁻¹))
      (tmJNqRowK ((tmJNqIn ns).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJNqRowF
  set W := (tmJNqIn ns).wt + (m + 1) * (q + 1) with hW
  have d0 := Det.arg' (P := P) (vs := [.list [tmJNqIn ns, tmJLocCtx m q], .nat a]) (rest := [])
    (j := 0) (v := .list [tmJNqIn ns, tmJLocCtx m q]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [tmJNqIn ns, tmJLocCtx m q], .nat a]) (rest := [])
    (j := 1) (v := .nat a) rfl
  have dns := Det.get' d0 (Det.nat 0) (vs := [tmJNqIn ns, tmJLocCtx m q]) (v := tmJNqIn ns) rfl
  have dlc := Det.get' d0 (Det.nat 1) (vs := [tmJNqIn ns, tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  have hM := mapList_spec hmp ns encPerm
    (fun s => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹)))
    (c := .list [tmJLocCtx m q, .nat a]) (fun s _ s' _ he => by rw [encPerm_injective he])
    (fun s _ => tmJ_locA_spec hlocA hds hrg htb htbe hpr a s)
  have dall := Det.call (Det.mk2 (Det.mk2 dlc d1) dns) hM
  have hval : Val.list (ns.map fun s =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹))) =
      tmJPermsVal (ns.map fun s => tmJLoc a s⁻¹) := by
    simp only [tmJPermsVal, List.map_map]
    rfl
  rw [hval] at dall
  refine dall.mono ?_
  clear_value W
  clear dall hM dlc dns d1 d0
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : (m + 1) * (q + 1) ≤ W := by omega
  have hY1 : 1 ≤ W := by omega
  have hV2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV23 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hV34 : W ^ 3 ≤ W ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hV49 : W ^ 4 ≤ W ^ 9 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hV1 2
  have hW8 : ((m + 1) * (q + 1)) ^ 8 ≤ W ^ 8 := Nat.pow_le_pow_left hV1 8
  have hmq2 : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  have hWW : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlen := length_lt_wt_list (ns.map encPerm)
  simp only [List.length_map] at hlen
  have hlen' : ns.length < (tmJNqIn ns).wt := hlen
  have wc := wt_tmJLocCtx_le m q
  have wa := wt_nat_le a
  have ha := a.2
  have wnl := wt_list2_le (tmJNqIn ns) (tmJLocCtx m q)
  have win := wt_list2_le (.list [tmJNqIn ns, tmJLocCtx m q]) (.nat a)
  have wca := wt_list2_le (tmJLocCtx m q) (.nat a)
  have wcL := wt_list2_le (.list [tmJLocCtx m q, .nat a]) (tmJNqIn ns)
  have wres := wt_tmJPermsVal_le (ns.map fun s => tmJLoc (q := q) a s⁻¹)
  simp only [List.length_map] at wres
  have P0 : ns.length * (8 * (m * q + 1) ^ 2 + 1) ≤ W * (9 * W ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e0 : W * (9 * W ^ 2) = 9 * W ^ 3 := by ring
  have P1 : ns.length * tmJLocK ((m + 1) * (q + 1)) ≤ 10 ^ 14 * W ^ 9 := by
    unfold tmJLocK
    have : ns.length * (10 ^ 14 * ((m + 1) * (q + 1)) ^ 8) ≤ W * (10 ^ 14 * W ^ 8) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hW8)
    have e : W * (10 ^ 14 * W ^ 8) = 10 ^ 14 * W ^ 9 := by ring
    omega
  have hin : (Val.list [Val.list [tmJLocCtx m q, .nat a], tmJNqIn ns]).wt =
      (Val.list [Val.list [tmJLocCtx m q, .nat a], .list (ns.map encPerm)]).wt := rfl
  have P2 : mapK * (ns.length + 1) * ((Val.list [Val.list [tmJLocCtx m q, .nat a],
      .list (ns.map encPerm)]).wt + (tmJPermsVal (ns.map fun s => tmJLoc (q := q) a s⁻¹)).wt + 1)
      ≤ 1000 * (2 * W) * (500 * W ^ 3) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * (2 * W) * (500 * W ^ 3) = 1000000 * W ^ 4 := by ring
  show _ ≤ 10 ^ 15 * W ^ 9
  omega

/-- The value of the flattened list. -/
theorem tmJNq_flatten (ns : List (Perm (Fin m))) :
    Val.list (((List.finRange q).map fun a =>
      (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).flatten) =
      tmJPermsVal (tmJNqList (q := q) ns) := by
  simp only [tmJPermsVal, tmJNqList, List.map_flatten, List.map_map, Function.comp_def]

/-- The cost of all rows. -/
def tmJNqK (W : ℕ) : ℕ := 10 ^ 18 * W ^ 30

structure TmJNqAt (P : Program) (f rg tbR row mp locA dsA tbA tbe pr prg prt prte fl app : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmJNqF rg tbR fl)
  hrg : P.HasAt rg (rangeFuns rg)
  htbR : P.HasAt tbR (mapFuns tbR row)
  hrow : P.funs[row]? = some (tmJNqRowF mp)
  hmp : P.HasAt mp (mapFuns mp locA)
  hlocA : P.funs[locA]? = some (tmJLocAF dsA pr)
  hds : P.funs[dsA]? = some (tmJDsAF rg tbA)
  htb : P.HasAt tbA (mapFuns tbA tbe)
  htbe : P.funs[tbe]? = some tmJDsAEF
  hpr : TmJPairAt P pr prg prt prte
  hfl : P.funs[fl]? = some (tmJFlatF (fl + 1))
  hflF : P.HasAt (fl + 1) (foldlFuns (fl + 1) (fl + 4))
  hst : P.funs[fl + 4]? = some (tmJFlatStepF app)
  happ : P.HasAt app (appendFuns app)

/-- **The generators of `N^q`.** -/
theorem tmJ_nq_spec {P : Program} {f rg tbR row mp locA dsA tbA tbe pr prg prt prte fl app : ℕ}
    (hA : TmJNqAt P f rg tbR row mp locA dsA tbA tbe pr prg prt prte fl app)
    (ns : List (Perm (Fin m))) :
    FunDet P f (.list [tmJNqIn ns, tmJLocCtx m q]) (tmJPermsVal (tmJNqList (q := q) ns))
      (tmJNqK ((tmJNqIn ns).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJNqF
  set W := (tmJNqIn ns).wt + (m + 1) * (q + 1) with hW
  have d0 := Det.arg' (P := P) (vs := [tmJNqIn ns, tmJLocCtx m q]) (rest := []) (j := 0)
    (v := tmJNqIn ns) rfl
  have d1 := Det.arg' (P := P) (vs := [tmJNqIn ns, tmJLocCtx m q]) (rest := []) (j := 1)
    (v := tmJLocCtx m q) rfl
  have dq := Det.get' d1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have dr := Det.call dq (tmJ_range_det hA.hrg q)
  have hT := tabulate_spec hA.htbR (c := .list [tmJNqIn ns, tmJLocCtx m q])
    (F := fun a : Fin q => tmJPermsVal (ns.map fun s => tmJLoc a s⁻¹))
    (B := tmJNqRowK W) (fun a =>
      tmJ_nqRow_spec hA.hrow hA.hmp hA.hlocA hA.hds hA.hrg hA.htb hA.htbe hA.hpr ns a)
  have dt := Det.call (Det.mk2 (Det.mk2 d0 d1) dr) hT
  have hrows : Val.list ((List.finRange q).map fun a =>
      tmJPermsVal (ns.map fun s => tmJLoc (q := q) a s⁻¹)) =
      Val.list (((List.finRange q).map fun a => (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).map Val.list) := by
    simp only [tmJPermsVal, List.map_map, Function.comp_def]
  rw [hrows] at dt
  have hF := tmJ_flat_spec hA.hfl hA.hflF hA.hst hA.happ ((List.finRange q).map fun a =>
    (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ))
  have dall := Det.call dt hF
  rw [tmJNq_flatten] at dall
  refine dall.mono ?_
  clear_value W
  clear dall hF dt hT dr dq d1 d0
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : (m + 1) * (q + 1) ≤ W := by omega
  have hY1 : 1 ≤ W := by omega
  have hpow : ∀ i j, i ≤ j → W ^ i ≤ W ^ j := fun i j h => Nat.pow_le_pow_right hY1 h
  have hlen := length_lt_wt_list (ns.map encPerm)
  simp only [List.length_map] at hlen
  have hlen' : ns.length < (tmJNqIn ns).wt := hlen
  have hmq2 : (m * q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left (hmq.trans hV1) 2
  have wrow : ∀ a : Fin q, (tmJPermsVal (ns.map fun s => tmJLoc (q := q) a s⁻¹)).wt ≤
      13 * W ^ 3 := by
    intro a
    have w := wt_tmJPermsVal_le (ns.map fun s => tmJLoc (q := q) a s⁻¹)
    simp only [List.length_map] at w
    have : ns.length * (8 * (m * q + 1) ^ 2 + 1) ≤ W * (9 * W ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := hpow 0 2 (by norm_num); simp at this; omega)
    have e : W * (9 * W ^ 2) = 9 * W ^ 3 := by ring
    have := hpow 0 3 (by norm_num); simp at this
    omega
  have wR : (Val.list ((List.finRange q).map fun a =>
      tmJPermsVal (ns.map fun s => tmJLoc (q := q) a s⁻¹))).wt ≤ 27 * W ^ 4 + 4 := by
    have := tmJ_wt_list_le (vs := (List.finRange q).map fun a =>
      tmJPermsVal (ns.map fun s => tmJLoc (q := q) a s⁻¹)) (E := 13 * W ^ 3) (by
        intro v hv
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        exact wrow a)
    simp only [List.length_map, List.length_finRange] at this
    have h1 : q * (2 * (13 * W ^ 3) + 1) ≤ W * (27 * W ^ 3) :=
      Nat.mul_le_mul (by omega) (by have := hpow 0 3 (by norm_num); simp at this; omega)
    have e : W * (27 * W ^ 3) = 27 * W ^ 4 := by ring
    omega
  rw [hrows] at wR
  have wc := wt_tmJLocCtx_le m q
  have wid := wt_ids_le q
  have w2 := wt_list2_le (tmJNqIn ns) (tmJLocCtx m q)
  have w3 := wt_list2_le (.list [tmJNqIn ns, tmJLocCtx m q]) (encFun fun i : Fin q => (i : ℕ))
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hV1 2
  have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left (hq1.trans hV1) 2
  have hq3 : (q + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left (hq1.trans hV1) 3
  have P1 : q * tmJNqRowK W ≤ 10 ^ 15 * W ^ 10 := by
    unfold tmJNqRowK
    have := Nat.mul_le_mul_right (10 ^ 15 * W ^ 9) (show q ≤ W by omega)
    have e : W * (10 ^ 15 * W ^ 9) = 10 ^ 15 * W ^ 10 := by ring
    omega
  have P2 : mapK * (q + 1) * ((Val.list [Val.list [tmJNqIn ns, tmJLocCtx m q],
      encFun fun i : Fin q => (i : ℕ)]).wt + (Val.list (((List.finRange q).map fun a =>
        (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).map Val.list)).wt
          + 1) ≤ 1000 * W * (300 * W ^ 4) := by
    unfold mapK
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    have := hpow 2 4 (by norm_num)
    have := hpow 1 4 (by norm_num); simp only [pow_one] at this
    omega
  have e2 : 1000 * W * (300 * W ^ 4) = 300000 * W ^ 5 := by ring
  have P3 : tmJFlatK (Val.list (((List.finRange q).map fun a =>
      (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
        encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).map Val.list)).wt ≤
      10 ^ 6 * (27 * W ^ 4 + 5) ^ 3 := by
    unfold tmJFlatK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have P4 : 10 ^ 6 * (27 * W ^ 4 + 5) ^ 3 ≤ 10 ^ 6 * (32 * W ^ 4) ^ 3 := by
    have := hpow 0 4 (by norm_num); simp at this
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e4 : 10 ^ 6 * (32 * W ^ 4) ^ 3 = 32768000000 * W ^ 12 := by ring
  have wrg : 10000 * (q + 1) ^ 3 ≤ 10000 * W ^ 3 := Nat.mul_le_mul_left _ hq3
  have wfl := tmJ_wt_flatten_le ((List.finRange q).map fun a =>
    (ns.map fun s => tmJLoc a s⁻¹).map fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ))
  rw [tmJNq_flatten] at wfl
  have h1 := hpow 1 30 (by norm_num)
  simp only [pow_one] at h1
  have wq := wt_nat_le q
  have h2 := hpow 2 30 (by norm_num)
  have h3 := hpow 3 30 (by norm_num)
  have h4 := hpow 4 30 (by norm_num)
  have h5 := hpow 5 30 (by norm_num)
  have h10 := hpow 10 30 (by norm_num)
  have h12 := hpow 12 30 (by norm_num)
  show _ ≤ 10 ^ 18 * W ^ 30
  omega

end GI.Impl
