module

public import Workspace.Lang.Lib.SmallGroup
public import Workspace.Lang.Lib.Search
public import Workspace.Lang.Prims.Reduce

@[expose] public section

/-!
# The answer coset on a small domain, by enumeration

Algorithm 5, `Solve` with `|dom| ≤ N₀`: "return the answer by direct enumeration". On the
positions `Fin s` of the domain, the restricted group `G' = ⟨hs⟩` has at most `s!` elements. We
list them (`enum_spec`, with a bound `B ≥ s!` written into the program), keep those that carry
the coloring `fx` to `fy` (the transporter `T`) and those that fix `fx` (the stabilizer `K`).
If `T` is empty, the answer is empty. Otherwise it is the coset `τ K` for the first element `τ`
of `T`. The coset value `[τ, encGroup K]` may have up to `s!` generators, so the coset normal
form (`cosetNF_spec`, cited **Membership**) cuts it to at most `s²` generators.

* `composeFun_spec`: on `[encFun f, encPerm τ]`, `compose` returns `encFun (f ∘ τ)`.
* `colTest_spec`: the test `fy ∘ σ = fx` on `[[encFun fx, encFun fy], encPerm σ]`.
* `cosetFin_spec`: the answer coset `{σ ∈ ⟨hs⟩ | fy ∘ σ = fx}` as a `CosetC` value, at cost at
  most `cosetFinCost`, a polynomial in `B + s + 1` plus one membership bound per input weight.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms encGroup gens Membership)
open Equiv
open scoped Pointwise

variable {n : ℕ}

/-! ### Composing a list of numbers with a permutation -/

theorem encFun_eq_natList (f : Fin n → ℕ) : encFun f = natList ((List.finRange n).map f) := by
  simp [encFun, natList, List.map_map, Function.comp_def]

/-- The cost constant of `composeFun_spec`. -/
def cfunK : ℕ := 100000

/-- **Composition of a list of numbers with a permutation.** -/
theorem composeFun_spec {P : Program} {b : ℕ} (h : P.HasAt b (composeFuns b)) (f : Fin n → ℕ)
    {M : ℕ} (hf : ∀ i, f i ≤ M) (τ : Perm (Fin n)) :
    FunDet P b (.list [encFun f, encPerm τ]) (encFun (f ∘ τ)) (cfunK * (n + M + 1) ^ 3) := by
  set Z := n + M + 1 with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hE := wt_encFun_le f hf
  have hE' := wt_encPerm_le τ
  have hfc : ∀ i, (f ∘ τ) i ≤ M := fun i => hf _
  have hE'' := wt_encFun_le (f ∘ τ) hfc
  have z12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have z23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have nM : n * (2 * M + 5) ≤ 5 * Z ^ 2 := by nlinarith
  have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hf' : ∀ x ∈ (List.finRange n).map (fun i => Val.nat (τ i)),
      FunAll P (b + 3) (.list [encFun f, x]) (fun w cost =>
        (∀ i : Fin n, x = .nat i → w = .nat (f i)) ∧ cost ≤ 100 * Z ^ 2) := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    have hb : P.funs[b + 3]? = some composeF := by
      simpa [composeFuns, mapFuns, loopFuns] using h.right.single
    refine FunAll.intro hb ((Det.get' (Det.arg' (rest := []) (j := 0) rfl)
      (Det.arg' (j := 1) rfl) (encFun_getElem? f (τ j))).post fun cost hc => ⟨fun i hi => ?_, ?_⟩)
    · simp only [Val.nat.injEq] at hi
      rw [Fin.ext hi]
    · have h1 := wt_list2_le (encFun f) (.nat (τ j))
      have h2 := wt_nat_le (τ j)
      have h3 := wt_nat_le (f (τ j))
      have h4 := (τ j).isLt
      have h5 := hf (τ j)
      omega
  refine ((map_spec h.left hf').mono fun w cost hw => ?_)
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' := forall₂_map_eq (g := fun i => Val.nat ((f ∘ τ) i))
    (fun a _ w hw => by rw [hw (τ a) rfl]; rfl) hws
  subst hws'
  refine ⟨rfl, ?_⟩
  have ha := wt_list2_le (encFun f) (encPerm τ)
  simp only [List.map_map, List.length_map, List.length_finRange] at hc
  have hs : ((List.finRange n).map ((fun _ => 100 * Z ^ 2) ∘
      fun i => Val.nat (τ i))).sum = n * (100 * Z ^ 2) := by
    rw [show ((fun _ => 100 * Z ^ 2) ∘ fun i : Fin n => Val.nat (τ i)) =
      fun _ => 100 * Z ^ 2 from rfl, List.map_const', List.sum_replicate,
      List.length_finRange, smul_eq_mul]
  have e1 : (Val.list [encFun f, Val.list ((List.finRange n).map fun i => Val.nat (τ i))]).wt =
    (Val.list [encFun f, encPerm τ]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat ((f ∘ τ) i))).wt =
    (encFun (f ∘ τ)).wt := rfl
  rw [hs, e1, e2] at hc
  have h1 : mapK * (n + 1) * ((Val.list [encFun f, encPerm τ]).wt + (encFun (f ∘ τ)).wt + 1) ≤
      mapK * Z * (60 * Z ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h2 : n * (100 * Z ^ 2) ≤ 100 * Z ^ 3 := by
    have : n * (100 * Z ^ 2) ≤ Z * (100 * Z ^ 2) := Nat.mul_le_mul_right _ (by omega)
    have e : Z * (100 * Z ^ 2) = 100 * Z ^ 3 := by ring
    omega
  have h3 : mapK * Z * (60 * Z ^ 2) = 60000 * Z ^ 3 := by simp only [mapK]; ring
  simp only [cfunK]
  omega

/-! ### The color test -/

/-- The test of a permutation `σ` of `Fin n`: `fy ∘ σ = fx`. -/
def colQ (fx fy : Fin n → ℕ) (σ : Perm (Fin n)) : Bool := decide (fy ∘ σ = fx)

/-- The body of the color test: on `[[xs, ys], σ]`, compare `ys ∘ σ` with `xs`. -/
def colTestF (cp eq : ℕ) : Expr :=
  .call eq (mk2 (.call cp (mk2 (.get (arg 0) (.nat 1)) (arg 1))) (.get (arg 0) (.nat 0)))

/-- The cost constant of the color test. -/
def colK : ℕ := 10 ^ 7

theorem map_finRange_eq_iff (f g : Fin n → ℕ) :
    (List.finRange n).map f = (List.finRange n).map g ↔ f = g := by
  constructor
  · intro h
    funext i
    exact List.map_inj_left.mp h i (List.mem_finRange i)
  · rintro rfl; rfl

/-- **The color test.** -/
theorem colTest_spec {P : Program} {tf cp eq : ℕ} (htf : P.funs[tf]? = some (colTestF cp eq))
    (hcp : P.HasAt cp (composeFuns cp)) (heq : P.HasAt eq (eqNatsFuns eq))
    (fx fy : Fin n → ℕ) {M : ℕ} (hx : ∀ i, fx i ≤ M) (hy : ∀ i, fy i ≤ M) (σ : Perm (Fin n)) :
    FunDet P tf (.list [.list [encFun fx, encFun fy], encPerm σ]) (boolVal (colQ fx fy σ))
      (colK * (n + M + 1) ^ 3) := by
  set Z := n + M + 1 with hZ
  have hZ1 : 1 ≤ Z := by omega
  set c := Val.list [encFun fx, encFun fy] with hc
  set vs : List Val := [c, encPerm σ] with hvs
  have d0 := Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl) (Det.nat 1)
    (show [encFun fx, encFun fy][1]? = some (encFun fy) from rfl)
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dc := Det.call (Det.mk2 d0 d1) (composeFun_spec hcp fy hy σ)
  have dx := Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl) (Det.nat 0)
    (show [encFun fx, encFun fy][0]? = some (encFun fx) from rfl)
  have hE := eqNats_spec heq ((List.finRange n).map (fy ∘ σ)) ((List.finRange n).map fx)
  have hd : decide ((List.finRange n).map (fy ∘ σ) = (List.finRange n).map fx) =
      colQ fx fy σ := by
    unfold colQ; exact decide_eq_decide.mpr (map_finRange_eq_iff _ _)
  rw [← encFun_eq_natList, ← encFun_eq_natList, hd] at hE
  refine FunDet.intro htf ((Det.call (Det.mk2 dc dx) hE).mono ?_)
  -- the weights
  have wx := wt_encFun_le fx hx
  have wy := wt_encFun_le fy hy
  have wyσ := wt_encFun_le (fy ∘ σ) (fun i => hy _)
  have wσ := wt_encPerm_le σ
  have wc := wt_list2_le (encFun fx) (encFun fy)
  have wv := wt_list2_le c (encPerm σ)
  have w2 := wt_list2_le (encFun fy) (encPerm σ)
  have w3 := wt_list2_le (encFun (fy ∘ σ)) (encFun fx)
  have z12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have z23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have nM : n * (2 * M + 5) ≤ 5 * Z ^ 2 := by nlinarith
  have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlen : ((List.finRange n).map (fy ∘ σ)).length = n := by simp
  rw [hlen]
  have h1 : loopModK * (n + 1) * ((Val.list [encFun (fy ∘ σ), encFun fx]).wt + n + 4) ≤
      loopModK * Z * (60 * Z ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 : loopModK * Z * (60 * Z ^ 2) = 60000 * Z ^ 3 := by simp only [loopModK]; ring
  have hcf : cfunK * (n + M + 1) ^ 3 = 100000 * Z ^ 3 := by rw [hZ]; rfl
  have evs : (Val.list vs).wt = (Val.list [c, encPerm σ]).wt := rfl
  have ec : c.wt = (Val.list [encFun fx, encFun fy]).wt := rfl
  have wb' : (boolVal (colQ fx fy σ)).wt ≤ 3 := wt_boolVal_le _
  simp only [colK]
  omega

/-! ### The answer coset -/

/-- The stabilizer of the coloring `fx` in `G`. -/
def colStab (G : Subgroup (Perm (Fin n))) (fx : Fin n → ℕ) : Subgroup (Perm (Fin n)) where
  carrier := {σ | σ ∈ G ∧ fx ∘ σ = fx}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨G.mul_mem ha hb, ?_⟩
    rw [Perm.coe_mul, ← Function.comp_assoc, ha', hb']
  one_mem' := ⟨G.one_mem, rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨G.inv_mem ha, ?_⟩
    funext i
    have h := congrFun ha' (a⁻¹ i)
    have e : a (a⁻¹ i) = i := by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    simp only [Function.comp_apply, e] at h
    exact h.symm

/-- **The transporter is a coset of the stabilizer.** -/
theorem transp_eq_smul {G : Subgroup (Perm (Fin n))} {fx fy : Fin n → ℕ} {τ : Perm (Fin n)}
    (hτ : τ ∈ G) (hτ' : fy ∘ τ = fx) :
    {σ | σ ∈ G ∧ fy ∘ σ = fx} =
      τ • ((colStab G fx : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  ext σ
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  change σ ∈ G ∧ fy ∘ σ = fx ↔ τ⁻¹ * σ ∈ G ∧ fx ∘ ⇑(τ⁻¹ * σ) = fx
  have e : fx ∘ ⇑(τ⁻¹ * σ) = fy ∘ σ := by
    rw [← hτ', Perm.coe_mul, ← Function.comp_assoc, Function.comp_assoc fy, ← Perm.coe_mul,
      mul_inv_cancel, Perm.coe_one, Function.comp_id]
  rw [e, G.mul_mem_cancel_left (G.inv_mem hτ)]

theorem gens_eq_of_mem {H : Subgroup (Perm (Fin n))} {K : List (Perm (Fin n))}
    (h : ∀ σ, σ ∈ K ↔ σ ∈ H) : gens K = H := by
  unfold gens
  have : {g | g ∈ K} = (H : Set (Perm (Fin n))) := Set.ext h
  rw [this, Subgroup.closure_eq]

theorem colQ_iff (fx fy : Fin n → ℕ) (σ : Perm (Fin n)) : colQ fx fy σ = true ↔ fy ∘ σ = fx := by
  simp [colQ]

theorem sq_le (s : ℕ) : s * (2 * (2 * s) + 5) ≤ 9 * (s + 1) ^ 2 := by nlinarith

/-- A call of a function with a specification, on a known argument. -/
theorem EvalAll.call_spec' {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v : Val} {ca : ℕ}
    {R : Val → ℕ → Prop} (ha : Det P env a v ca) (hf : FunAll P f v R) :
    EvalAll P env (.call f a) (fun w c => ∃ cb, R w cb ∧ c ≤ ca + cb + w.wt + 1) :=
  EvalAll.call_funAll ha fun _ _ ⟨h1, h2⟩ => by
    subst h1
    exact hf.mono fun w cb hR => ⟨cb, hR, by omega⟩

/-- The body of the coset program, on `[s, encGroup hs, encFun fx, encFun fy]`. The number `B`
bounds the order of the group. -/
def cosetFinF (B en fl nf ap rg : ℕ) : Expr :=
  .letE (.call en (mk3 (.get (arg 1) (.nat 1)) (.nat B) (arg 0)))
  (.letE (.call fl (mk2 (mk2 (arg 2) (arg 3)) (.var 1)))
  (.letE (.call fl (mk2 (mk2 (arg 2) (arg 2)) (.var 1)))
  (.ite (.length (.var 2))
    (.call nf (mk2 (.get (.var 2) (.nat 0))
      (mk2 (arg 0) (.call ap (mk2 (mk1 (.call rg (arg 0))) (.var 3))))))
    .nil)))

/-- Where the pieces of the coset program sit. -/
structure CosetFinAt (P : Program) (f B en fl tf cp eq nf ap rg jm : ℕ) : Prop where
  entry : P.funs[f]? = some (cosetFinF B en fl nf ap rg)
  enAt : P.HasAt en (enumFuns en)
  flAt : P.HasAt fl (filterFuns fl tf)
  tfAt : P.funs[tf]? = some (colTestF cp eq)
  cpAt : P.HasAt cp (composeFuns cp)
  eqAt : P.HasAt eq (eqNatsFuns eq)
  nfAt : P.HasAt nf (cosetNFFuns nf jm)
  apAt : P.HasAt ap (appendFuns ap)
  rgAt : P.HasAt rg (rangeFuns rg)

/-- The cost bound of the coset program, with `Z = B + s + 1`: one coset normal form of a value
of weight at most `100 Z³`, and a polynomial in `Z`. -/
noncomputable def cosetFinCost (h : Membership) (s B : ℕ) : ℕ :=
  reduceCost h s (100 * (B + s + 1) ^ 3) + 10 ^ 20 * (B + s + 1) ^ 12

/-- **The answer coset by enumeration.** -/
theorem cosetFin_spec (hm : Membership) {P : Program} {f B en fl tf cp eq nf ap rg jm : ℕ}
    (h : CosetFinAt P f B en fl tf cp eq nf ap rg jm)
    (hj : P.prims[jm]? = some (membershipPrim hm))
    {s : ℕ} (hB : s.factorial ≤ B) (hs : List (Perm (Fin s))) (hl : hs.length ≤ s ^ 2)
    (fx fy : Fin s → ℕ) (hx : ∀ i, fx i ≤ 2 * s) (hy : ∀ i, fy i ≤ 2 * s) :
    FunAll P f (.list [.nat s, encGroup hs, encFun fx, encFun fy]) (fun u cost =>
      CosetC s u {σ | σ ∈ gens hs ∧ fy ∘ σ = fx} ∧ cost ≤ cosetFinCost hm s B) := by
  set gl := Val.list ((1 :: hs).map encPerm) with hgl
  have eg : encGroup hs = .list [.nat s, gl] := rfl
  set vs : List Val := [.nat s, .list [.nat s, gl], encFun fx, encFun fy] with hvs
  set a := Val.list vs with ha
  show FunAll P f a _
  refine FunAll.intro h.entry ?_
  set Z := B + s + 1 with hZ
  -- 1. the elements of the group
  have hcard : Nat.card (genGroup (1 :: hs)) ≤ B := by
    refine le_trans ?_ hB
    have h1 := Subgroup.card_le_card_group (genGroup (1 :: hs))
    rw [Nat.card_eq_fintype_card (α := Perm (Fin s)), Fintype.card_perm, Fintype.card_fin] at h1
    exact h1
  have dG := Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl) (Det.nat 1)
    (show [Val.nat s, gl][1]? = some gl from rfl)
  have dA := Det.mk3 dG (Det.nat (P := P) (env := [a]) B)
    (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl)
  refine EvalAll.letE (EvalAll.call_spec' dA (enum_spec h.enAt (1 :: hs) hcard)) ?_
  rintro w1 c1 ⟨cb1, ⟨els, rfl, hnd, hmem, hcb1⟩, hc1⟩
  have hlen : els.length ≤ B := by
    have := hnd.length_le_card
    rw [Fintype.card_perm, Fintype.card_fin] at this
    omega
  -- 2. the transporter
  have dT := Det.call (Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [Val.list (els.map encPerm)]) (j := 2) rfl)
      (Det.arg' (P := P) (vs := vs) (rest := [Val.list (els.map encPerm)]) (j := 3) rfl))
      (Det.var' (P := P) (env := [a, Val.list (els.map encPerm)]) (i := 1) rfl))
    ((transpAll_spec h.flAt (c := Val.list [encFun fx, encFun fy]) els (colQ fx fy)
      (fun σ _ => colTest_spec h.tfAt h.cpAt h.eqAt fx fy hx hy σ)).mono
      (fun w c hw => hw))
  refine EvalAll.letE dT ?_
  rintro _ c2 ⟨rfl, hc2⟩
  set T := els.filter (colQ fx fy) with hT
  -- 3. the stabilizer
  have dK := Det.call (Det.mk2 (Det.mk2
      (Det.arg' (P := P) (vs := vs) (rest := [Val.list (els.map encPerm), .list (T.map encPerm)]) (j := 2) rfl)
      (Det.arg' (P := P) (vs := vs) (rest := [Val.list (els.map encPerm), .list (T.map encPerm)]) (j := 2) rfl))
      (Det.var' (P := P) (env := [a, Val.list (els.map encPerm), .list (T.map encPerm)]) (i := 1) rfl))
    ((transpAll_spec h.flAt (c := Val.list [encFun fx, encFun fx]) els (colQ fx fx)
      (fun σ _ => colTest_spec h.tfAt h.cpAt h.eqAt fx fx hx hx σ)).mono
      (fun w c hw => hw))
  refine EvalAll.letE dK ?_
  rintro _ c3 ⟨rfl, hc3⟩
  set K := els.filter (colQ fx fx) with hK
  have hmemG : ∀ σ, σ ∈ els ↔ σ ∈ gens hs := fun σ => by
    rw [hmem σ]; exact Iff.of_eq (congrArg (σ ∈ ·) (gens_one_cons hs))
  have hKH : gens K = colStab (gens hs) fx := gens_eq_of_mem fun σ => by
    rw [hK, List.mem_filter, hmemG, colQ_iff]; rfl
  -- the weights so far
  have hZ1 : 1 ≤ Z := by omega
  have z12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have z23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have z34 : Z ^ 3 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have z46 : Z ^ 4 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have z612 : Z ^ 6 ≤ Z ^ 12 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have s2 : (s + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have s6 : (s + 1) ^ 6 ≤ Z ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have wEG : (Val.list [.nat s, gl]).wt ≤ 320 * (s + 1) ^ 6 := wt_encGroup_le_sq hl
  have wgl : gl.wt < (Val.list [.nat s, gl]).wt := wt_le_wt_list (by simp)
  have wns := wt_nat_le s
  have wnB := wt_nat_le B
  have wfx := wt_encFun_le fx hx
  have wfy := wt_encFun_le fy hy
  have sq : s * (2 * (2 * s) + 5) ≤ 9 * Z ^ 2 := (sq_le s).trans (by omega)
  have wvs := wt_list4_le (.nat s) (.list [.nat s, gl]) (encFun fx) (encFun fy)
  have evs : (Val.list vs).wt =
      (Val.list [.nat s, .list [.nat s, gl], encFun fx, encFun fy]).wt := rfl
  have WA : (Val.list vs).wt ≤ 1000 * Z ^ 6 := by omega
  have w3 := wt_list3_le gl (.nat B) (.nat s)
  have hlen1 : (1 :: hs).length + B + 4 * (s + 1) ^ 2 + 20 ≤ 30 * Z ^ 2 := by
    simp only [List.length_cons]
    have : s ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have Ccb1 : cb1 ≤ enumK * 30 ^ 6 * Z ^ 12 := by
    refine hcb1.trans ?_
    have := Nat.pow_le_pow_left hlen1 6
    have e : (30 * Z ^ 2) ^ 6 = 30 ^ 6 * Z ^ 12 := by ring
    rw [e] at this
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ this
  have wperm : ∀ σ : Perm (Fin s), (encPerm σ).wt ≤ 4 * Z ^ 2 := fun σ =>
    (wt_encPerm_le σ).trans (by omega)
  have wE : (Val.list (els.map encPerm)).wt ≤ 13 * Z ^ 3 := by
    have h1 := wt_list_le_of (els.map encPerm) (c := 4 * Z ^ 2) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ σ _ rfl; exact wperm σ)
    rw [List.length_map] at h1
    have h2 : els.length * (2 * (4 * Z ^ 2) + 1) ≤ Z * (9 * Z ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : Z * (9 * Z ^ 2) = 9 * Z ^ 3 := by ring
    omega
  have wT : (Val.list (T.map encPerm)).wt ≤ (Val.list (els.map encPerm)).wt :=
    wt_list_sublist (List.filter_sublist.map encPerm)
  have wK : (Val.list (K.map encPerm)).wt ≤ (Val.list (els.map encPerm)).wt :=
    wt_list_sublist (List.filter_sublist.map encPerm)
  have lT : T.length ≤ B := (List.length_filter_le _ _).trans hlen
  have lK : K.length ≤ B := (List.length_filter_le _ _).trans hlen
  have wc1 := wt_list2_le (encFun fx) (encFun fy)
  have wc2 := wt_list2_le (encFun fx) (encFun fx)
  have wcE1 := wt_list2_le (Val.list [encFun fx, encFun fy]) (Val.list (els.map encPerm))
  have wcE2 := wt_list2_le (Val.list [encFun fx, encFun fx]) (Val.list (els.map encPerm))
  have Pt : els.length * (colK * (s + 2 * s + 1) ^ 3) ≤ colK * 27 * Z ^ 4 := by
    have h1 : (s + 2 * s + 1) ^ 3 ≤ (3 * Z) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : els.length * (colK * (s + 2 * s + 1) ^ 3) ≤ Z * (colK * (3 * Z) ^ 3) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
    have e : Z * (colK * (3 * Z) ^ 3) = colK * 27 * Z ^ 4 := by ring
    omega
  have Pl1 : 3 * loopModK * (els.length + 1) *
      ((Val.list [Val.list [encFun fx, encFun fy], Val.list (els.map encPerm)]).wt + 1) ≤
      3 * loopModK * Z * (200 * Z ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have Pl2 : 3 * loopModK * (els.length + 1) *
      ((Val.list [Val.list [encFun fx, encFun fx], Val.list (els.map encPerm)]).wt + 1) ≤
      3 * loopModK * Z * (200 * Z ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have ePl : 3 * loopModK * Z * (200 * Z ^ 3) = 600000 * Z ^ 4 := by simp only [loopModK]; ring
  have C1 : c1 ≤ 10 ^ 17 * Z ^ 12 := by
    have e : enumK * 30 ^ 6 * Z ^ 12 = 14580000000000000 * Z ^ 12 := by simp only [enumK]; ring
    clear hc2 hc3
    omega
  have C2 : c2 ≤ 10 ^ 10 * Z ^ 6 := by
    have e : colK * 27 * Z ^ 4 = 270000000 * Z ^ 4 := by simp only [colK]; ring
    clear hc1 hc3
    omega
  have C3 : c3 ≤ 10 ^ 10 * Z ^ 6 := by
    have e : colK * 27 * Z ^ 4 = 270000000 * Z ^ 4 := by simp only [colK]; ring
    clear hc1 hc2
    omega
  clear hc1 hc2 hc3 hcb1 Ccb1 Pt Pl1 Pl2
  set env4 := [a, Val.list (els.map encPerm), Val.list (T.map encPerm), Val.list (K.map encPerm)] with henv4
  have dl := Det.length (Det.var' (P := P) (env := env4) (i := 2) rfl)
  obtain hTe | ⟨τ, rest, hTe⟩ : T = [] ∨ ∃ τ rest, T = τ :: rest := by
    cases T with
    | nil => exact Or.inl rfl
    | cons τ rest => exact Or.inr ⟨τ, rest, rfl⟩
  · -- no element carries `fx` to `fy`: the answer is empty
    rw [hTe] at dl
    refine (Det.ite_zero dl Det.nil).post fun c4 hc4 => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · refine Set.eq_empty_iff_forall_notMem.2 fun σ ⟨hσG, hσ⟩ => ?_
      have : σ ∈ T := by rw [hT, List.mem_filter, hmemG, colQ_iff]; exact ⟨hσG, hσ⟩
      rw [hTe] at this
      exact List.not_mem_nil this
    · have w0 : (Val.list []).wt = 4 := wt_list_nil
      simp only [List.map_nil, List.length_nil, w0] at hc4 ⊢
      unfold cosetFinCost
      rw [← hZ]
      omega
  · -- the coset of the first element
    have hτT : τ ∈ T := by rw [hTe]; exact List.mem_cons_self
    rw [hT, List.mem_filter, hmemG, colQ_iff] at hτT
    have hC : {σ | σ ∈ gens hs ∧ fy ∘ σ = fx} = τ • (gens K : Set (Perm (Fin s))) := by
      rw [hKH]; exact transp_eq_smul hτT.1 hτT.2
    have hv : CosetOrEmpty s (.list [encPerm τ, .list [.nat s, .list ([encPerm 1] ++
        K.map encPerm)]]) {σ | σ ∈ gens hs ∧ fy ∘ σ = fx} := Or.inr ⟨τ, K, rfl, hC⟩
    have dR : FunDet P rg (.nat s) (encPerm (1 : Perm (Fin s)))
        (loopModK * (s + 1) * ((Val.nat s).wt + s + (encPerm (1 : Perm (Fin s))).wt + 1)) :=
      (range_spec h.rgAt s).mono fun w c hw => by
        obtain ⟨rfl, hc⟩ := hw
        rw [range_eq_encPerm_one] at hc ⊢
        exact ⟨rfl, hc⟩
    set G1 := Val.list ([encPerm (1 : Perm (Fin s))] ++ K.map encPerm) with hG1
    have fAp : FunDet P ap (.list [.list [encPerm 1], .list (K.map encPerm)]) G1
        (loopModK * (K.length + 1) * ((Val.list [.list [encPerm 1], .list (K.map encPerm)]).wt +
          K.length + G1.wt + 1)) :=
      (append_spec h.apAt [encPerm 1] (K.map encPerm)).mono fun w c hw => by
        obtain ⟨rfl, hc⟩ := hw
        simp only [List.length_map] at hc
        exact ⟨rfl, hc⟩
    have dAp := Det.call (Det.mk2 (Det.mk1 (Det.call
      (Det.arg' (P := P) (vs := vs) (rest := env4.tail) (j := 0) rfl) dR))
      (Det.var' (P := P) (env := env4) (i := 3) rfl)) fAp
    have dArg := Det.mk2 (Det.get' (Det.var' (P := P) (env := env4) (i := 2) rfl) (Det.nat 0)
      (show (T.map encPerm)[0]? = some (encPerm τ) by rw [hTe]; rfl))
      (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := env4.tail) (j := 0) rfl) dAp)
    refine EvalAll.ite dl (fun _ _ hh => ⟨_, hh.1⟩) fun x cc hx => ?_
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Val.nat.injEq] at hx1
    have hx0 : x ≠ 0 := by rw [hx1, hTe]; simp
    rw [if_neg hx0]
    refine (EvalAll.call_spec' dArg (cosetNF_spec hm h.nfAt hj hv)).mono ?_
    rintro u c5 ⟨cb5, ⟨hu, hcb5⟩, hc5⟩
    refine ⟨hu, ?_⟩
    have wu : u.wt ≤ 700 * Z ^ 6 := by
      rcases hu with ⟨rfl, -⟩ | ⟨x', hs', rfl, hl', -⟩
      · simp only [wt_list_nil]; omega
      · have h1 := wt_list2_le (encPerm x') (encGroup hs')
        have h2 := wt_encGroup_le_sq hl'
        have h3 := wperm x'
        omega
    have wG1 : G1.wt ≤ 13 * Z ^ 3 := by
      have h1 := wt_list_le_of ([encPerm (1 : Perm (Fin s))] ++ K.map encPerm) (c := 4 * Z ^ 2) (by
        simp only [List.singleton_append, List.mem_cons, List.mem_map]
        rintro _ (rfl | ⟨σ, _, rfl⟩) <;> exact wperm _)
      simp only [List.singleton_append, List.length_cons, List.length_map] at h1
      have h2 : (K.length + 1) * (2 * (4 * Z ^ 2) + 1) ≤ Z * (9 * Z ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e : Z * (9 * Z ^ 2) = 9 * Z ^ 3 := by ring
      have e2 : G1 = Val.list (encPerm (1 : Perm (Fin s)) :: K.map encPerm) := rfl
      rw [e2]
      omega
    have w1 := wt_list1_le (encPerm (1 : Perm (Fin s)))
    have w11 := wperm 1
    have wτ := wperm τ
    have wa1 := wt_list2_le (Val.list [encPerm (1 : Perm (Fin s))]) (Val.list (K.map encPerm))
    have wa2 := wt_list2_le (.nat s) G1
    have wa3 := wt_list2_le (encPerm τ) (Val.list [.nat s, G1])
    have W5 : (Val.list [encPerm τ, Val.list [Val.nat s, G1]]).wt ≤ 100 * Z ^ 3 := by omega
    have Pr : loopModK * (s + 1) * ((Val.nat s).wt + s + (encPerm (1 : Perm (Fin s))).wt + 1) ≤
        loopModK * Z * (10 * Z ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have Pa : loopModK * (K.length + 1) *
        ((Val.list [Val.list [encPerm (1 : Perm (Fin s))], Val.list (List.map encPerm K)]).wt +
          K.length + G1.wt + 1) ≤ loopModK * Z * (100 * Z ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have ePr : loopModK * Z * (10 * Z ^ 2) = 10000 * Z ^ 3 := by simp only [loopModK]; ring
    have ePa : loopModK * Z * (100 * Z ^ 3) = 100000 * Z ^ 4 := by simp only [loopModK]; ring
    have hmono := reduceCost_mono hm s W5
    have C5 : cb5 ≤ reduceCost hm s (100 * Z ^ 3) + 10 ^ 4 * Z ^ 6 := by
      unfold cosetNFCost at hcb5
      omega
    have lTm : (List.map encPerm T).length ≤ B := by rw [List.length_map]; exact lT
    unfold cosetFinCost
    rw [← hZ]
    clear dG dA dT dK dl dR fAp dAp dArg hv hC hmono hcb5
    omega

end GI.Lang
