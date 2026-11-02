/-
**Coset helpers.**

* `CosetOrEmpty n v C`: `v = []` and `C = ∅`, or `v` is a coset value of `C` (`CosetVal`).
  The answer format of a stage 2 program is this format on the image of the answer
  (`answerVal_iff`, `answerVal_of_cosetOrEmpty`, `cosetOrEmpty_of_answerVal`).
* `cosetMulFuns`: on `[encPerm y, [encPerm x, gv]]`, the coset value `[encPerm (y x), gv]` of
  `y • (x • G)` (`cosetMul_spec`).
* `cosetInterFuns`: the intersection `x • G ∩ H` of a coset with a subgroup `H` given by a
  membership test, when `G` is given by the list of its elements (`cosetInter_spec`). The result
  is `[]` or `[y, encGroup K]` with `K` the elements of `G ∩ H`.
-/
import Workspace.Lang.Prims.Ops
import Workspace.Lang.Lib.SmallGroup
import Workspace.Assembly.Encoding

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv
open scoped Pointwise

variable {n : ℕ}

/-! ### Cosets or the empty set -/

/-- `v = []` and `C = ∅`, or `v` is a coset value of `C`. -/
def CosetOrEmpty (n : ℕ) (v : Val) (C : Set (Perm (Fin n))) : Prop :=
  (v = .list [] ∧ C = ∅) ∨ CosetVal n v C

theorem CosetOrEmpty.unique {v : Val} {C D : Set (Perm (Fin n))} (hC : CosetOrEmpty n v C)
    (hD : CosetOrEmpty n v D) : C = D := by
  rcases hC with ⟨rfl, rfl⟩ | hC <;> rcases hD with ⟨hv, rfl⟩ | hD
  · rfl
  · obtain ⟨x, gs, h, -⟩ := hD; cases h
  · obtain ⟨x, gs, rfl, -⟩ := hC; cases hv
  · exact hC.unique hD

/-- **The answer format is a coset-or-empty value of the image.** -/
theorem answerVal_iff {Ω : Type} {k : ℕ} (e : Ω ≃ Fin k) (v : Val) (A : Set (Perm Ω)) :
    GI.Assembly.AnswerVal e v A ↔ CosetOrEmpty k v (GI.Assembly.toFin e '' A) := by
  unfold GI.Assembly.AnswerVal CosetOrEmpty
  rw [Set.image_eq_empty]

theorem answerVal_of_cosetOrEmpty {Ω : Type} {k : ℕ} (e : Ω ≃ Fin k) {v : Val}
    {C : Set (Perm (Fin k))} (h : CosetOrEmpty k v C) :
    GI.Assembly.AnswerVal e v (GI.Assembly.toFin e ⁻¹' C) := by
  rw [answerVal_iff, Set.image_preimage_eq _ (GI.Assembly.toFin e).surjective]
  exact h

theorem cosetOrEmpty_of_answerVal {Ω : Type} {k : ℕ} {e : Ω ≃ Fin k} {v : Val}
    {A : Set (Perm Ω)} (h : GI.Assembly.AnswerVal e v A) :
    CosetOrEmpty k v (GI.Assembly.toFin e '' A) := (answerVal_iff e v A).mp h

/-! ### Multiplying a coset by an element -/

/-- On `[encPerm y, [encPerm x, gv]]`: `[encPerm (y x), gv]`. -/
def cosetMulF (comp : ℕ) : Expr :=
  mk2 (.call comp (mk2 (arg 0) (.get (arg 1) (.nat 0)))) (.get (arg 1) (.nat 1))

/-- The program of `cosetMul`, at base `b` (five functions). -/
def cosetMulFuns (b : ℕ) : List Expr := [cosetMulF (b + 1)] ++ composeFuns (b + 1)

/-- **Multiplying a coset by an element.** For a coset value `v` of `C`, the result is a coset
value of `y • C`. -/
theorem cosetMul_spec {P : Program} {b : ℕ} (h : P.HasAt b (cosetMulFuns b))
    (y : Perm (Fin n)) {v : Val} {C : Set (Perm (Fin n))} (hv : CosetVal n v C) :
    FunAll P b (.list [encPerm y, v]) (fun w c => CosetVal n w (y • C) ∧
      c ≤ (permK + 20) * (n + 1) ^ 3 + 20 * (Val.list [encPerm y, v]).wt + 70) := by
  have he : P.funs[b]? = some (cosetMulF (b + 1)) := h.left.single
  have hc : P.HasAt (b + 1) (composeFuns (b + 1)) := by simpa using h.right
  obtain ⟨x, gs, rfl, rfl⟩ := hv
  set vs : List Val := [encPerm y, .list [encPerm x, encGroup gs]] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dx := Det.get' d1 (Det.nat 0) (show [encPerm x, encGroup gs][0]? = some (encPerm x) from rfl)
  have dg := Det.get' d1 (Det.nat 1) (show [encPerm x, encGroup gs][1]? = some (encGroup gs) from rfl)
  have dA := Det.mk2 (Det.call (Det.mk2 d0 dx) (compose_spec hc y x)) dg
  refine FunAll.intro he (dA.post fun c hc' => ⟨⟨y * x, gs, rfl, by rw [smul_smul]⟩, ?_⟩)
  have w1 := wt_list2_le (encPerm y) (encPerm x)
  have w2 : (Val.list [encPerm x, encGroup gs]).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have w3 : (encPerm y).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have w4 : (encPerm x).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
  have w5 : (encGroup gs).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
  have w6 := wt_list2_le (encPerm (y * x)) (encGroup gs)
  have w7 := wt_encPerm_le (y * x)
  have w8 := wt_encPerm_le x
  have hN : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e : (permK + 20) * (n + 1) ^ 3 = permK * (n + 1) ^ 3 + 20 * (n + 1) ^ 3 := by ring
  omega

/-! ### Intersecting a coset with a subgroup -/

/-- If `y ∈ x • G ∩ H`, then `x • G ∩ H = y • (G ⊓ H)`. -/
theorem coset_inter_eq {G H : Subgroup (Perm (Fin n))} {x y : Perm (Fin n)}
    (hy : y ∈ x • (G : Set (Perm (Fin n))) ∩ (H : Set (Perm (Fin n)))) :
    x • (G : Set (Perm (Fin n))) ∩ (H : Set (Perm (Fin n))) =
      y • ((G ⊓ H : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  obtain ⟨⟨g₀, hg₀, rfl⟩, hyH⟩ := hy
  simp only [smul_eq_mul, SetLike.mem_coe] at hg₀ hyH
  ext z
  simp only [Set.mem_inter_iff, Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hzH⟩
    refine ⟨(x * g₀)⁻¹ * (x * g), ⟨?_, ?_⟩, by group⟩
    · rw [show (x * g₀)⁻¹ * (x * g) = g₀⁻¹ * g by group]
      exact G.mul_mem (G.inv_mem hg₀) hg
    · exact H.mul_mem (H.inv_mem hyH) hzH
  · rintro ⟨k, ⟨hkG, hkH⟩, rfl⟩
    exact ⟨⟨g₀ * k, G.mul_mem hg₀ hkG, by group⟩, H.mul_mem hyH hkH⟩

/-- The list of all elements of a subgroup generates it. -/
theorem gens_of_mem_iff {K : Subgroup (Perm (Fin n))} {ks : List (Perm (Fin n))}
    (h : ∀ σ, σ ∈ ks ↔ σ ∈ K) : gens ks = K := by
  unfold gens
  have : {g | g ∈ ks} = (K : Set (Perm (Fin n))) := Set.ext h
  rw [this, Subgroup.closure_eq]

/-- On `[encPerm x, encPerm g]`: `encPerm (x g)`. -/
def mulLeftF (comp : ℕ) : Expr := .call comp (mk2 (arg 0) (arg 1))

theorem mulLeft_spec {P : Program} {f comp : ℕ} (hf : P.funs[f]? = some (mulLeftF comp))
    (hc : P.HasAt comp (composeFuns comp)) (x g : Perm (Fin n)) :
    FunDet P f (.list [encPerm x, encPerm g]) (encPerm (x * g)) (31000 * (n + 1) ^ 3) := by
  have d0 := Det.arg' (P := P) (vs := [encPerm x, encPerm g]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm x, encPerm g]) (rest := []) (j := 1) rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 d0 d1) (compose_spec hc x g)).mono ?_)
  have w1 := wt_list2_le (encPerm x) (encPerm g)
  have w2 := wt_encPerm_le x
  have w3 := wt_encPerm_le g
  have w4 := wt_encPerm_le (x * g)
  have hN : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [permK]
  omega

/-- The entry of `cosetInter`: on `[c, encPerm x, els, n]`, the list `ys = x · els`, the
elements `Y` of `ys` that pass the test, and `[Y[0], encGroup K]` for the elements `K` of `els`
that pass the test, or `[]` if `Y` is empty. -/
def cosetInterEntry (b tfl : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (arg 1) (arg 2)))
    (.letE (.call tfl (mk2 (arg 0) (.var 1)))
      (.ite (.length (.var 2))
        (mk2 (.get (.var 2) (.nat 0)) (.call (b + 9) (mk2 (arg 3) (.call tfl (mk2 (arg 0) (arg 2))))))
        .nil))

/-- The program of `cosetInter`, at base `b` (19 functions), with the test at `tf`. -/
def cosetInterFuns (b tf : ℕ) : List Expr :=
  [cosetInterEntry b (b + 16)] ++ mapFuns (b + 1) (b + 4) ++ [mulLeftF (b + 5)] ++
    composeFuns (b + 5) ++ mkGroupFuns (b + 9) ++ filterFuns (b + 16) tf

theorem getElem?_zero_map_head {α : Type} {f : α → Val} {l : List α} (h : l ≠ []) :
    (l.map f)[0]? = some (f (l.head h)) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

theorem wt_perms_le_S {l : List (Perm (Fin n))} {m S : ℕ} (hl : l.length ≤ m)
    (hS : (m + 2) * (n + 1) ≤ S) : (Val.list (l.map encPerm)).wt ≤ 13 * S ^ 2 := by
  have h1 := wt_list_encPerms_le l
  have h2 : ((l.length + 1) * (n + 1)) ^ 2 ≤ S ^ 2 :=
    Nat.pow_le_pow_left (le_trans (Nat.mul_le_mul_right _ (by omega)) hS) 2
  omega

theorem wt_group_le_S {l : List (Perm (Fin n))} {m S : ℕ} (hl : l.length ≤ m)
    (hS : (m + 2) * (n + 1) ≤ S) : (encGroup l).wt ≤ 40 * S ^ 2 := by
  have h1 := wt_encGroup_le l
  have h2 : ((l.length + 2) * (n + 1)) ^ 2 ≤ S ^ 2 :=
    Nat.pow_le_pow_left (le_trans (Nat.mul_le_mul_right _ (by omega)) hS) 2
  omega

theorem wt_perm_le_S {m S : ℕ} (hS : (m + 2) * (n + 1) ≤ S) (g : Perm (Fin n)) :
    (encPerm g).wt ≤ 4 * S ^ 2 := by
  have h1 := wt_encPerm_le g
  have h2 : (n + 1) ^ 2 ≤ S ^ 2 :=
    Nat.pow_le_pow_left (le_trans (Nat.le_mul_of_pos_left _ (by omega)) hS) 2
  omega

/-- The value of the intersection. -/
def interVal (Y K : List (Perm (Fin n))) : Val :=
  if h : Y = [] then .list [] else .list [encPerm (Y.head h), encGroup K]

/-- The constant of `cosetInter`. -/
def cosetInterK : ℕ := 100000000

/-- **Intersecting a coset with a subgroup.** `els` lists the elements of `G`, and the test `tf`
decides membership in `H` (`q σ = true ↔ σ ∈ H`). On `[c, encPerm x, els, n]` the result is
`[]` if `x • G ∩ H` is empty, and otherwise a coset value of `x • G ∩ H`. -/
theorem cosetInter_spec {P : Program} {b tf : ℕ} (h : P.HasAt b (cosetInterFuns b tf))
    {c : Val} {G H : Subgroup (Perm (Fin n))} {els : List (Perm (Fin n))}
    (hels : ∀ σ, σ ∈ els ↔ σ ∈ G) {q : Perm (Fin n) → Bool} (hq : ∀ σ, q σ = true ↔ σ ∈ H)
    {T : ℕ} (ht : ∀ σ, FunDet P tf (.list [c, encPerm σ]) (boolVal (q σ)) T) (x : Perm (Fin n)) :
    FunAll P b (.list [c, encPerm x, .list (els.map encPerm), .nat n]) (fun w cost =>
      CosetOrEmpty n w (x • (G : Set (Perm (Fin n))) ∩ (H : Set (Perm (Fin n)))) ∧
      cost ≤ 2 * els.length * T + cosetInterK * ((els.length + 2) * (n + 1) + c.wt) ^ 4) := by
  simp only [cosetInterFuns] at h
  have he : P.funs[b]? = some (cosetInterEntry b (b + 16)) := h.left.left.left.left.left.single
  have hm : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by simpa using h.left.left.left.left.right
  have hml : P.funs[b + 4]? = some (mulLeftF (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right.single
  have hc : P.HasAt (b + 5) (composeFuns (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right
  have hg : P.HasAt (b + 9) (mkGroupFuns (b + 9)) := by
    simpa [mapFuns, loopFuns, composeFuns, Nat.add_assoc] using h.left.right
  have hfl : P.HasAt (b + 16) (filterFuns (b + 16) tf) := by
    simpa [mapFuns, loopFuns, composeFuns, mkGroupFuns, rangeFuns, appendFuns, Nat.add_assoc]
      using h.right
  -- the value
  set Y := (els.map (x * ·)).filter q with hY
  set K := els.filter q with hK
  have hYm : ∀ σ, σ ∈ Y ↔ σ ∈ x • (G : Set (Perm (Fin n))) ∧ σ ∈ H := by
    intro σ
    simp only [hY, List.mem_filter, List.mem_map, hq, Set.mem_smul_set, SetLike.mem_coe,
      smul_eq_mul, hels]
  have hKm : ∀ σ, σ ∈ K ↔ σ ∈ G ⊓ H := by
    intro σ
    simp only [hK, List.mem_filter, hq, hels, Subgroup.mem_inf]
  have hval : CosetOrEmpty n (interVal Y K) (x • (G : Set (Perm (Fin n))) ∩ (H : Set (Perm (Fin n)))) := by
    unfold interVal
    split_ifs with hY0
    · refine Or.inl ⟨rfl, Set.eq_empty_iff_forall_notMem.mpr fun σ hσ => ?_⟩
      have := (hYm σ).mpr hσ
      rw [hY0] at this; simp at this
    · refine Or.inr ⟨Y.head hY0, K, rfl, ?_⟩
      rw [gens_of_mem_iff hKm]
      exact coset_inter_eq ((hYm _).mp (List.head_mem hY0))
  -- the pieces
  have hMap := mapList_spec hm els encPerm (fun g => encPerm (x * g)) (c := encPerm x)
    (B := 31000 * (n + 1) ^ 3) (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun g _ => mulLeft_spec hml hc x g)
  have eys : (els.map fun g => encPerm (x * g)) = (els.map (x * ·)).map encPerm := by
    simp [List.map_map, Function.comp_def]
  rw [eys] at hMap
  have hFY : FunDet P (b + 16) (.list [c, .list ((els.map (x * ·)).map encPerm)])
      (.list (Y.map encPerm)) ((els.map (x * ·)).length * T + 3 * loopModK *
        ((els.map (x * ·)).length + 1) * ((Val.list [c, .list ((els.map (x * ·)).map encPerm)]).wt + 1)) :=
    FunAll.mono (transpAll_spec hfl (c := c) (els.map (x * ·)) q (fun σ _ => ht σ))
      fun w cost hw => ⟨hw.1, hw.2⟩
  have hFK : FunDet P (b + 16) (.list [c, .list (els.map encPerm)])
      (.list (K.map encPerm)) (els.length * T + 3 * loopModK * (els.length + 1) *
        ((Val.list [c, .list (els.map encPerm)]).wt + 1)) :=
    FunAll.mono (transpAll_spec hfl (c := c) els q (fun σ _ => ht σ)) fun w cost hw => ⟨hw.1, hw.2⟩
  set vs : List Val := [c, encPerm x, .list (els.map encPerm), .nat n] with hvs
  set ysv := Val.list ((els.map (x * ·)).map encPerm) with hysv
  have dM := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl)) hMap
  have dY := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [ysv]) (j := 0) rfl)
    (Det.var' (P := P) (env := [.list vs, ysv]) (i := 1) rfl)) hFY
  set env2 : List Val := [.list vs, ysv, .list (Y.map encPerm)] with henv2
  have dL := Det.length (Det.var' (P := P) (env := env2) (i := 2) rfl)
  have dIte := Det.ite dL (v := interVal Y K)
    (t := mk2 (.get (.var 2) (.nat 0)) (.call (b + 9) (mk2 (arg 3) (.call (b + 16) (mk2 (arg 0) (arg 2))))))
    (e := .nil)
    (ct := els.length * T + 20000000 * ((els.length + 2) * (n + 1) + c.wt) ^ 3)
    (ce := 5) (fun hx => ?_) (fun hx => ?_)
  rotate_left
  · have hY0 : Y ≠ [] := fun h0 => by simp [h0] at hx
    have hv : interVal Y K = .list [encPerm (Y.head hY0), encGroup K] := by
      unfold interVal; rw [dif_neg hY0]
    rw [hv]
    have dH := Det.get' (Det.var' (P := P) (env := env2) (i := 2) rfl) (Det.nat 0)
      (getElem?_zero_map_head hY0)
    have dK := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [ysv, .list (Y.map encPerm)])
      (j := 0) rfl) (Det.arg' (P := P) (vs := vs) (rest := [ysv, .list (Y.map encPerm)]) (j := 2) rfl)) hFK
    have dG := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [ysv, .list (Y.map encPerm)])
      (j := 3) rfl) dK) (mkGroup_spec hg K)
    refine (Det.mk2 dH dG).mono ?_
    clear dH dG dK dL dY dM hFY hFK hMap
    have hYl : Y.length ≤ els.length := by
      simp only [hY]; exact (List.length_filter_le _ _).trans (by simp)
    have hKl : K.length ≤ els.length := by simp only [hK]; exact List.length_filter_le _ _
    generalize hS : (els.length + 2) * (n + 1) + c.wt = S
    have hS0 : (els.length + 2) * (n + 1) ≤ S := by omega
    have hcS : c.wt ≤ S := by omega
    have hnS : n + 2 ≤ S := by
      have := (le_S els.length n).2; have := Nat.mul_le_mul_right (n + 1) (show 1 ≤ els.length + 2 by omega)
      nlinarith
    have hlS : els.length + 2 ≤ S := le_trans (le_S els.length n).1 hS0
    have w1 := wt_perms_le_S (le_refl _) hS0 (l := els)
    have w2 := wt_perms_le_S hYl hS0
    have w3 := wt_perms_le_S hKl hS0
    have w4 := wt_group_le_S hKl hS0
    have w5 := wt_perm_le_S hS0 x
    have w6 := wt_perm_le_S hS0 (Y.head hY0)
    have w7 := wt_nat_le n
    have w8 := wt_list4_le c (encPerm x) (.list (els.map encPerm)) (.nat n)
    have w9 := wt_list2_le c (.list (els.map encPerm))
    have w10 := wt_list2_le (.nat n) (.list (K.map encPerm))
    have w11 := wt_list2_le (encPerm (Y.head hY0)) (encGroup K)
    have wvs : (Val.list vs).wt = (Val.list [c, encPerm x, .list (els.map encPerm), .nat n]).wt := rfl
    have hS1 : 1 ≤ S := by omega
    have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
    have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
    have h5 : 3 * loopModK * (els.length + 1) *
        ((Val.list [c, Val.list (List.map encPerm els)]).wt + 1) ≤ 3 * loopModK * S * (40 * S ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h6 : mkGroupK * ((K.length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * S ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_trans (Nat.mul_le_mul_right _ (by omega)) hS0) 3)
    have e5 : 3 * loopModK * S * (40 * S ^ 2) = 120000 * S ^ 3 := by simp only [loopModK]; ring
    simp only [mkGroupK] at h6 ⊢
    omega
  · have hY0 : Y = [] := by simpa using hx
    have hv : interVal Y K = .list [] := by unfold interVal; rw [dif_pos hY0]
    rw [hv]; exact Det.nil
  refine FunAll.intro he ((Det.letE dM (Det.letE dY dIte)).post fun cost hcost => ⟨hval, ?_⟩)
  clear dIte dL dY dM hFY hFK hMap
  have hYl : Y.length ≤ els.length := by
    simp only [hY]; exact (List.length_filter_le _ _).trans (by simp)
  have hKl : K.length ≤ els.length := by simp only [hK]; exact List.length_filter_le _ _
  have hml : (List.map (fun x_1 => x * x_1) els).length = els.length := List.length_map _
  have hmY : (List.map encPerm Y).length = Y.length := List.length_map _
  rw [hml] at hcost
  generalize hS : (els.length + 2) * (n + 1) + c.wt = S at hcost
  have hS0 : (els.length + 2) * (n + 1) ≤ S := by omega
  have hcS : c.wt ≤ S := by omega
  have hnS : n + 1 ≤ S := le_trans (le_S els.length n).2 hS0
  have hlS : els.length + 2 ≤ S := le_trans (le_S els.length n).1 hS0
  have w1 := wt_perms_le_S (le_refl _) hS0 (l := els)
  have w2 := wt_perms_le_S hYl hS0
  have w3 : ysv.wt ≤ 13 * S ^ 2 := wt_perms_le_S (by simp) hS0
  have w5 := wt_perm_le_S hS0 x
  have w7 := wt_nat_le n
  have w8 := wt_list4_le c (encPerm x) (.list (els.map encPerm)) (.nat n)
  have w9 := wt_list2_le c ysv
  have w10 := wt_list2_le (encPerm x) (.list (els.map encPerm))
  have wvs : (Val.list vs).wt = (Val.list [c, encPerm x, .list (els.map encPerm), .nat n]).wt := rfl
  have wI : (interVal Y K).wt ≤ 100 * S ^ 2 := by
    unfold interVal
    split_ifs with hY0
    · have := wt_list_le ([] : List Val); simp at this ⊢
      have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    · have := wt_list2_le (encPerm (Y.head hY0)) (encGroup K)
      have := wt_perm_le_S hS0 (Y.head hY0)
      have := wt_group_le_S hKl hS0
      have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
  have hS1 : 1 ≤ S := by omega
  have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have hS34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by omega)
  have hN3 : els.length * (n + 1) ^ 3 ≤ S ^ 4 := by
    have := Nat.mul_le_mul (le_trans (by omega : els.length ≤ S) le_rfl)
      (Nat.pow_le_pow_left hnS 3)
    calc els.length * (n + 1) ^ 3 ≤ S * S ^ 3 := this
      _ = S ^ 4 := by ring
  have h1 : els.length * (31000 * (n + 1) ^ 3) ≤ 31000 * S ^ 4 := by nlinarith
  have h2 : mapK * (els.length + 1) * ((Val.list [encPerm x, Val.list (List.map encPerm els)]).wt +
      ysv.wt + 1) ≤ mapK * S * (60 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 : 3 * loopModK * (els.length + 1) * ((Val.list [c, ysv]).wt + 1) ≤
      3 * loopModK * S * (40 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : mapK * S * (60 * S ^ 2) = 60000 * S ^ 3 := by simp only [mapK]; ring
  have e3 : 3 * loopModK * S * (40 * S ^ 2) = 120000 * S ^ 3 := by simp only [loopModK]; ring
  rw [Nat.max_eq_left (by omega)] at hcost
  have eT : 2 * els.length * T = els.length * T + els.length * T := by ring
  simp only [cosetInterK]
  omega

end GI.Lang
