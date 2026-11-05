module

public import Workspace.Impl.AggItemHvBr

@[expose] public section

/-!
# Case 2a meets its contract, given the init program

The halving item of Case 2a (Lemma A.11) asks three kernel calls in every branch, on `x`, on
`y ∘ τ₀` and on `y ∘ τ₀ t`, and returns the two pieces. Its alignment `τ₀`, its twist `t`, the
kernel `K` and the generators of `A` are the same for all branches, so the case computes them
once, in its init program, and keeps them in the kept value (`ItHvKept`):

`w = [1, arg₀, arg₁, arg₂, a₀, a₀₁, gA]`, with `arg_i` the canonical values of the three calls,
`a₀ = toFin e τ₀`, `a₀₁ = toFin e (τ₀ t)` and `gA` generators of `A` on positions.

When the test of `halvingItem` fails, the kept value is `[0]` and every branch is empty.

`ItHvInitOK` is what the init program must do. `itS_c2a_caseOK` proves the contract
`ItSCaseOK` for the case `.twoA` from `ItHvInitOK`, with the branch step `itHvBF`
(`AggItemHvBr.lean`) and the piece program `itHvPcF` (`AggItemHvPc.lean`).

The candidate rounds after the init program are those of the base set whose halving choices at
`(Φ, Φ')` are `τ₀` and `t` (`itHvD`). They all have the same item script in every branch
(`it_hv_items_some`), so the step never splits the set of rounds.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The kept value -/

/-- **The facts of the kept value of the halving item.** -/
structure ItHvKept (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {L : SuppliedLabels S}
    (K : ItSCtx k S L) (w : Val) (τ₀ t : Perm Ω) : Prop where
  al : ItHvAl L.toGiantLabels (itHvPhi K) (itHvPhi' K) τ₀
  tw : ItHvTw L.toGiantLabels (itHvPhi K) t
  val : ∃ (gv kgv dv xv yv hv rv fv hh yv0 yv1 : Val) (N : ℕ) (gA : List (Perm (Fin k))),
    K.sv = .list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] ∧
    GroupValC k kgv (groupFin e (itHvKer L.toGiantLabels (itHvPhi K))) ∧
    ColorVal e c xv S.x ∧ ColorVal e c yv0 (S.y ∘ τ₀) ∧ ColorVal e c yv1 (S.y ∘ (τ₀ * t)) ∧
    gens gA = groupFin e (itHvH K τ₀ t).A ∧
    w = .list [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv yv0 hv N,
      winVal' k kgv dv xv yv1 hv N, encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)),
      .list (gA.map encPerm)]

variable (I : Iface) (Pg : Program)

/-- **What the init program of Case 2a must do**: on `K.v` it returns `[0]` if the test of
`halvingItem` fails, and a kept value with its facts otherwise, at cost and weight at most
`Xi W₀`. -/
def ItHvInitOK (F : Funs) (f0 : ℕ) (Xi : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → K.case = .twoA →
      FunAll Pg f0 K.v (fun w cost => cost ≤ Xi (I.inW .giant S) ∧ w.wt ≤ Xi (I.inW .giant S) ∧
        ((¬ ItHvCond K ∧ w = .list [.nat 0]) ∨ (ItHvCond K ∧ ∃ τ₀ t, ItHvKept e c K w τ₀ t)))

/-! ### The rest of the item script -/

section Scripts

variable {S : State Ω C} {L : GiantLabels S}

/-- The script after the answer `AK` for `x` and the answer `B₁` for `y ∘ τ₀`. -/
noncomputable def itHvS2 (H : Halving S L) (AK B₁ : Set (Perm Ω)) : Script (Branches Ω) :=
  Script.ask .cont (H.kerState (S.y ∘ (H.τ₀ * H.t))) fun B₂ =>
    Script.done ⟨[H.piece H.τ₀ AK B₁, H.piece (H.τ₀ * H.t) AK B₂], []⟩

/-- The script after the answer `AK` for `x`. -/
noncomputable def itHvS1 (H : Halving S L) (AK : Set (Perm Ω)) : Script (Branches Ω) :=
  Script.ask .cont (H.kerState (S.y ∘ H.τ₀)) fun B₁ => itHvS2 H AK B₁

theorem itHv_script_eq (H : Halving S L) :
    H.script = Script.ask .cont (H.kerState S.x) fun AK => itHvS1 H AK := rfl

end Scripts

/-! ### The bounds -/

/-- A bound on the weight of an answer value, for `k + 1 ≤ 2 W₀ + 4`. -/
def itHvBu (W₀ : ℕ) : ℕ := 1000 * (2 * W₀ + 4) ^ 6

/-- The bound on the weight of a branch state. -/
def itHvRB (Xi : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  100 * (Xi W₀ + itHvBu W₀ + itSVB W₀ + 5 * (2 * W₀ + 3 + 1) ^ 2) + 100

/-- **The bound of Case 2a.** -/
def itHvX (Xi : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  Xi W₀ + itHvB3C (itHvRB Xi W₀) (itHvPcC (itHvRB Xi W₀)) + itHvBC (itHvRB Xi W₀) + itHvRB Xi W₀ + 10

/-- An answer value is light. -/
theorem itHv_ansC_wt {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) {W₀ : ℕ}
    (hk : k + 1 ≤ 2 * W₀ + 4) : u.wt ≤ itHvBu W₀ := by
  have h6 : (k + 1) ^ 6 ≤ (2 * W₀ + 4) ^ 6 := Nat.pow_le_pow_left hk 6
  have h2 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hl, -⟩
  · rw [wt_list_nil]; unfold itHvBu
    have : 1 ≤ (2 * W₀ + 4) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  · have w1 := wt_encPerm_le x
    have w2 := wt_encGroup_le_sq hl
    have w3 := wt_list2_le (encPerm x) (encGroup gs)
    have : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    unfold itHvBu
    omega

/-- The answer for `x` under a subgroup is not empty: it holds `1`. -/
theorem itHv_ansC_x {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S} (H : Halving S L)
    {u : Val} (h : AnsC e u (H.kerState S.x).answer) :
    ∃ (x₀ : Perm (Fin k)) (gs₀ : List (Perm (Fin k))), u = .list [encPerm x₀, encGroup gs₀] ∧
      toFin e '' (H.kerState S.x).answer = x₀ • (gens gs₀ : Set (Perm (Fin k))) := by
  rcases h with ⟨-, h0⟩ | ⟨x, gs, rfl, -, hA⟩
  · have h1 : (1 : Perm Ω) ∈ (H.kerState S.x).answer := by
      rw [Halving.kerState_answer, mem_answer]
      exact ⟨H.ker.one_mem, fun v _ => by simp⟩
    rw [h0] at h1
    exact absurd h1 (Set.notMem_empty _)
  · exact ⟨x, gs, rfl, hA⟩

/-! ### The relations -/

/-- **The kept value stands for the rounds `D`.** -/
def itHvKc (Xi : ℕ → ℕ) {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (w : Val)
    (D : Set (Aggregation P₀ S L.toGiantLabels)) : Prop :=
  w.wt ≤ Xi (I.inW .giant S) ∧ D.Nonempty ∧ D ⊆ itSBase K ∧
    ((¬ ItHvCond K ∧ w = .list [.nat 0] ∧ D = itSBase K) ∨
      (ItHvCond K ∧ ∃ τ₀ t, ItHvKept e c K w τ₀ t ∧ D = itHvD K τ₀ t))

/-- **The branch state after some answers**, for the kept value `w` of `(τ₀, t)`. -/
def itHvLate {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) {S : State Ω C} {L : SuppliedLabels S}
    (K : ItSCtx k S L) (w : Val) (τ₀ t : Perm Ω) (bst : Val)
    (sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)) (f : ℕ) : Prop :=
  (∃ u0, bst = .list [.list [.nat 1, w], u0] ∧
      AnsC e u0 ((itHvH K τ₀ t).kerState S.x).answer ∧
      sb = (fun _ => itHvS1 (itHvH K τ₀ t) ((itHvH K τ₀ t).kerState S.x).answer) ∧ 2 ≤ f) ∨
  (∃ u0 u1, bst = .list [.list [.nat 2, w, u0], u1] ∧
      AnsC e u0 ((itHvH K τ₀ t).kerState S.x).answer ∧
      AnsC e u1 ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)).answer ∧
      sb = (fun _ => itHvS2 (itHvH K τ₀ t) ((itHvH K τ₀ t).kerState S.x).answer
        ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)).answer) ∧ 1 ≤ f) ∨
  (∃ u0 u1 u2, bst = .list [.list [.nat 3, w, u0, u1], u2] ∧
      AnsC e u0 ((itHvH K τ₀ t).kerState S.x).answer ∧
      AnsC e u1 ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)).answer ∧
      AnsC e u2 ((itHvH K τ₀ t).kerState (S.y ∘ (τ₀ * t))).answer ∧
      sb = (fun _ => Script.done ⟨[(itHvH K τ₀ t).piece τ₀ ((itHvH K τ₀ t).kerState S.x).answer
        ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)).answer, (itHvH K τ₀ t).piece (τ₀ * t)
          ((itHvH K τ₀ t).kerState S.x).answer
          ((itHvH K τ₀ t).kerState (S.y ∘ (τ₀ * t))).answer], []⟩))

/-- **The relations of Case 2a.** -/
def itHvRel (Xi : ℕ → ℕ) : ItSCaseRel where
  Kc e c S L K w D := itHvKc I Xi e c S L K w D
  Rb e c S L K b bst D sb f := bst.wt ≤ itHvRB Xi (I.inW .giant S) ∧
    ((∃ w, bst = .list [K.v, stTv b, w] ∧ itHvKc I Xi e c S L K w D ∧
        sb = (fun Ag => (Ag.items b).script) ∧ 3 ≤ f) ∨
      (∃ w τ₀ t, itHvKc I Xi e c S L K w D ∧ ItHvCond K ∧ ItHvKept e c K w τ₀ t ∧
        D = itHvD K τ₀ t ∧ itHvLate e K w τ₀ t bst sb f))

/-! ### The pieces -/

section Pieces

variable {P : Program} {f cmp app : ℕ} (hf : P.funs[f]? = some (itHvPcF cmp app))
  (hcmp : P.HasAt cmp (composeFuns cmp)) (happ : P.HasAt app (appendFuns app))
include hf hcmp happ

/-- **One piece of the halving item as a program.** For the answers `u₀` (for `x`) and `u`
(for the twisted target `z = y ∘ ρ`), the program returns a value of a piece whose set is the image
of `H.piece ρ AK B` (`it_hv_piece_some`, `it_hv_piece_none`). -/
theorem it_hv_piece_prog {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S} (H : Halving S L)
    (hA : H.A ≤ H.even) (hAx : ∀ a ∈ H.A, ∀ v ∈ S.dom, S.x (a v) = S.x v) (ρ : Perm Ω)
    (z : Ω → C) {x₀ : Perm (Fin k)} {gs₀ gA : List (Perm (Fin k))}
    (h₀ : toFin e '' (H.kerState S.x).answer = x₀ • (gens gs₀ : Set (Perm (Fin k))))
    (hgA : gens gA = groupFin e H.A) {u : Val} (hu : AnsC e u (H.kerState z).answer) {W : ℕ}
    (hW : (Val.list [encPerm (toFin e ρ), .list [encPerm x₀, encGroup gs₀], u,
      .list (gA.map encPerm)]).wt ≤ W) :
    ∃ p : Perm (Fin k) × Acc k,
      ceSet p = toFin e '' H.piece ρ (H.kerState S.x).answer (H.kerState z).answer ∧
      FunDet P f (.list [encPerm (toFin e ρ), .list [encPerm x₀, encGroup gs₀], u,
        .list (gA.map encPerm)]) (encPiece p) (itHvPcC W) := by
  rcases hu with ⟨rfl, hB⟩ | ⟨x₁, gs₁, rfl, -, hB⟩
  · obtain ⟨p, hp, hd⟩ := it_hvPc_spec hf hcmp happ (toFin e ρ) x₀ gs₀ gA (.list []) (Or.inl rfl) hW
    rcases hp with ⟨-, rfl⟩ | ⟨x₁, gs₁, h, -⟩
    · exact ⟨_, it_hv_piece_none (e := e) H ρ z hB, hd⟩
    · simp at h
  · obtain ⟨p, hp, hd⟩ := it_hvPc_spec hf hcmp happ (toFin e ρ) x₀ gs₀ gA _
      (Or.inr ⟨x₁, gs₁, rfl⟩) hW
    rcases hp with ⟨h, -⟩ | ⟨x₁', gs₁', h, rfl⟩
    · simp at h
    · simp only [Val.list.injEq, List.cons.injEq, and_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain rfl := encPerm_injective h1
      exact ⟨_, it_hv_piece_some (e := e) (H := H) hA hAx ρ z h₀ hB hgA, hd⟩

end Pieces

/-! ### The contract -/

/-- **The three call values of the kept value are canonical** (`it_hv_canon`). -/
theorem itHv_kept_canon {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {K : ItSCtx k S L} (hK : K.OK e c) {w : Val} {τ₀ t : Perm Ω} (hk : ItHvKept e c K w τ₀ t) :
    ∃ (a0 a1 a2 : Val) (gA : List (Perm (Fin k))),
      w = .list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)),
        .list (gA.map encPerm)] ∧
      Canon e c a0 ((itHvH K τ₀ t).kerState S.x) ∧
      Canon e c a1 ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)) ∧
      Canon e c a2 ((itHvH K τ₀ t).kerState (S.y ∘ (τ₀ * t))) ∧
      gens gA = groupFin e (itHvH K τ₀ t).A := by
  obtain ⟨gv, kgv, dv, xv, yv, hv, rv, fv, hh, yv0, yv1, N, gA, hsv, hkg, hxv, hy0, hy1, hgA, rfl⟩ :=
    hk.val
  have hS : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S := hsv ▸ hK.can
  have hkg' : GroupValC k kgv (groupFin e (itHvH K τ₀ t).ker) := hkg
  refine ⟨_, _, _, gA, rfl, it_hv_canon hS _ hkg' hxv fun a => (hK.can.colors a).1,
    it_hv_canon hS _ hkg' hy0 fun a => (hK.can.colors (τ₀ a)).2,
    it_hv_canon hS _ hkg' hy1 fun a => (hK.can.colors ((τ₀ * t) a)).2, hgA⟩

set_option maxHeartbeats 4000000 in
/-- **Case 2a meets its contract** `ItSCaseOK` for the case `.twoA`, with an init program at
`f0` that meets `ItHvInitOK`, the branch step `itHvBF` at `fb` and the piece program `itHvPcF`,
and the bound `itHvX Xi`. -/
theorem itS_c2a_caseOK {F : Funs} {f0 fb pc cmp app : ℕ} {Xi : ℕ → ℕ}
    (hinit : ItHvInitOK I Pg F f0 Xi) (hfb : Pg.funs[fb]? = some (itHvBF pc))
    (hpc : Pg.funs[pc]? = some (itHvPcF cmp app)) (hcmp : Pg.HasAt cmp (composeFuns cmp))
    (happ : Pg.HasAt app (appendFuns app)) :
    ItSCaseOK I Pg F (· = .twoA) f0 fb (itHvX Xi) := by
  refine ⟨itHvRel I Xi, fun {Ω C k} e c S sv lv L hc K hK hcs => ?_⟩
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  have hk4 : k + 1 ≤ 2 * I.inW .giant S + 4 := by omega
  have hR : itHvRB Xi (I.inW .giant S) = 100 * (Xi (I.inW .giant S) + itHvBu (I.inW .giant S) +
      itSVB (I.inW .giant S) + 5 * (2 * I.inW .giant S + 3 + 1) ^ 2) + 100 := rfl
  have hRX : itHvRB Xi (I.inW .giant S) + 10 ≤ itHvX Xi (I.inW .giant S) := by
    unfold itHvX; omega
  have hXiX : Xi (I.inW .giant S) ≤ itHvX Xi (I.inW .giant S) := by unfold itHvX; omega
  have hBC : itHvBC (itHvRB Xi (I.inW .giant S)) ≤ itHvX Xi (I.inW .giant S) := by
    unfold itHvX; omega
  have hB3 : itHvB3C (itHvRB Xi (I.inW .giant S)) (itHvPcC (itHvRB Xi (I.inW .giant S))) ≤
      itHvX Xi (I.inW .giant S) := by unfold itHvX; omega
  have hBCm : ∀ x, x ≤ itHvRB Xi (I.inW .giant S) → itHvBC x ≤ itHvX Xi (I.inW .giant S) :=
    fun x hx => le_trans (by unfold itHvBC; omega) hBC
  have hu : ∀ {u : Val} {A : Set (Perm Ω)}, AnsC e u A → u.wt ≤ itHvBu (I.inW .giant S) :=
    fun h => itHv_ansC_wt h hk4
  refine ⟨?_, fun w D h => h.2.1, fun w D h => h.1.trans hXiX, fun b w D h => ?_,
    fun b bst D sb f h => h.1.trans (by omega), fun b bst D sb f h => ?_⟩
  · -- init
    refine (hinit e c S sv lv L hc K hK hcs).mono fun w cost ⟨hcost, hw, hcase⟩ => ?_
    rcases hcase with ⟨hn, rfl⟩ | ⟨hy, τ₀, t, hkept⟩
    · exact ⟨itSBase K, subset_rfl, ⟨hw, itSBase_nonempty hK, subset_rfl, Or.inl ⟨hn, rfl, rfl⟩⟩,
        hcost.trans hXiX⟩
    · exact ⟨itHvD K τ₀ t, itHvD_sub K τ₀ t, ⟨hw, itHvD_nonempty hK (fun _ _ => hkept.al)
        (fun _ => hkept.tw), itHvD_sub K τ₀ t, Or.inr ⟨hy, τ₀, t, hkept, rfl⟩⟩, hcost.trans hXiX⟩
  · -- start
    have h3 := wt_list3_le K.v (stTv b) w
    have htb := wt_stTv_le b (M := 2 * I.inW .giant S + 3) (by omega) (by omega)
    have hw := h.1
    exact ⟨by omega, Or.inl ⟨w, rfl, h, rfl, by omega⟩⟩
  -- the step
  obtain ⟨hbw, ⟨w, rfl, hKc, rfl, hf⟩ | ⟨w, τ₀, t, hKc, hy, hkept, rfl, hlate⟩⟩ := h
  · obtain ⟨hw, hDn, hDs, ⟨hn, rfl, rfl⟩ | ⟨hy, τ₀, t, hkept, rfl⟩⟩ := hKc
    · -- stage 0, the empty item
      refine FunAll.mono (it_hvB_s0n hfb K.v (stTv b)) fun w' cost ⟨hw', hc'⟩ => ⟨hc'.trans (hBCm _ hbw),
        Or.inl ⟨⟨[], []⟩, [], [], .list [.nat 0], itSBase K, hw', subset_rfl,
          fun Ag hAg => it_hv_items_none hK hAg hcs b hn,
          ⟨hw, itSBase_nonempty hK, subset_rfl, Or.inl ⟨hn, rfl, rfl⟩⟩,
          ⟨List.Forall₂.nil, rfl, fun i h => absurd h (by simp), fun o ho => absurd ho (by simp)⟩,
          ?_⟩⟩
      have h2 := wt_list2_le (.list []) (.list [])
      rw [wt_list_nil] at h2
      show (Val.list [.list [], .list []]).wt ≤ _
      omega
    · -- stage 0, the first call
      obtain ⟨a0, a1, a2, gA, rfl, hc0, hc1, hc2, hgA⟩ := itHv_kept_canon hK hkept
      obtain ⟨Ag₁, hAg₁⟩ := hDn
      haveI : Finite Ω := Ag₁.fin
      have hv := it_hv_valid hK hAg₁ hcs hy
      obtain ⟨hg0, hm0⟩ := it_hv_call hc.good _ hv S.x
      refine FunAll.mono (it_hvB_s0 hfb K.v (stTv b) (ws := [.nat 1, a0, a1, a2,
        encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) rfl rfl)
        fun w' cost ⟨hw', hc'⟩ =>
        ⟨hc'.trans (hBCm _ hbw), Or.inr ⟨by omega, .cont, Ω, C, _, k, e, c, a0, _,
          itHvD K τ₀ t, fun _ AK => itHvS1 (itHvH K τ₀ t) AK, subset_rfl, ⟨Ag₁, hAg₁⟩, hc.inj,
          Or.inr rfl, hw', hc0, hg0, hm0, fun Ag hAg => ?_, fun u hu' => ?_⟩⟩
      · show (Ag.items b).script = _
        rw [it_hv_items_some hK hAg hcs b hy]
        rfl
      · refine ⟨?_, Or.inr ⟨_, τ₀, t, ⟨hw, ⟨Ag₁, hAg₁⟩, hDs, Or.inr ⟨hy, τ₀, t, hkept, rfl⟩⟩, hy,
          hkept, rfl, Or.inl ⟨u, rfl, hu', rfl, by omega⟩⟩⟩
        have := hu hu'
        have := wt_list2_le (.list [.nat 1, .list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
          encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]]) u
        have := wt_list2_le (.nat 1) (.list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
          encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)])
        have := wt_nat_le 1
        omega
  · -- the later stages
    have hw := hKc.1
    have hDn := hKc.2.1
    obtain ⟨Ag₁, hAg₁⟩ := hDn
    haveI : Finite Ω := Ag₁.fin
    have hv := it_hv_valid hK hAg₁ hcs hy
    obtain ⟨a0, a1, a2, gA, rfl, hc0, hc1, hc2, hgA⟩ := itHv_kept_canon hK hkept
    have hwl := wt_nat_le 1
    have hw2 := wt_nat_le 2
    have hw3 := wt_nat_le 3
    rcases hlate with ⟨u0, rfl, hu0, rfl, hf⟩ | ⟨u0, u1, rfl, hu0, hu1, rfl, hf⟩ |
      ⟨u0, u1, u2, rfl, hu0, hu1, hu2, rfl⟩
    · -- stage 1: the call on `y ∘ τ₀`
      obtain ⟨hg1, hm1⟩ := it_hv_call hc.good _ hv (S.y ∘ τ₀)
      refine FunAll.mono (it_hvB_s1 hfb (ws := [.nat 1, a0, a1, a2,
        encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) rfl u0)
        fun w' cost ⟨hw', hc'⟩ =>
        ⟨hc'.trans (hBCm _ hbw), Or.inr ⟨by omega, .cont, Ω, C, _, k, e, c, a1, _,
          itHvD K τ₀ t, fun _ B₁ => itHvS2 (itHvH K τ₀ t) ((itHvH K τ₀ t).kerState S.x).answer B₁,
          subset_rfl, ⟨Ag₁, hAg₁⟩, hc.inj, Or.inr rfl, hw', hc1, hg1, hm1, fun Ag hAg => rfl,
          fun u hu' => ?_⟩⟩
      refine ⟨?_, Or.inr ⟨_, τ₀, t, hKc, hy, hkept, rfl, Or.inr (Or.inl ⟨u0, u, rfl, hu0, hu', rfl,
        by omega⟩)⟩⟩
      have := hu hu'
      have := hu hu0
      have := wt_list2_le (.list [.nat 2, .list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
        encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)], u0]) u
      have := wt_list3_le (.nat 2) (.list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
        encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) u0
      omega
    · -- stage 2: the call on `y ∘ τ₀ t`
      obtain ⟨hg2, hm2⟩ := it_hv_call hc.good _ hv (S.y ∘ (τ₀ * t))
      refine FunAll.mono (it_hvB_s2 hfb (ws := [.nat 1, a0, a1, a2,
        encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) rfl u0 u1)
        fun w' cost ⟨hw', hc'⟩ =>
        ⟨hc'.trans (hBCm _ hbw), Or.inr ⟨by omega, .cont, Ω, C, _, k, e, c, a2, _,
          itHvD K τ₀ t, fun _ B₂ => Script.done ⟨[(itHvH K τ₀ t).piece τ₀
            ((itHvH K τ₀ t).kerState S.x).answer ((itHvH K τ₀ t).kerState (S.y ∘ τ₀)).answer,
            (itHvH K τ₀ t).piece (τ₀ * t) ((itHvH K τ₀ t).kerState S.x).answer B₂], []⟩,
          subset_rfl, ⟨Ag₁, hAg₁⟩, hc.inj, Or.inr rfl, hw', hc2, hg2, hm2, fun Ag hAg => rfl,
          fun u hu' => ?_⟩⟩
      refine ⟨?_, Or.inr ⟨_, τ₀, t, hKc, hy, hkept, rfl, Or.inr (Or.inr ⟨u0, u1, u, rfl, hu0, hu1,
        hu', rfl⟩)⟩⟩
      have := hu hu'
      have := hu hu0
      have := hu hu1
      have := wt_list2_le (.list [.nat 3, .list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
        encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)], u0, u1]) u
      have := wt_list4_le (.nat 3) (.list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
        encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) u0 u1
      omega
    · -- stage 3: the pieces
      obtain ⟨x₀, gs₀, rfl, hx0⟩ := itHv_ansC_x _ hu0
      have wu0 := hu hu0
      have wu1 := hu hu1
      have wu2 := hu hu2
      have wr0 : (encPerm (toFin e τ₀)).wt < (Val.list [.nat 1, a0, a1, a2, encPerm (toFin e τ₀),
          encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]).wt := itHv_wt_mem (j := 4) rfl
      have wr1 : (encPerm (toFin e (τ₀ * t))).wt < (Val.list [.nat 1, a0, a1, a2,
          encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]).wt :=
        itHv_wt_mem (j := 5) rfl
      have wg : (Val.list (gA.map encPerm)).wt < (Val.list [.nat 1, a0, a1, a2,
          encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]).wt :=
        itHv_wt_mem (j := 6) rfl
      have wi1 := wt_list4_le (encPerm (toFin e τ₀)) (.list [encPerm x₀, encGroup gs₀]) u1
        (.list (gA.map encPerm))
      have wi2 := wt_list4_le (encPerm (toFin e (τ₀ * t))) (.list [encPerm x₀, encGroup gs₀]) u2
        (.list (gA.map encPerm))
      obtain ⟨p1, hP1, hp1⟩ := it_hv_piece_prog hpc hcmp happ (itHvH K τ₀ t) hv.A_le hv.A_aut τ₀
        (S.y ∘ τ₀) hx0 hgA hu1 (W := itHvRB Xi (I.inW .giant S)) (by omega)
      obtain ⟨p2, hP2, hp2⟩ := it_hv_piece_prog hpc hcmp happ (itHvH K τ₀ t) hv.A_le hv.A_aut
        (τ₀ * t) (S.y ∘ (τ₀ * t)) hx0 hgA hu2 (W := itHvRB Xi (I.inW .giant S)) (by omega)
      have wp1 := FunDet.wt_lt hp1
      have wp2 := FunDet.wt_lt hp2
      refine FunAll.mono (it_hvB_s3 hfb (ws := [.nat 1, a0, a1, a2,
        encPerm (toFin e τ₀), encPerm (toFin e (τ₀ * t)), .list (gA.map encPerm)]) rfl rfl rfl
        (.list [encPerm x₀, encGroup gs₀]) u1 u2 hp1 hp2)
        fun w' cost ⟨hw', hc'⟩ => ⟨?_, Or.inl ⟨_, [p1, p2], [], _, itHvD K τ₀ t, hw', subset_rfl,
          fun Ag _ => rfl, hKc, ⟨List.Forall₂.nil, rfl, fun i h1 _ => ?_,
            fun o ho => absurd ho (by simp)⟩, ?_⟩⟩
      · refine hc'.trans (le_trans ?_ hB3)
        unfold itHvB3C
        omega
      · rcases i with _ | _ | i
        · exact hP1
        · exact hP2
        · exact absurd h1 (by simp)
      · have h2 := wt_list2_le (.list [encPiece p1, encPiece p2]) (.list [])
        have h3 := wt_list2_le (encPiece p1) (encPiece p2)
        rw [wt_list_nil] at h2
        show (Val.list [.list [encPiece p1, encPiece p2], .list []]).wt ≤ _
        refine le_trans ?_ hB3
        unfold itHvB3C
        omega

end GI.Impl
