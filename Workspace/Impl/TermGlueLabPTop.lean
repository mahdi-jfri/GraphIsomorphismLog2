import Workspace.Impl.TermGlueLabMain
import Workspace.Impl.TermGlue

/-!
# The label program: the empty case and the dispatch (step 1)

Proof of Theorem A.23, the label step. The input is `[V, r, w]` with `w` a
canonical answer for the residual set `Res = tmGlRes I r` of one radical coset.

1. If `w = []`, the residual set is empty, so the label coset is empty (`tmGL_lab_res_empty`)
   and the program returns `[]`.
2. Otherwise `w = [x₀, U]` and the program calls the nonempty part at index `ne`: steps 2–6
   of the label program (alignment by `k(τ)` with `τ = x₀`, the offsets `t_a(s)`, the
   supplement, the coordinates `E`, one affine transporter call, the output reduction).

`Iface.TmGLPNeSpec` is the contract of the nonempty part: the contract `TermGlueLabSpec` with
the extra hypothesis `w ≠ []`. `tmGLP_top_spec` proves `TermGlueLabSpec` for the dispatch from
it. The nonempty part is a hypothesis here.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-- **The dispatch**: `[]` on an empty residual answer, else the nonempty part `ne`. -/
def tmGLPTopF (ne : ℕ) : Expr := .ite (.length (arg 2)) (.call ne (.var 0)) .nil

namespace Iface

/-- **The nonempty part of the label step**: `TermGlueLabSpec` with `w ≠ []`. -/
def TmGLPNeSpec (Pg : Program) (K D g : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      ∀ (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B),
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
        (hqα : (S.N : ℝ) ^ P₀.α < L.q),
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      ∀ r : Perm (Fin m), r ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb →
      ∀ w : Val, AnsC (Equiv.refl (Fin m)) w
        (tmGlRes ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r) →
      w ≠ .list [] →
      FunAll Pg g (.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w])
        (fun u cost => AnsC (Equiv.refl (Fin m)) u
            (tmGlLab ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r) ∧
          cost ≤ K * ((Val.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
            encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r, w]).wt + 1) ^ D)

end Iface

/-- The weight of a canonical answer that is not `[]` has length 2. -/
private theorem tmGLP_ans_len {m : ℕ} {w : Val} {T : Set (Perm (Fin m))}
    (hw : AnsC (Equiv.refl (Fin m)) w T) :
    (w = .list [] ∧ T = ∅) ∨ ∃ ws : List Val, w = .list ws ∧ ws.length = 2 := by
  rcases hw with h | ⟨x, gs, rfl, -, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, rfl, rfl⟩

/-- **The label program from its nonempty part.** The dispatch `tmGLPTopF ne` at `f` meets
`TermGlueLabSpec` with constants `3 K + 100`, `D + 1` when the nonempty part meets
`TmGLPNeSpec` with `K`, `D`. -/
theorem tmGLP_top_spec {P : Program} {f ne K D : ℕ} (hf : P.funs[f]? = some (tmGLPTopF ne))
    (hne : Iface.TmGLPNeSpec P K D ne) : Iface.TermGlueLabSpec P (3 * K + 100) (D + 1) f := by
  intro Ω C _ S k e c hc sv lv L hcan hlab hq0 hgood hrow label hnat hq m h0 E hP σH σN σS
    hH hN hS htr hlH hlN hlS hcard hsN hN0 hqα us vs hus hvs r hr w hw
  set V : Val := .list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)], .list us, .list vs]
  set a : Val := .list [V, encPerm r, w]
  have hpow : ∀ W : ℕ, 100 * (W + 1) ≤ 100 * (W + 1) ^ (D + 1) := fun W =>
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
  have hpow' : ∀ W : ℕ, K * (W + 1) ^ D ≤ K * (W + 1) ^ (D + 1) := fun W =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have wa : w.wt < a.wt := wt_le_wt_list (by simp)
  apply FunAll.intro hf
  have dw := Det.arg' (P := P) (vs := [V, encPerm r, w]) (rest := []) (j := 2) rfl
  rcases tmGLP_ans_len hw with ⟨rfl, hres⟩ | ⟨ws, rfl, hlen⟩
  · -- the empty case
    have dl := Det.length dw
    have dres := Det.ite_zero (t := .call ne (.var 0)) dl (Det.nil (P := P) (env := [a]))
    refine dres.post fun cost hcost => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · exact tmGL_lab_res_empty _ hres
    · have h1 := hpow a.wt
      have h2 : (Val.list []).wt ≤ 5 := by decide
      simp only [List.length_nil] at hcost
      have := wt_nat_le 0
      have ea : a.wt = (Val.list [V, encPerm r, Val.list []]).wt := rfl
      change cost ≤ (3 * K + 100) * (a.wt + 1) ^ (D + 1)
      have e1 : (3 * K + 100) * (a.wt + 1) ^ (D + 1) =
          3 * (K * (a.wt + 1) ^ (D + 1)) + 100 * (a.wt + 1) ^ (D + 1) := by ring
      omega
  · -- the nonempty part
    have hne' := hne S k e c hc sv lv L hcan hlab hq0 hgood hrow label hnat hq h0 E hP σH σN σS
      hH hN hS htr hlH hlN hlS hcard hsN hN0 hqα us vs hus hvs r hr (.list ws) hw
      (by intro h; injection h with h; subst h; simp at hlen)
    have dl := Det.length dw
    rw [hlen] at dl
    refine EvalAll.ite dl (fun _ _ h => ⟨2, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_neg (by decide)]
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine hne'.wt_lt.mono fun u cost hu => ⟨hu.1.1, ?_⟩
    have hc := hu.1.2
    have hwt := hu.2
    have h1 := hpow a.wt
    have h3 := hpow' a.wt
    have := wt_nat_le 2
    change cost ≤ K * (a.wt + 1) ^ D at hc
    change cc + (ca + cost + u.wt + 1) + u.wt + 1 ≤ (3 * K + 100) * (a.wt + 1) ^ (D + 1)
    have e1 : (3 * K + 100) * (a.wt + 1) ^ (D + 1) =
        3 * (K * (a.wt + 1) ^ (D + 1)) + 100 * (a.wt + 1) ^ (D + 1) := by ring
    have hcc : cc ≤ 2 * a.wt + 2 + 5 + 2 + 3 := by simpa using h2
    have hca' : ca ≤ a.wt + 1 := hca
    clear_value a V
    omega

end GI.Impl
