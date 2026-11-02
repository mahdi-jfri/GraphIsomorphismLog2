import Workspace.Impl.TermGlueLabPGenM

/-!
# The items of all generators (step 5, the `map`)

Step 5 of the label program (proof of Theorem A.23). The affine procedure takes
one item per generator of the supplement `S = ⟨gs⟩` (`tmGLAffIn`). The program runs the
per-generator program (`tmGLPGen_spec`) on every generator with `map`.

* `tmGLPItems_spec`: `map gen` on `[ctx, [enc g for g in gs]]` returns a list related to `gs`
  entrywise, for any per-entry specification with a monotone bound `G` (`tmGLPItemsC G`).
* `tmGLP_items_eq`: a list related entrywise to `gs` by "is the item of `g`" is the list of
  items in `tmGLAffIn` (over `gs.attach`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm gens)

/-- The cost bound of the `map` over the generators, for a per-item bound `G`. -/
def tmGLPItemsC (G : ℕ → ℕ) (W : ℕ) : ℕ := 4000 * (W + 1) ^ 2 * (G (4 * W + 6) + 2)

theorem tmGLPItemsC_mono {G : ℕ → ℕ} (hG : Monotone G) {W W' : ℕ} (h : W ≤ W') :
    tmGLPItemsC G W ≤ tmGLPItemsC G W' := by
  unfold tmGLPItemsC
  have := hG (show 4 * W + 6 ≤ 4 * W' + 6 by omega)
  gcongr

private theorem tmGLP_items_ar {c S w l W G : ℕ} (hl : l ≤ W) (hS : S ≤ l * G)
    (hw : w ≤ l * (2 * G + 1) + 4) (hc : c ≤ S + 1000 * (l + 1) * (W + w + 1)) :
    c ≤ 4000 * (W + 1) ^ 2 * (G + 2) := by
  have h1 : l * G ≤ (W + 1) * G := Nat.mul_le_mul_right _ (by omega)
  have h2 : l * (2 * G + 1) ≤ (W + 1) * (2 * G + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : W + w + 1 ≤ (W + 1) * (2 * G + 1) + W + 5 := by omega
  have h4 : (W + 1) * (2 * G + 1) + W + 5 ≤ (W + 1) * (3 * G + 6) := by
    have : (W + 1) * (3 * G + 6) = (W + 1) * (2 * G + 1) + (W + 1) * (G + 5) := by ring
    have : W + 5 ≤ (W + 1) * (G + 5) := by nlinarith
    omega
  have h5 : 1000 * (l + 1) * (W + w + 1) ≤ 1000 * (W + 1) * ((W + 1) * (3 * G + 6)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (h3.trans h4)
  have h6 : 1000 * (W + 1) * ((W + 1) * (3 * G + 6)) = 3000 * ((W + 1) ^ 2 * (G + 2)) := by ring
  have h8 : (W + 1) * G ≤ (W + 1) ^ 2 * (G + 2) := by
    rw [sq, mul_assoc]; exact Nat.mul_le_mul_left _ (by nlinarith)
  rw [show 4000 * (W + 1) ^ 2 * (G + 2) = 4000 * ((W + 1) ^ 2 * (G + 2)) by ring]
  generalize (W + 1) ^ 2 * (G + 2) = Q at h6 h8 ⊢
  omega

/-- **The items of all generators.** If the per-item program `gen` on `[ctx, enc g]` gives a
value related to `g` by `R` at cost at most `G` of its input weight, for every `g ∈ gs`, then
`map gen` on `[ctx, [enc g for g in gs]]` gives a list related to `gs` entrywise by `R`. -/
theorem tmGLPItems_spec {P : Program} {b gen : ℕ} (h : P.HasAt b (mapFuns b gen)) {cx : Val}
    {α : Type*} {enc : α → Val} (henc : Function.Injective enc) (gs : List α)
    {R : α → Val → Prop} {G : ℕ → ℕ} (hG : Monotone G)
    (hgen : ∀ g ∈ gs, FunAll P gen (.list [cx, enc g])
      (fun w c => R g w ∧ c ≤ G (Val.list [cx, enc g]).wt)) :
    FunAll P b (.list [cx, .list (gs.map enc)]) (fun w c => ∃ ws, w = .list ws ∧
      List.Forall₂ R gs ws ∧ c ≤ tmGLPItemsC G (Val.list [cx, .list (gs.map enc)]).wt) := by
  set W := (Val.list [cx, .list (gs.map enc)]).wt with hW
  have wcx : cx.wt < W := wt_le_wt_list (by simp)
  have wl : (Val.list (gs.map enc)).wt < W := wt_le_wt_list (by simp)
  have hlen : (gs.map enc).length < W := (length_lt_wt_list _).trans wl
  set Gm := G (4 * W + 6) with hGm
  have hB : ∀ x ∈ gs.map enc, FunAll P gen (.list [cx, x]) (fun w c =>
      (w.wt ≤ Gm ∧ ∀ g, enc g = x → R g w) ∧ c ≤ Gm) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    have hxw : (enc g).wt < W := (wt_le_wt_list hx).trans wl
    have hle : G (Val.list [cx, enc g]).wt ≤ Gm :=
      hG (by have := wt_list2_le cx (enc g); omega)
    refine FunAll.mono (FunAll.wt_lt (hgen g hg)) fun w c ⟨⟨hR, hc⟩, hwc⟩ => ?_
    refine ⟨⟨by omega, fun g' he => ?_⟩, hc.trans hle⟩
    rw [henc he]; exact hR
  refine FunAll.mono (map_spec h hB (B := fun _ => Gm)) fun w c ⟨ws, hw, hws, hc⟩ => ?_
  obtain ⟨hl, hget⟩ := List.forall₂_iff_get.mp hws
  have hwl : ∀ v ∈ ws, v.wt ≤ Gm := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact (hget i (hl ▸ hi) hi).1
  refine ⟨ws, hw, ?_, ?_⟩
  · rw [List.forall₂_map_left_iff] at hws
    exact hws.imp fun {g w} h => h.2 g rfl
  · subst hw
    have hws' := wt_list_le_of hwl
    rw [List.map_const', List.sum_replicate, smul_eq_mul] at hc
    exact tmGLP_items_ar (G := Gm) (l := (gs.map enc).length) hlen.le le_rfl
      (hl ▸ hws') hc

/-- **The list of items.** If every entry of `ws` is the item of the matching generator, then
`ws` is the item list of `tmGLAffIn`. -/
theorem tmGLP_items_eq {n : ℕ} {gs : List (Perm (Fin n))} {R : Perm (Fin n) → Val → Prop}
    {F : gens gs → Val} (hF : ∀ g (hg : g ∈ gs) w, R g w → w = F ⟨g, Subgroup.subset_closure hg⟩)
    {ws : List Val} (hws : List.Forall₂ R gs ws) :
    ws = gs.attach.map fun g => F ⟨g.1, Subgroup.subset_closure g.2⟩ := by
  obtain ⟨hl, hget⟩ := List.forall₂_iff_get.mp hws
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < gs.length := hl ▸ h1
  rw [List.getElem_map, List.getElem_attach]
  exact hF _ (List.getElem_mem hi) _ (hget i hi h1)

end GI.Impl
