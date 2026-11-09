module

public import Workspace.Degree.GraphDeg
public import Workspace.Assembly.Convert

/-!
# The output cells

On an isomorphism `σ` and a list `L` of automorphisms, the cells `1, σ, |L|, L` of a positive
answer (`yesCells`).
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv

variable {n : ℕ}

/-- The output, on `[σ, L]`. -/
def outE (app cat : ℕ) : Expr :=
  .call cat (mk3 .nil (arg 1) (.snoc (.call app (mk2 (mk1 (.nat 1)) (arg 0))) (.length (arg 1))))

/-- The functions of the output. -/
def outFuns (o : ℕ) : List Expr := [outE (o + 1) (o + 4)] ++ appendFuns (o + 1) ++ catFuns (o + 4) (o + 1)

/-- A bound on the length of the list of generators. -/
def GLn (n : ℕ) : ℕ := n ^ 2 * (n ^ 2 + 2)

/-- A bound on the weight of the output. -/
def OW (n : ℕ) : ℕ := (n + 2 + n * GLn n) * (2 * (n + GLn n + 1) + 5) + 4

/-- The budget of the output. -/
def outT (n : ℕ) : ℕ :=
  GLn n * (4000 * (n + 1) * (2 * AL n + 3 * OW n + 30)) +
    loopModK * (GLn n + 1) * (10 * AL n + 10 * OW n + GLn n + 100) +
    loopModK * (n + 1) * (20 * WB n + 10 * OW n + n + 10) + 100 * AL n + 100 * OW n + 1000 * WB n

theorem permCells_val (σ : Perm (Fin n)) : encPerm σ = .list ((permCells σ).map .nat) := by
  rw [encPerm_eq_encFun, encFun_eq_ofFn]
  rfl

theorem yesCells_wt (σ : Perm (Fin n)) (L : List (Perm (Fin n))) (hL : L.length ≤ GLn n) :
    (Val.list ((yesCells σ L).map .nat)).wt ≤ OW n := by
  have hlen : (yesCells σ L).length = n + 2 + n * L.length := by
    simp [yesCells, length_permCells, length_permsCells]
    omega
  have hle : ∀ x ∈ yesCells σ L, x ≤ n + GLn n + 1 := by
    intro x hx
    simp only [yesCells, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | rfl | hx
    · omega
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := (σ i).isLt
      omega
    · omega
    · obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := (g i).isLt
      omega
  have h1 := wt_natList_le _ hle
  rw [hlen] at h1
  have h2 : n * L.length ≤ n * GLn n := Nat.mul_le_mul_left _ hL
  have h3 := Nat.mul_le_mul_right (2 * (n + GLn n + 1) + 5) (show n + 2 + n * L.length ≤
    n + 2 + n * GLn n by omega)
  simp only [OW]
  omega

set_option maxHeartbeats 4000000 in
/-- **The output.** -/
theorem out_spec {P : Program} {o : ℕ} (hP : P.HasAt o (outFuns o)) (σ : Perm (Fin n))
    (L : List (Perm (Fin n))) (hL : L.length ≤ GLn n) :
    FunDet P o (.list [encPerm σ, .list (L.map encPerm)]) (.list ((yesCells σ L).map .nat))
      (1000 * outT n) := by
  have hM : P.funs[o]? = some (outE (o + 1) (o + 4)) := hP.left.left.single
  have hAp : P.HasAt (o + 1) (appendFuns (o + 1)) := hP.left.right
  have hCat : P.HasAt (o + 4) (catFuns (o + 4) (o + 1)) := hP.right
  have h0 := WB_ge n
  have hlk := le_kB n
  have wσ : (encPerm σ).wt ≤ WB n := perm_wt (by omega) σ
  have wL : (Val.list (L.map encPerm)).wt ≤ AL n := permList_AL (by simp only [GLn] at hL; omega)
  have hAL : 4 * WB n + 6 ≤ AL n := by
    have := Nat.mul_le_mul_right (2 * WB n + 1) (show 2 ≤ n ^ 2 * (n ^ 2 + 2) + 2 by omega)
    simp only [AL]
    omega
  set B0 := Val.list [encPerm σ, .list (L.map encPerm)] with hB0
  have wB : B0.wt ≤ 2 * (2 * AL n + 1) + 4 := wt_lit _ (by
    simp only [hB0, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)
  set T := outT n with hT
  have hTB : 2 * B0.wt + 100 ≤ T := by simp only [hT, outT]; omega
  have hTO : 100 * OW n + 100 * AL n + 1000 * WB n ≤ T := by simp only [hT, outT]; omega
  have a0 : Lv P [B0] T (arg 0) (.list ((permCells σ).map .nat)) 1 := by
    refine Lv.arg (vs := [encPerm σ, .list (L.map encPerm)]) ?_ (by change 2 * B0.wt + 0 + 5 ≤ T; omega)
    rw [permCells_val]
    rfl
  have a1 : Lv P [B0] T (arg 1) (.list (L.map encPerm)) 1 :=
    Lv.arg (vs := [encPerm σ, .list (L.map encPerm)]) rfl (by change 2 * B0.wt + 1 + 5 ≤ T; omega)
  have hle : ∀ x ∈ yesCells σ L, x ≤ n + GLn n + 1 := by
    intro x hx
    simp only [yesCells, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | rfl | hx
    · omega
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := (σ i).isLt
      omega
    · omega
    · obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := (g i).isLt
      omega
  have hOW : (n + 2) * (2 * (n + GLn n + 1) + 5) + 4 ≤ OW n := by
    have := Nat.mul_le_mul_right (2 * (n + GLn n + 1) + 5) (show n + 2 ≤ n + 2 + n * GLn n by omega)
    simp only [OW]
    omega
  have wQ : (Val.list ((1 :: permCells σ).map .nat)).wt ≤ OW n := by
    have := wt_natList_le (1 :: permCells σ) (B := n + GLn n + 1) (fun x hx => hle x (by
      simp only [yesCells, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (List.mem_append_left _ hx)))
    simp only [List.length_cons, length_permCells] at this
    have := Nat.mul_le_mul_right (2 * (n + GLn n + 1) + 5) (show n + 1 ≤ n + 2 by omega)
    omega
  set P0 := 1 :: permCells σ ++ [L.length] with hP0
  have wP0 : (Val.list (P0.map .nat)).wt ≤ OW n := by
    have := wt_natList_le P0 (B := n + GLn n + 1) (fun x hx => hle x (by
      simp only [hP0, yesCells, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with (rfl | hx) | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl rfl))))
    have hl : P0.length = n + 2 := by simp [hP0, length_permCells]
    rw [hl] at this
    omega
  have wY := yesCells_wt σ L hL
  have w1 : (Val.list [Val.nat 1]).wt ≤ 3 * WB n := by
    have h1 : (Val.nat 1).wt ≤ WB n := nat_wt (by omega)
    have := wt_lit (c := WB n) [Val.nat 1] (by simp; exact h1)
    simp only [List.length_singleton] at this
    omega
  have wcs : (Val.list ((permCells σ).map Val.nat)).wt ≤ WB n := by rw [← permCells_val]; exact wσ
  have w2 : (Val.list [.list [Val.nat 1], .list ((permCells σ).map Val.nat)]).wt ≤
      2 * (2 * (3 * WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)
  have hApD : FunDet P (o + 1) (.list [.list [Val.nat 1], .list ((permCells σ).map Val.nat)])
      (.list ((1 :: permCells σ).map .nat)) (loopModK * (n + 1) * (20 * WB n + 10 * OW n + n + 10)) := by
    refine FunAll.mono (append_spec hAp [Val.nat 1] ((permCells σ).map Val.nat)) fun x c hx => ⟨?_, ?_⟩
    · rw [hx.1]
      simp
    · have h1 := hx.2
      have e1 : (Val.list ([Val.nat 1] ++ (permCells σ).map Val.nat)) =
          .list ((1 :: permCells σ).map .nat) := by simp
      rw [hx.1, e1] at h1
      simp only [List.length_map, length_permCells] at h1
      have e2 : loopModK * (n + 1) * ((Val.list [.list [Val.nat 1],
          .list ((permCells σ).map Val.nat)]).wt + n + (Val.list ((1 :: permCells σ).map .nat)).wt + 1) ≤
          loopModK * (n + 1) * (20 * WB n + 10 * OW n + n + 10) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have cA := Lv.call (Lv.mk2 (Lv.mk1 (Lv.nat (env := [B0]) (T := T) 1 (by omega)) (by omega)) a0
    (by omega)) hApD (by simp only [hT, outT]; omega)
  have cL := Lv.length a1 (by omega)
  have cS := Lv.snoc cA cL (by omega)
  have eS : ((1 :: permCells σ).map Val.nat ++ [Val.nat (L.map encPerm).length]) = P0.map .nat := by
    simp [hP0]
  rw [eS] at cS
  set Ls := L.map permCells with hLs
  have eL : Val.list (L.map encPerm) = .list (Ls.map fun l => Val.list (l.map .nat)) := by
    simp only [hLs, List.map_map]
    congr 1
    apply List.map_congr_left
    intro g _
    exact permCells_val g
  have a1' : Lv P [B0] T (arg 1) (.list (Ls.map fun l => Val.list (l.map .nat))) 1 := eL ▸ a1
  have hls : ∀ l ∈ Ls, l.length = n := by
    intro l hl
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hl
    exact length_permCells g
  have hcat := cat_spec hCat hAp (.list []) Ls P0 hls
  have eY : (P0 ++ Ls.flatten) = yesCells σ L := by
    simp [hP0, hLs, yesCells, permsCells]
  rw [eY] at hcat
  have wLs : (Val.list (Ls.map fun l => Val.list (l.map .nat))).wt ≤ AL n := eL ▸ wL
  have hLl : Ls.length ≤ GLn n := by simp [hLs]; exact hL
  have w0 : (Val.list []).wt ≤ 5 := by
    have := wt_lit (c := 0) [] (by simp)
    simp only [List.length_nil] at this
    omega
  have w4 : (Val.list [.list [], .list (Ls.map fun l => Val.list (l.map .nat)),
      .list (P0.map .nat)]).wt ≤ 3 * (2 * (AL n + OW n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  have e3 : Ls.length * (4000 * (n + 1) * (2 * (Val.list []).wt +
      2 * (Val.list (Ls.map fun l => Val.list (l.map .nat))).wt +
      3 * (Val.list ((yesCells σ L).map .nat)).wt + 20)) ≤
      GLn n * (4000 * (n + 1) * (2 * AL n + 3 * OW n + 30)) :=
    Nat.mul_le_mul hLl (Nat.mul_le_mul_left _ (by omega))
  have e4 : loopModK * (Ls.length + 1) * ((Val.list [.list [], .list (Ls.map fun l =>
      Val.list (l.map .nat)), .list (P0.map .nat)]).wt + Ls.length +
      (Val.list ((yesCells σ L).map .nat)).wt + 1) ≤
      loopModK * (GLn n + 1) * (10 * AL n + 10 * OW n + GLn n + 100) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hT5 : 5 ≤ T := le_trans (by omega) hTB
  have hTc : GLn n * (4000 * (n + 1) * (2 * AL n + 3 * OW n + 30)) +
      loopModK * (GLn n + 1) * (10 * AL n + 10 * OW n + GLn n + 100) ≤ T := by
    rw [hT]; unfold outT; clear * -; omega
  have cC := Lv.call (Lv.mk3 (Lv.nil hT5) a1' cS hT5) hcat ((Nat.add_le_add e3 e4).trans hTc)
  exact funDet_of_lv hM (Lv.mono (e := outE (o + 1) (o + 4)) cC (by norm_num))

end GI.Degree
