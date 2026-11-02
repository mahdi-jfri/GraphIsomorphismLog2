import Workspace.Impl.AggItemCiCfgO

/-!
# The configuration query: the overcoset program, its spec

`itcq_ouF_spec`: the program `itcqOuF` on `[σ₀, S, w]` returns
`itciRes (itciOV (itcqOs X σ₀ S)) w` in cost `itcqOuC M`, for `M` at least `q + 1` and the input
weight. The four cases (`σ₀` even or odd, an odd entry of `S` or none) follow `itcqRep` and
`itcqEG` (`itcqOs_odd_some`, `itcqOs_even`, `itcqOs_odd_none`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-! ### The values in the four cases -/

theorem itcqEG_some {S : List (Perm (Fin q))} {t : Perm (Fin q)} (ht : itcqOdd S = some t) :
    itcqEG S = (List.range (2 * S.length)).map (itSchE t S) := by
  unfold itcqEG; rw [ht]

theorem itcqEG_none {S : List (Perm (Fin q))} (ht : itcqOdd S = none) : itcqEG S = S := by
  unfold itcqEG; rw [ht]

theorem itcqOs_odd_some {X : PairCfg q} {σ₀ t : Perm (Fin q)} {S : List (Perm (Fin q))}
    (hp : sign σ₀ ≠ 1) (ht : itcqOdd S = some t) :
    itciOV (itcqOs X σ₀ S) = .list [lcOv (σ₀ * t) (itcqEG S)] := by
  have hs : sign (σ₀ * t) = 1 := by
    rw [Perm.sign_mul, (itp_sign_cases σ₀).resolve_left hp, (itcqOdd_some ht).2]; decide
  have hr : itcqRep σ₀ S = some (σ₀ * t) := by
    unfold itcqRep; rw [if_neg hp, ht]; rfl
  unfold itcqOs
  rw [hr]
  simp only [dif_pos hs]
  rfl

theorem itcqOs_even {X : PairCfg q} {σ₀ : Perm (Fin q)} {S : List (Perm (Fin q))}
    (hp : sign σ₀ = 1) : itciOV (itcqOs X σ₀ S) = .list [lcOv σ₀ (itcqEG S)] := by
  have hr : itcqRep σ₀ S = some σ₀ := by unfold itcqRep; rw [if_pos hp]
  unfold itcqOs
  rw [hr]
  simp only [dif_pos hp]
  rfl

theorem itcqOs_odd_none {X : PairCfg q} {σ₀ : Perm (Fin q)} {S : List (Perm (Fin q))}
    (hp : sign σ₀ ≠ 1) (ht : itcqOdd S = none) : itciOV (itcqOs X σ₀ S) = .list [] := by
  have hr : itcqRep σ₀ S = none := by unfold itcqRep; rw [if_neg hp, ht]; rfl
  unfold itcqOs
  rw [hr]
  rfl

/-- The weight of a result with one overcoset. -/
theorem itcq_res1_wt (σ : Perm (Fin q)) (E : List (Perm (Fin q))) (w : Val) :
    (itciRes (.list [lcOv σ E]) w).wt ≤
      20 * (E.length * (9 * (q + 1) ^ 2)) + 200 * (q + 1) ^ 2 + 4 * w.wt + 400 := by
  have h1 := wt_encPerm_le σ
  have h2 := it_perms_wt (l := E) (m := E.length) le_rfl
  have h3 := wt_list2_le (encPerm σ) (.list (E.map encPerm))
  have h4 := wt_list1_le (lcOv σ E)
  have h5 := wt_list3_le (.list []) (.list [lcOv σ E]) w
  have h6 := wt_list2_le (.nat 0) (.list [.list [], .list [lcOv σ E], w])
  have h7 := wt_nat_le 0
  simp only [wt_list_nil] at h5
  unfold itciRes
  unfold lcOv at h4 h5 h6 ⊢
  omega

section Prog

variable {P : Program}

/-- **A result with one overcoset.** -/
theorem itcq_res1_st {rest : List Val} {a0 a1 w : Val} {eσ eE : Expr} {σ : Perm (Fin q)}
    {E : List (Perm (Fin q))} {n1 n2 E1 E2 W : ℕ}
    (hσ : StDC P (.list [a0, a1, w] :: rest) eσ (encPerm σ) n1 E1 W)
    (hE : StDC P (.list [a0, a1, w] :: rest) eE (.list (E.map encPerm)) n2 E2 W)
    (hv : (Val.list [a0, a1, w]).wt ≤ W) (hr : (itciRes (.list [lcOv σ E]) w).wt ≤ W) :
    StDC P (.list [a0, a1, w] :: rest) (itcqRes1 eσ eE) (itciRes (.list [lcOv σ E]) w)
      (n1 + n2 + 30) (E1 + E2) W := by
  have hw : w.wt < (Val.list [a0, a1, w]).wt := wt_le_wt_list (by simp)
  have h4 : 4 ≤ W := by have := wt_list_eq [a0, a1, w]; omega
  have hin : (Val.list [.list [], .list [lcOv σ E], w]).wt ≤ W := by
    have := wt_le_wt_list (show Val.list [.list [], .list [lcOv σ E], w] ∈
      [Val.nat 0, .list [.list [], .list [lcOv σ E], w]] by simp)
    unfold itciRes at hr; omega
  have hl1 : (Val.list [lcOv σ E]).wt ≤ W := by
    have := wt_le_wt_list (show Val.list [lcOv σ E] ∈ [.list [], .list [lcOv σ E], w] by simp)
    omega
  have hl0 : (lcOv σ E).wt ≤ W := by
    have := wt_le_wt_list (show lcOv σ E ∈ [lcOv σ E] by simp); omega
  have A2 := StDC.arg (P := P) (rest := rest) (vs := [a0, a1, w]) (j := 2) rfl hv (by omega)
    (by omega)
  have m := StDC.mk2 hσ hE hl0 h4
  have s := StDC.snoc (StDC.nil (env := .list [a0, a1, w] :: rest) (P := P) h4) m
    (vs := []) (by simpa using hl1)
  have r := StDC.mk2 (StDC.nat 0 (by omega)) (StDC.mk3 (StDC.nil h4) s A2 hin h4) hr h4
  unfold itcqRes1
  exact r.mono (by omega) (by omega)

/-- **The result with no overcoset.** -/
theorem itcq_res0_st {rest : List Val} {a0 a1 w : Val} {W : ℕ}
    (hv : (Val.list [a0, a1, w]).wt ≤ W) (hr : (itciRes (.list []) w).wt ≤ W) :
    StDC P (.list [a0, a1, w] :: rest) itcqRes0 (itciRes (.list []) w) 20 0 W := by
  have hw : w.wt < (Val.list [a0, a1, w]).wt := wt_le_wt_list (by simp)
  have h4 : 4 ≤ W := by have := wt_list_eq [a0, a1, w]; omega
  have hin : (Val.list [.list [], .list [], w]).wt ≤ W := by
    have := wt_le_wt_list (show Val.list [.list [], .list [], w] ∈
      [Val.nat 0, .list [.list [], .list [], w]] by simp)
    unfold itciRes at hr; omega
  have A2 := StDC.arg (P := P) (rest := rest) (vs := [a0, a1, w]) (j := 2) rfl hv (by omega)
    (by omega)
  have r := StDC.mk2 (StDC.nat 0 (by omega)) (StDC.mk3 (StDC.nil h4) (StDC.nil h4) A2 hin h4) hr h4
  unfold itcqRes0
  exact r.mono (by omega) (by omega)

end Prog

end GI.Impl
