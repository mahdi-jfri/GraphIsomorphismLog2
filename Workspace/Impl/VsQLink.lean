import Workspace.Lang.Lib.Basic

/-!
# Sparse programs

A program from a list of blocks: block `k` starts at `B k` (`B` larger than every block), and the
places between blocks hold `.nil`. A block is found by division with remainder, so the facts
`P.HasAt (B k) block` and `P.funs[B k + j]? = some e` follow from the list of blocks alone
(`spProg_hasAt`, `spProg_funs`).
-/

namespace GI.Impl

open GI.Lang

/-- The sparse program with blocks `blks`, spacing `B`, and primitives `ps`. -/
def spProg (B : ℕ) (blks : List (List Expr)) (ps : List Prim) : Program :=
  ⟨(List.range (B * blks.length)).map fun i => (blks.getD (i / B) []).getD (i % B) .nil, ps⟩

theorem spProg_funs {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {k j : ℕ}
    (hk : k < blks.length) (hj : j < B) :
    (spProg B blks ps).funs[B * k + j]? = some ((blks.getD k []).getD j .nil) := by
  have hB : 0 < B := by omega
  have hlt : B * k + j < B * blks.length := by
    have : B * k + j < B * (k + 1) := by rw [Nat.mul_succ]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ hk)
  simp only [spProg, List.getElem?_map, List.getElem?_range hlt, Option.map_some]
  congr 2
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem spProg_hasAt {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {k : ℕ} {fs : List Expr}
    (hk : k < blks.length) (hblk : blks.getD k [] = fs) (hl : fs.length ≤ B) :
    (spProg B blks ps).HasAt (B * k) fs := by
  intro j hj
  rw [spProg_funs hk (by omega), hblk, List.getD_eq_getElem _ _ hj]

theorem spProg_hasAt_off {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {k i : ℕ} {fs : List Expr}
    (hk : k < blks.length) (hblk : (blks.getD k []).drop i = fs) (hl : i + fs.length ≤ B) :
    (spProg B blks ps).HasAt (B * k + i) fs := by
  intro j hj
  subst hblk
  rw [Nat.add_assoc, spProg_funs hk (by omega)]
  have : i + j < (blks.getD k []).length := by
    rw [List.length_drop] at hj
    omega
  rw [List.getD_eq_getElem _ _ this, List.getElem_drop]

theorem spProg_fun {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {k : ℕ} {e : Expr} {rest : List Expr}
    (hk : k < blks.length) (hblk : blks.getD k [] = e :: rest) (hB : 0 < B) :
    (spProg B blks ps).funs[B * k]? = some e := by
  have := spProg_funs (ps := ps) hk hB (j := 0)
  rw [Nat.add_zero] at this
  rw [this, hblk]; rfl

theorem spProg_fun_off {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {k i : ℕ} {e : Expr}
    (hk : k < blks.length) (hblk : (blks.getD k []).getD i .nil = e) (hi : i < B) :
    (spProg B blks ps).funs[B * k + i]? = some e := by
  rw [spProg_funs hk hi, hblk]

theorem spProg_prim {B : ℕ} {blks : List (List Expr)} {ps : List Prim} {j : ℕ} {p : Prim}
    (h : ps[j]? = some p) : (spProg B blks ps).prims[j]? = some p := h

end GI.Impl
