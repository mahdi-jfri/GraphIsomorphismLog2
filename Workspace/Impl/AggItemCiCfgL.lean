import Workspace.Impl.AggItemCiCfgS
import Workspace.Impl.AggItemCiCfgC

/-!
# The configuration branch: the list of pair colors

The canonical value `itcqArg` of the pair structure codes each pair color by its first place
in the list `itcqCL` of all pair colors of `X`, then of `Y`. This file builds the list of the
pair colors of one configuration as a program: `map` of the pair color program `itcqPcF`
(`itcq_pcF_spec`) over the positions `0, …, n² - 1` (`itcq_pcs_spec`).

The costs are counted in weights: the color values can be about `q^κ`, so a cost bound by
values would be too large.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

variable {q : ℕ}

/-- The pair colors of `Z` by numbered position, when the fiber of `Z` has `n` points. -/
def itcqPcsV (Z : PairCfg q) (n : ℕ) (h : Z.fiber.card = n) : List ℕ :=
  (List.finRange (n * n)).map fun t => itcqPC Z h ((itciPE n).symm t)

theorem itcqCL_eq (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) :
    itcqCL X Y hc = itcqPcsV X _ rfl ++ itcqPcsV Y _ hc.symm := rfl

/-- A list related entrywise to `xs` by `w = F x` is `xs.map F`. -/
theorem itcq_f2_map {F : Val → Val} :
    ∀ {xs ws : List Val}, List.Forall₂ (fun x w => w = F x) xs ws → ws = xs.map F
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [h, itcq_f2_map t]; rfl

/-- A pair color weighs at most the color table. -/
theorem itcq_pcw (Z : PairCfg q) (a b : Fin q) : (Val.nat (Z.col a b)).wt ≤ (rcColVal Z).wt :=
  (st_wt_mem (List.mem_of_getElem? (encFun_getElem? (Z.col a) b))).trans
    (st_wt_mem (List.mem_of_getElem? (itcq_col_get Z a)))

/-- The weight of a list of numbers, each weighing at most `B`. -/
theorem itcq_natList_wt {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, (Val.nat x).wt ≤ B) :
    (natList l).wt ≤ 2 * (l.length * B) + l.length + 4 := by
  have h1 := wt_list_le (l.map Val.nat)
  have h2 : ((l.map Val.nat).map Val.wt).sum ≤ l.length * B := by
    have := List.sum_le_card_nsmul ((l.map Val.nat).map Val.wt) B (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact h y hy)
    simpa using this
  simp only [List.length_map] at h1
  unfold natList; omega

/-- The cost bound of the list of pair colors. -/
def itcqMC (W : ℕ) : ℕ := 10 ^ 4 * (W + 2) ^ 3

theorem itcq_mc_arith {m W o s c : ℕ} (hm : m ≤ W) (ho : o ≤ 2 * (m * W) + m + 4)
    (hs : s ≤ m * (50 * (4 * W + 10 + 1)))
    (hc : c ≤ s + 1000 * (m + 1) * (W + o + 1)) : c ≤ itcqMC W := by
  unfold itcqMC
  have h1 : m * W ≤ W * W := Nat.mul_le_mul_right _ hm
  have h2 : m * (50 * (4 * W + 10 + 1)) ≤ W * (50 * (4 * W + 11)) := Nat.mul_le_mul_right _ hm
  have h3 : (m + 1) * (W + o + 1) ≤ (W + 1) * (2 * (W * W) + 2 * W + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem itcq_mc_arith2 {m W a o s c : ℕ} (ha : a ≤ W)
    (hc : c ≤ s + mapK * (m + 1) * (a + o + 1)) : c ≤ s + 1000 * (m + 1) * (W + o + 1) := by
  have := Nat.mul_le_mul_left (1000 * (m + 1)) (show a + o + 1 ≤ W + o + 1 by omega)
  unfold mapK at hc; exact hc.trans (Nat.add_le_add_left this s)

section Prog

variable {P : Program}

/-- **The list of the pair colors of `Z`**, by `map` of `itcqPcF` over `0, …, n² - 1`. -/
theorem itcq_pcs_spec {mb fpc : ℕ} (hm : P.HasAt mb (mapFuns mb fpc))
    (hf : P.funs[fpc]? = some itcqPcF) (Z : PairCfg q) {n : ℕ} (h : Z.fiber.card = n) {W : ℕ}
    (hW : (Val.list [.list [rcColVal Z, itcqFV Z, .nat n], natList (List.range (n * n))]).wt ≤ W) :
    FunAll P mb (.list [.list [rcColVal Z, itcqFV Z, .nat n], natList (List.range (n * n))])
      (fun w cost => w = natList (itcqPcsV Z n h) ∧ cost ≤ itcqMC W) := by
  subst h
  set m := Z.fiber.card * Z.fiber.card with hmdef
  set c : Val := .list [rcColVal Z, itcqFV Z, .nat Z.fiber.card] with hcdef
  let F : Val → Val := fun x => match x with
    | .nat t => if ht : t < m then .nat (itcqPC Z rfl ((itciPE _).symm ⟨t, ht⟩)) else .nat 0
    | _ => .nat 0
  have hcw : c.wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hRw : (natList (List.range m)).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hmw : m ≤ W := by
    have := length_lt_wt_list ((List.range m).map Val.nat)
    simp only [List.length_map, List.length_range] at this
    unfold natList at hRw; omega
  have hcol : (rcColVal Z).wt ≤ c.wt := st_wt_mem (by simp)
  have key := map_spec (P := P) hm (c := c) (xs := (List.range m).map Val.nat)
    (R := fun x w => w = F x) (B := fun _ => 50 * (4 * W + 10 + 1)) (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      have ht' := List.mem_range.1 ht
      have h2 := wt_list2_le c (.nat t)
      have := wt_nat_le t
      have hx : (Val.list [c, .nat t]).wt ≤ 4 * W + 10 := by omega
      refine FunAll.mono (itcq_pcF_spec hf Z ⟨t, ht'⟩ (W := 4 * W + 10) hx)
        fun w cost ⟨hw, hc⟩ => ⟨?_, hc⟩
      subst hw
      simp only [F, dif_pos ht'])
  refine key.mono fun w cost ⟨ws, hw, h2, hc⟩ => ?_
  have hws := itcq_f2_map h2
  have hval : w = natList (itcqPcsV Z Z.fiber.card rfl) := by
    rw [hw, hws, natList, itcqPcsV, ← List.map_coe_finRange_eq_range]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, F, dif_pos t.isLt, Fin.eta]
  refine ⟨hval, ?_⟩
  have hlen : (itcqPcsV Z Z.fiber.card rfl).length = m := by simp [itcqPcsV, m]
  have hout := itcq_natList_wt (l := itcqPcsV Z Z.fiber.card rfl) (B := W) (by
    intro x hx
    simp only [itcqPcsV, List.mem_map] at hx
    obtain ⟨t, -, rfl⟩ := hx
    exact (itcq_pcw Z _ _).trans (by omega))
  rw [hlen] at hout
  rw [← hval] at hout
  simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
    smul_eq_mul] at hc
  have hin : (Val.list [c, .list ((List.range m).map Val.nat)]).wt ≤ W := hW
  exact itcq_mc_arith hmw hout le_rfl (itcq_mc_arith2 hin hc)

end Prog

end GI.Impl
