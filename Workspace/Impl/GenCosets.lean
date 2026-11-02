import Workspace.Lang.Lib.Schreier

/-!
# Coset representatives of the kernel of a block action

The enumeration and product steps of the dispatcher (Algorithm 5) split `G` into the cosets of
a subgroup `K` and solve one child per coset. For the kernel of the action on a block system we
get the representatives from the orbit program with a transversal (`Workspace.Lang.Lib.OrbitT`).

**The idea.** A block system is given by a labeling `lab : Fin n → ℕ` (equal labels mean the
same block). A permutation `g` moves a labeling by `g · f = f ∘ g⁻¹` (`labAct`); this is an
action of the whole symmetric group. An element of `G` fixes `lab` exactly when it maps every
block to itself, so the stabilizer of `lab` in `G` is the kernel `K`. The orbit of `lab` under
`G` is in bijection with the cosets `G / K`: the orbit program returns pairs `(f, t)` with
`t ∈ G` and `t · lab = f`, one for each orbit point. The elements `t` are then one
representative per coset (`labPairs_cover`, `labPairs_distinct`).

**The program.** `labActF` computes `g · f` from `encPerm g` and `encFun f`: it inverts `g` and
reads `f` at the points `g⁻¹ i` (`precomp_spec`: `compose` reads any list at the points of a
permutation). `cosetsFuns` is the orbit program with this action (`cosets_spec`). Its cost is a
polynomial in `n`, the number of generators and a bound `B` on the number of cosets (`B` comes
from `GroupOrder`).
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)
open Equiv

variable {n : ℕ}

/-! ### Reading a list at the points of a permutation -/

/-- **Precomposition.** `compose` on `[encFun f, encPerm τ]` gives `encFun (f ∘ τ)`, when the
values of `f` are at most `n`. -/
theorem precomp_spec {P : Program} {b : ℕ} (h : P.HasAt b (composeFuns b)) (f : Fin n → ℕ)
    (hf : ∀ i, f i ≤ n) (τ : Equiv.Perm (Fin n)) :
    FunDet P b (.list [encFun f, encPerm τ]) (encFun (f ∘ τ)) (permK * (n + 1) ^ 3) := by
  have hE := wt_encFun_le_sq f hf
  have hE' := wt_encPerm_le τ
  have hf' : ∀ x ∈ (List.finRange n).map (fun i => Val.nat (τ i)),
      FunAll P (b + 3) (.list [encFun f, x]) (fun w cost =>
        (∀ i : Fin n, x = .nat i → w = .nat (f i)) ∧ cost ≤ 100 * (n + 1) ^ 2) := by
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
      nlinarith
  refine ((map_spec h.left hf').mono fun w cost hw => ?_)
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' := forall₂_map_eq (g := fun i => Val.nat ((f ∘ τ) i))
    (fun a _ w hw => by rw [hw (τ a) rfl]; rfl) hws
  subst hws'
  refine ⟨rfl, ?_⟩
  have hw := wt_encFun_le_sq (f ∘ τ) fun i => hf _
  have ha := wt_list2_le (encFun f) (encPerm τ)
  simp only [List.map_map, List.length_map, List.length_finRange] at hc
  have hs : ((List.finRange n).map ((fun _ => 100 * (n + 1) ^ 2) ∘
      fun i => Val.nat (τ i))).sum = n * (100 * (n + 1) ^ 2) := by
    rw [show ((fun _ => 100 * (n + 1) ^ 2) ∘ fun i : Fin n => Val.nat (τ i)) =
      fun _ => 100 * (n + 1) ^ 2 from rfl, List.map_const', List.sum_replicate,
      List.length_finRange, smul_eq_mul]
  have e1 : (Val.list [encFun f, Val.list ((List.finRange n).map fun i => Val.nat (τ i))]).wt =
    (Val.list [encFun f, encPerm τ]).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => Val.nat ((f ∘ τ) i))).wt =
    (encFun (f ∘ τ)).wt := rfl
  rw [hs, e1, e2] at hc
  have h1 : mapK * (n + 1) * ((Val.list [encFun f, encPerm τ]).wt + (encFun (f ∘ τ)).wt + 1) ≤
      mapK * (n + 1) * (27 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h2 : n * (100 * (n + 1) ^ 2) ≤ 100 * (n + 1) ^ 3 := by nlinarith
  have h3 : mapK * (n + 1) * (27 * (n + 1) ^ 2) = 27000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  simp only [permK]
  omega

/-! ### The action on labelings -/

/-- A permutation moves a labeling: `g · f = f ∘ g⁻¹`. -/
def labAct (g : Perm (Fin n)) (f : Fin n → ℕ) : Fin n → ℕ := fun i => f (g⁻¹ i)

theorem isAct_lab : IsAct (n := n) labAct :=
  ⟨fun f => by funext i; simp [labAct], fun g h f => by funext i; simp [labAct, mul_inv_rev]⟩

/-- The key of a labeling: its list of values. -/
def labKey (f : Fin n → ℕ) : List ℕ := (List.finRange n).map f

theorem natList_labKey (f : Fin n → ℕ) : natList (labKey f) = encFun f := by
  simp [natList, labKey, encFun, List.map_map, Function.comp_def]

theorem labKey_injective : Function.Injective (labKey (n := n)) := fun f g h => by
  funext i
  have := congrArg (fun l => l[(i : ℕ)]?) h
  simpa [labKey] using this

/-- The action on labelings: on `[ac, encPerm g, encFun f]`, the value `encFun (g · f)`. -/
def labActF (inv comp : ℕ) : Expr := .call comp (mk2 (arg 2) (.call inv (arg 1)))

theorem labAct_spec {P : Program} {f inv comp : ℕ} (hf : P.funs[f]? = some (labActF inv comp))
    (hi : P.HasAt inv (invFuns inv)) (hc : P.HasAt comp (composeFuns comp)) (ac : Val)
    (g : Perm (Fin n)) (l : Fin n → ℕ) (hl : ∀ i, l i ≤ n) :
    FunDet P f (.list [ac, encPerm g, natList (labKey l)]) (natList (labKey (labAct g l)))
      (5 * (Val.list [ac, encPerm g, natList (labKey l)]).wt + 200000 * (n + 1) ^ 4) := by
  rw [natList_labKey, natList_labKey]
  have d1 := Det.arg' (P := P) (vs := [ac, encPerm g, encFun l]) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := [ac, encPerm g, encFun l]) (rest := []) (j := 2) rfl
  have dg := Det.call d1 (inv_spec hi g)
  have hla : labAct g l = l ∘ (g⁻¹ : Perm (Fin n)) := rfl
  rw [hla]
  refine FunDet.intro hf ((Det.call (Det.mk2 d2 dg) (precomp_spec hc l hl g⁻¹)).mono ?_)
  have w2 := wt_encPerm_le g
  have w2' := wt_encPerm_le g⁻¹
  have w3 := wt_encFun_le_sq l hl
  have w4 := wt_encFun_le_sq (l ∘ (g⁻¹ : Perm (Fin n))) fun i => hl _
  have w5 := wt_list2_le (encFun l) (encPerm g⁻¹)
  have hN : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [permK, invK]
  omega

/-! ### The program -/

/-- The coset program, at base `b` (35 functions): the orbit program with the action on
labelings. -/
def cosetsFuns (b : ℕ) : List Expr :=
  orbTFuns b (b + 22) ++ [labActF (b + 23) (b + 12)] ++ invFuns (b + 23)

/-- The constant of the coset program. -/
def cosetsK : ℕ := 10 ^ 9

/-- **The orbit of a labeling with a transversal.** On
`[0, [encPerm g | g ∈ gs], encFun lab, B, n]`, when the orbit of `lab` has at most `B` points,
the result is the value of a list `L` of pairs `(f, t)`: the labelings `f` are the orbit of `lab`
without repeats, `t ∈ ⟨gs⟩` and `t · lab = f`. -/
theorem cosets_spec {P : Program} {b : ℕ} (h : P.HasAt b (cosetsFuns b))
    (gs : List (Perm (Fin n))) (lab : Fin n → ℕ) (hlab : ∀ i, lab i ≤ n) {B : ℕ}
    (hB : (actOrbit labAct gs lab).ncard ≤ B) :
    FunAll P b (.list [.nat 0, .list (gs.map encPerm), encFun lab, .nat B, .nat n])
      (fun w cost => ∃ L : List ((Fin n → ℕ) × Perm (Fin n)), w = encPairs labKey L ∧
        (L.map Prod.fst).Nodup ∧ (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct gs lab) ∧
        (∀ p ∈ L, p.2 ∈ genGroup gs ∧ labAct p.2 lab = p.1) ∧
        cost ≤ cosetsK * (gs.length + B + 4 * (n + 1) ^ 2 + 20) ^ 6) := by
  simp only [cosetsFuns] at h
  have hO : P.HasAt b (orbTFuns b (b + 22)) := h.left.left
  have hA : P.funs[b + 22]? = some (labActF (b + 23) (b + 12)) := by
    simpa [length_orbTFuns] using h.left.right.single
  have hI : P.HasAt (b + 23) (invFuns (b + 23)) := by
    simpa [length_orbTFuns, Nat.add_assoc] using h.right
  obtain ⟨-, -, hP, -⟩ := OrbTAt.pieces hO
  have hc : P.HasAt (b + 12) (composeFuns (b + 12)) := by simpa [Nat.add_assoc] using hP.comp
  set S := gs.length + B + 4 * (n + 1) ^ 2 + 20 with hS
  have hS1 : 1 ≤ S := by omega
  have p2 : (n + 1) ^ 2 ≤ S := by omega
  have p4 : (n + 1) ^ 4 ≤ S ^ 2 := by
    have := Nat.pow_le_pow_left p2 2; rw [← pow_mul] at this; exact this
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  -- every labeling of the orbit has values at most `n`
  have horb : ∀ y ∈ actOrbit labAct gs lab, ∀ i, y i ≤ n := by
    rintro y ⟨g, -, rfl⟩ i
    exact hlab _
  have H : OrbTHyp P (b + 22) labKey labAct gs lab (.nat 0) S (300000 * S ^ 2) :=
    { isAct := isAct_lab
      key_inj := labKey_injective
      hn := by nlinarith
      hm := by omega
      hac := by have := wt_nat_le 0; omega
      hkey := fun y hy => by
        rw [natList_labKey]; have := wt_encFun_le_sq y (horb y hy); omega
      hfa := fun g _ y hy => (labAct_spec hA hI hc (.nat 0) g y (horb y hy)).mono (by
        have w1 := wt_list3_le (.nat 0) (encPerm g) (natList (labKey y))
        have w2 := wt_encPerm_le g
        have w3 : (natList (labKey y)).wt ≤ 4 * (n + 1) ^ 2 := by
          rw [natList_labKey]; exact wt_encFun_le_sq y (horb y hy)
        have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
        omega) }
  have := orbT_spec hO H (by omega) hB
  rw [natList_labKey] at this
  refine this.mono fun w cost hw => ?_
  obtain ⟨L, h1, h2, h3, h4, -, h6⟩ := hw
  refine ⟨L, h1, h2, h3, h4, ?_⟩
  have e6 : S ^ 2 * (300000 * S ^ 2) = 300000 * S ^ 4 := by ring
  have p46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  simp only [cosetsK, orbTK] at h6 ⊢
  omega

end GI.Lang
