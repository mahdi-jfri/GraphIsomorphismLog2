module

public import Workspace.Impl.GenEnum

@[expose] public section

/-!
# `CombineExact` of an aggregation round

Algorithm 5, `CombineExact`: the answer of the round is the union of the exact pieces of the
items and of the translated continuation answers, `(⋃ pieces) ∪ ⋃_j τ_j A_j` (`Run.aggregate`).
This union is the set of parent isomorphisms (`Run.exact`), so it is empty or a left coset.

Both kinds of pieces reach the program as values `encPiece (t, a)`: a permutation `t` and an
accumulator value `a` (`[]` or `[x, gens]`), standing for the set `t · accSet a`.

* an item piece `p` comes from the items as `encPiece (t, a)` with `t · accSet a = e(p)`
  (`toFin e '' p`; the contract `BranchV` of the items);
* a continuation piece is `[encPerm e(τ_j), u_j]` with `u_j` a canonical answer of `A_j`
  (`AnsC.acc`), standing for `e(τ_j) · e(A_j) = e(τ_j A_j)`.

The program (`ceF`) appends the two lists, folds the coset rule over them (`comb_spec`) and takes
the coset normal form (`cosetNF_spec`, cited **Membership**). `ce_spec` is the result:
the output is in coset normal form for the union of the sets of the pieces, at a cost polynomial
in the weight of the input (`ceCost`). `ce_union` computes that union for the pieces of a round.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership)
open scoped Pointwise

variable {k : ℕ}

/-! ### The program -/

/-- **`CombineExact`** on `[item pieces, continuation pieces]`: append, fold the coset rule
(the fold module at `bc`), normal form (the module at `bn`). `bapp` is an append module. -/
def ceF (bapp bc bn : ℕ) : Expr :=
  .call bn (.call bc (mk3 (.nat 0) (.call bapp (mk2 (arg 0) (arg 1))) .nil))

/-- The weight bound of the input of the fold, for an input of weight `W`. -/
def ceInW (W : ℕ) : ℕ := 2 * W + 30

/-- The weight bound of the folded accumulator, for an input of weight `W`. -/
def ceOutW (k W : ℕ) : ℕ := 100 * ((ceInW W + 2) * (k + 1)) ^ 2

/-- **The cost bound of `CombineExact`** on an input of weight `W`. -/
noncomputable def ceCost (hm : Membership) (k W : ℕ) : ℕ :=
  loopModK * (W + 1) * (3 * W + 1) + combCost k (ceInW W) + cosetNFCost hm k (ceOutW k W) +
    20 * W + 4 * ceInW W + 2 * ceOutW k W + 2 * ansW k + 100

/-- **`CombineExact` meets its specification.** If the union of the sets of the pieces is empty or
a left coset, the output is its coset normal form. -/
theorem ce_spec (hm : Membership) {Pg : Program} {f bapp bc g comp inv app bn jm : ℕ}
    (hf : Pg.funs[f]? = some (ceF bapp bc bn)) (hap : Pg.HasAt bapp (appendFuns bapp))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    (pcs cps : List (Perm (Fin k) × Acc k))
    (hU : unionSet (pcs ++ cps) = ∅ ∨ ∃ (c : Perm (Fin k)) (H : Subgroup (Perm (Fin k))),
      unionSet (pcs ++ cps) = c • (H : Set _)) :
    FunAll Pg f (.list [.list (pcs.map encPiece), .list (cps.map encPiece)]) (fun u cost =>
      CosetC k u (unionSet (pcs ++ cps)) ∧
        cost ≤ ceCost hm k (Val.list [.list (pcs.map encPiece), .list (cps.map encPiece)]).wt) := by
  set xs := pcs.map encPiece with hxs
  set ys := cps.map encPiece with hys
  set a := Val.list [.list xs, .list ys] with ha
  set W := a.wt with hW
  set ps := pcs ++ cps with hps
  have hxW : (Val.list xs).wt < W := wt_le_wt_list (by simp)
  have hyW : (Val.list ys).wt < W := wt_le_wt_list (by simp)
  have hylen : ys.length < (Val.list ys).wt := length_lt_wt_list ys
  have hxy : xs ++ ys = ps.map encPiece := by simp [hxs, hys, hps]
  have ea : (Val.list [Val.list xs, Val.list ys]).wt = W := rfl
  have hsum : (Val.list xs).wt + (Val.list ys).wt < W := by
    have := sum_wt_lt_wt_list [Val.list xs, Val.list ys]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    omega
  -- the arguments
  have d0 := Det.arg' (P := Pg) (vs := [.list xs, .list ys]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := Pg) (vs := [.list xs, .list ys]) (rest := []) (j := 1) rfl
  have dm := Det.mk2 d0 d1
  -- the append
  have hap' := append_spec hap xs ys
  have dapp := Det.call dm (w := .list (xs ++ ys)) (cb := loopModK * (ys.length + 1) *
    (W + ys.length + W + 1)) (hap'.mono fun w c h => ⟨h.1, by
      have h2 := h.2
      rw [h.1] at h2
      have := wt_list_append_le xs ys
      have : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
          (Val.list (xs ++ ys)).wt + 1) ≤ loopModK * (ys.length + 1) * (W + ys.length + W + 1) :=
        Nat.mul_le_mul_left _ (by rw [ea]; omega)
      omega⟩)
  have d3 := Det.mk3 (Det.nat (P := Pg) (env := [a]) 0) dapp Det.nil
  rw [hxy] at d3
  -- the fold
  have hcomb := Det.call d3 (comb_spec hbc hg hcomp hinv happ (.nat 0) ps)
  -- the union is empty or a coset, so the fold gives a coset value of it
  have hCE := combine_cosetOrEmpty ps hU
  refine FunAll.intro hf (EvalAll.call_funAll hcomb fun w0 ca h0 => ?_)
  obtain ⟨rfl, hca⟩ := h0
  refine (cosetNF_spec hm hbn hjm hCE).mono fun u cb hu => ⟨hu.1, ?_⟩
  obtain ⟨hC, hcb⟩ := hu
  -- weights
  have hpw : (Val.list (ps.map encPiece)).wt ≤ W := by
    rw [← hxy]; have := wt_list_append_le xs ys; omega
  have hin : (Val.list [.nat 0, .list (ps.map encPiece), .list []]).wt ≤ ceInW W := by
    have h1 := wt_list3_le (.nat 0) (.list (ps.map encPiece)) (.list [])
    have := wt_nat_le 0
    rw [wt_list_nil] at h1
    unfold ceInW; omega
  have hcc := combCost_mono k hin
  have hL : ∀ c0 gs, combine ps = some (c0, gs) → gs.length ≤ ceInW W := by
    intro c0 gs h
    have h1 := length_combine ps c0 gs h
    have h2 := sum_accLen_le ps
    have h3 := sum_wt_lt_wt_list (ps.map encPiece)
    have : (Val.list (ps.map encPiece)).wt < (Val.list [.nat 0, .list (ps.map encPiece),
      .list []]).wt := wt_le_wt_list (by simp)
    omega
  have hacc : (encAcc (combine ps)).wt ≤ ceOutW k W := wt_encAcc_le (combine ps) hL
  have hnf := cosetNFCost_mono hm k hacc
  have hwu : u.wt ≤ ansW k := by
    rcases hC with ⟨rfl, -⟩ | ⟨x, hs, rfl, hl, -⟩
    · simp [ansW]
    · have h1 := wt_list2_le (encPerm x) (encGroup hs)
      have h2 := wt_encPerm_le x
      have h3 : GroupValC k (encGroup hs) (gens hs) := ⟨hs, rfl, rfl, hl⟩
      have := h3.wt_le
      unfold ansW; omega
  have hy1 : loopModK * (ys.length + 1) * (W + ys.length + W + 1) ≤
      loopModK * (W + 1) * (3 * W + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hw2 := wt_list2_le (.list xs) (.list ys)
  have hxyw : (Val.list (xs ++ ys)).wt ≤ W := by
    have := wt_list_append_le xs ys; omega
  rw [← hxy] at hin
  have e3 : (Val.list [.nat 0, .list (ps.map encPiece), .list []]).wt ≤ ceInW W := by
    rw [← hxy]; exact hin
  unfold ceCost
  simp only [ea] at hca
  have := wt_nat_le 0
  omega

/-! ### The pieces of a round -/

variable {Ω : Type}

/-- The set of a piece value: `t · accSet a`. -/
def ceSet (p : Perm (Fin k) × Acc k) : Set (Perm (Fin k)) := p.1 • accSet p.2

theorem unionSet_eq_iUnion (ps : List (Perm (Fin k) × Acc k)) :
    unionSet ps = ⋃ p ∈ ps, ceSet p := by
  ext g; simp [unionSet, ceSet]

/-- **The union of the pieces of a round.** If the item pieces `pcs` stand for the sets of `ps`
(entry by entry) and the continuation pieces stand for the translates `τ_j A_j`, the union of the
sets of all pieces is the image of `(⋃ ps) ∪ ⋃_j τ_j A_j`. -/
theorem ce_union (e : Ω ≃ Fin k) (pieces : List (Set (Perm Ω))) (pcs : List (Perm (Fin k) × Acc k))
    (hl : pcs.length = pieces.length)
    (hp : ∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i])
    {n : ℕ} (τ : Fin n → Perm Ω) (A : Fin n → Set (Perm Ω)) (cps : List (Perm (Fin k) × Acc k))
    (hcl : cps.length = n)
    (hc : ∀ j : Fin n, ∀ h : (j : ℕ) < cps.length, ceSet cps[(j : ℕ)] = toFin e '' (τ j • A j)) :
    unionSet (pcs ++ cps) = toFin e '' ((⋃ p ∈ pieces, p) ∪ ⋃ j, τ j • A j) := by
  rw [unionSet_eq_iUnion, Set.image_union, Set.image_iUnion₂, Set.image_iUnion]
  ext g
  simp only [List.mem_append, Set.mem_iUnion, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨p, hp' | hp', hg⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
      left
      refine ⟨pieces[i], List.getElem_mem (by omega), ?_⟩
      rw [← hp i hi (by omega)]; exact hg
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
      right
      refine ⟨⟨i, by omega⟩, ?_⟩
      rw [← hc ⟨i, by omega⟩ hi]; exact hg
  · rintro (⟨p, hp', hg⟩ | ⟨j, hg⟩)
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
      refine ⟨pcs[i], Or.inl (List.getElem_mem (by omega)), ?_⟩
      rw [hp i (by omega) hi]; exact hg
    · refine ⟨cps[(j : ℕ)], Or.inr (List.getElem_mem (by omega)), ?_⟩
      rw [hc j (by omega)]; exact hg

/-- A continuation piece `[encPerm e(τ), u]` with `u` a canonical answer of `A` stands for
`τ A`. -/
theorem ce_contPiece (e : Ω ≃ Fin k) (τ : Perm Ω) {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) :
    ∃ a : Acc k, Val.list [encPerm (toFin e τ), u] = encPiece (toFin e τ, a) ∧
      ceSet (toFin e τ, a) = toFin e '' (τ • A) := by
  obtain ⟨a, rfl, ha⟩ := h.acc
  refine ⟨a, rfl, ?_⟩
  rw [ceSet, image_toFin_smul, ha]

/-- **The answer of a round.** For a union that is the image of the exact answer of the parent,
the normal form is a canonical answer. -/
theorem ce_ansC (e : Ω ≃ Fin k) {u : Val} {U : Set (Perm Ω)}
    (h : CosetC k u (toFin e '' U)) : AnsC e u U := CosetC.ansC h

end GI.Impl
