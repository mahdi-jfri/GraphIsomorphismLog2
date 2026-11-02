import Workspace.Impl.VsFAlgSpanStep

/-!
# A pass of the algebra basis program

`vsFAFold_spec`: the `foldl` of the insertion step over the generators, for one matrix `M`.
This is the work of `vsFAOuter` (`Impl/VsFAlgSpan.lean`) when `Bm[i]` exists.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

theorem VsAccFits.mono {p N lx lt k k' : ℕ} {acc : List VsRow × List (List ℕ)}
    (h : VsAccFits p N lx lt k acc) (hk : k ≤ k') : VsAccFits p N lx lt k' acc :=
  ⟨h.rows, h.nrows.trans hk, h.rels, h.nrels.trans hk⟩

theorem VsFAFits.mono {p N d k k' : ℕ}
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (h : VsFAFits p N d k st)
    (hk : k ≤ k') : VsFAFits p N d k' st :=
  ⟨h.acc.mono hk, h.sq, h.nb.trans hk⟩

theorem vsFA_foldl_take_succ {α β : Type*} (f : β → α → β) (l : List α) (a : β) (j : ℕ)
    (hj : j < l.length) : (l.take (j + 1)).foldl f a = f ((l.take j).foldl f a) l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

theorem vsFAFold_fits {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) {z : List ℕ}
    (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hdN : d * d ≤ N) {M : List (List ℕ)}
    (hM : VsFSq p d M) : ∀ (gs : List (List (List ℕ))) (k : ℕ)
    (st : (List VsRow × List (List ℕ)) × List (List (List ℕ))), VsFAFits p N d k st →
    VsFAFits p N d (k + gs.length) (gs.foldl (vsFAInner p z M) st)
  | [], k, st, h => h
  | g :: gs, k, st, h => by
    have := vsFAFold_fits hp hpN hzb hzl hdN hM gs (k + 1) _
      (vsFAInner_fits hp hpN h hzb hzl hdN hM (g := g))
    rw [List.foldl_cons, List.length_cons, show k + (gs.length + 1) = k + 1 + gs.length by omega]
    exact this

theorem vsFAFold_cost {N L c S T X : ℕ} (hL : L ≤ N) (hS : S ≤ L * (10 ^ 8 * X))
    (hT : T ≤ 1000 * (L + 1) * (2200 * (N + 1) ^ 4)) (hX : X = (N + 1) ^ 5)
    (hc : c ≤ S + T) : c ≤ 2 * 10 ^ 8 * (N + 1) ^ 6 := by
  have e6 : (N + 1) ^ 6 = (N + 1) * X := by rw [hX]; ring
  have h1 : L * (10 ^ 8 * X) ≤ (N + 1) * (10 ^ 8 * X) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * (L + 1) * (2200 * (N + 1) ^ 4) ≤ 1000 * (N + 1) * (2200 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h3 : 1000 * (N + 1) * (2200 * (N + 1) ^ 4) = 2200000 * X := by rw [hX]; ring
  have h4 : (N + 1) * (10 ^ 8 * X) = 10 ^ 8 * ((N + 1) * X) := by ring
  have h5 : X ≤ (N + 1) * X := Nat.le_mul_of_pos_left _ (by omega)
  rw [e6]
  omega

/-- **A pass.** On `[[p, z, M], generators, state]`, with at most `N - |gs|` insertions so
far, the result is the state after inserting `M g` for all generators `g`. -/
theorem vsFAFold_spec {P : Program} {fo f mm fl sa : ℕ} (hfo : P.HasAt fo (foldlFuns fo f))
    (hf : P.funs[f]? = some (vsFAInnerF mm fl sa))
    (hmm : P.HasAt mm (vsFMatMulFuns mm)) (hfl : P.HasAt fl (vsFFlatFuns fl))
    (hsa : P.funs[sa]? = some (vsAllStepF (sa + 1))) (hin : P.HasAt (sa + 1) (vsInsertFuns (sa + 1)))
    {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d * d ≤ N)
    {gs : List (List (List ℕ))} (hgs : ∀ g ∈ gs, VsFSq p d g) (hk : k + gs.length ≤ N)
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (hst : VsFAFits p N d k st)
    {z : List ℕ} (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) {M : List (List ℕ)}
    (hM : VsFSq p d M) :
    FunDet P fo (.list [vsFACtx p z M, vsFMatsVal gs, vsFAVal st])
      (vsFAVal (gs.foldl (vsFAInner p z M) st)) (2 * 10 ^ 8 * (N + 1) ^ 6) := by
  have hd : d ≤ N := le_trans (Nat.le_mul_self d) hdN
  have hfit : ∀ j, j ≤ gs.length →
      VsFAFits p N d (k + j) ((gs.take j).foldl (vsFAInner p z M) st) := by
    intro j hj
    have := vsFAFold_fits hp hpN hzb hzl hdN hM (gs.take j) k st hst
    rwa [List.length_take, Nat.min_eq_left hj] at this
  refine (foldl_spec hfo (c := vsFACtx p z M) (xs := gs.map fun g => Val.list (g.map natList))
    (acc0 := vsFAVal st) (M := 600 * (N + 1) ^ 4) (B := fun _ => 10 ^ 8 * (N + 1) ^ 5)
    (Inv := fun j acc => acc = vsFAVal ((gs.take j).foldl (vsFAInner p z M) st)) (by simp)
    (fun j acc hj hacc => by
      rw [List.length_map] at hj
      rw [hacc]
      exact wt_vsFAVal_le hpN hd (by omega) (hfit j hj))
    (fun j acc hj hacc => by
      rw [List.length_map] at hj
      rw [hacc, List.getElem_map]
      refine FunAll.mono (vsFAInner_spec hf hmm hfl hsa hin hp hpN hdN (by omega) (hfit j hj.le)
        hzb hzl hM (hgs _ (List.getElem_mem hj))) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, vsFA_foldl_take_succ _ _ _ _ hj])).mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have hK : loopModK = 1000 := rfl
    rw [hK] at hc
    have wc : (vsFACtx p z M).wt ≤ 100 * (N + 1) ^ 3 := by
      have h1 := wt_vsFSq_le hpN hd hM
      have h2 := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
      have h3 := wt_list3_le (.nat p) (natList z) (.list (M.map natList))
      have h4 := wt_nat_le p
      have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have e : (vsFACtx p z M).wt = (Val.list [.nat p, natList z, .list (M.map natList)]).wt := rfl
      omega
    have wg := wt_vsFMatsVal_le hpN hd hgs (by omega)
    have ws := wt_vsFAVal_le hpN hd (by omega) hst
    have w3 := wt_list3_le (vsFACtx p z M) (vsFMatsVal gs) (vsFAVal st)
    have eg : vsFMatsVal gs = Val.list (gs.map fun g => Val.list (g.map natList)) := rfl
    rw [eg] at wg w3
    have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hN4 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
    exact vsFAFold_cost (L := gs.length) (by omega) le_rfl
      (Nat.mul_le_mul_left _ (by omega)) rfl hc

end GI.Impl
