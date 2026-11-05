module

public import Workspace.Impl.ColHier

@[expose] public section

/-!
# The child partitions of the column step from position keys

The program labels each position by a number (a *key*), and the class numbering `cls_spec` turns
the keys of the domain positions into canonical partition labels (`colPartVal`). This file says
which keys give the partitions that the column step stores, for the column step `colStep` at a
switch `J` and a base point `b₀`:

* the columns: the orbit label of the column coordinate (`colCols_val`);
* the lower part of level `k`: the row label, the label of level `k`, and the orbit label of the
  column coordinate, in mixed radix `n + 1` (`colLower_val`);
* the upper part of level `k`: the least orbit label over the level-`(k+1)` block of the column
  coordinate (`colUpper_val`).

The positions are numbered by `eΩ : Ω ≃ Fin n`. The program knows the column coordinate of a
domain position (`colB`), its row label (`rl`) and the stored hierarchy labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {n : ℕ} {S : State Ω C} {L : GiantLabels S}

/-- **Mixed radix keys are injective** on digits below the base. -/
theorem colRadix_inj {N a b c a' b' c' : ℕ} (hb : b < N) (hc : c < N) (hb' : b' < N)
    (hc' : c' < N) : (a * N + b) * N + c = (a' * N + b') * N + c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have key : ∀ x y, (x * N + y) % N = y % N := fun x y => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    have h1 : c = c' := by
      have := congrArg (· % N) h
      simp only [key, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this
      exact this
    subst h1
    have h2 : a * N + b = a' * N + b' := by
      have hN : 0 < N := by omega
      have := Nat.eq_of_mul_eq_mul_right hN (Nat.add_right_cancel h)
      exact this
    have h3 : b = b' := by
      have := congrArg (· % N) h2
      simp only [key, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at this
      exact this
    subst h3
    have hN : 0 < N := by omega
    exact ⟨Nat.eq_of_mul_eq_mul_right hN (Nat.add_right_cancel h2), rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

namespace Col

variable (F : RowForm S L) [Finite Ω]
  (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
  (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (b₀ : F.B) (J : ℕ)
  (hJl : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
  (hhighJ : F.High (levOf ⊥ S.hier (J + 1)))
  (eΩ : Ω ≃ Fin n) (colB : Fin n → F.B) (hcol : ∀ v : S.dom, colB (eΩ v) = (F.e.symm v).1)
  (ol : F.B → ℕ) (hol : ∀ c d, ol c = ol d ↔ ∃ n : F.Nl, (n : F.Hb) • c = d)

include hcol hol in
/-- **The columns**: key `ol (colB i) + n + 1`. -/
theorem colCols_val :
    PartitionValC eΩ (encFun (Cls.repOf (Cls.keyOf (fun i => ol (colB i) + n + 1)
      (indF eΩ S.dom)))) (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).cols := by
  set I := (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).toColumnPre
  show PartitionValC eΩ _ I.cols
  rw [colCols_key I ol hol]
  refine colPartVal eΩ S _ _ (fun v => by omega) fun v w => ?_
  rw [hcol, hcol, colCB_dom, colCB_dom]
  show ol (F.e.symm v).1 + n + 1 = ol (F.e.symm w).1 + n + 1 ↔ ol (F.e.symm v).1 = ol (F.e.symm w).1
  omega

include hcol hol in
/-- **The lower part of level `k`**: key `(rl i (n+1) + lab i) (n+1) + ol (colB i) + (n+1)`,
with `lab` the labels of the stored level `k`. -/
theorem colLower_val (rl : Fin n → ℕ) (hrl : ∀ v : S.dom, rl (eΩ v) = (F.label v : ℕ))
    {k : ℕ} (hk : k < S.hier.length)
    (lab : Fin n → ℕ) (hlab : ∀ i j, lab i = lab j ↔ S.hier[k].part.r (eΩ.symm i) (eΩ.symm j))
    (hlabn : ∀ i, lab i < n + 1) (holn : ∀ c, ol c < n + 1) :
    PartitionValC eΩ (encFun (Cls.repOf (Cls.keyOf
      (fun i => (rl i * (n + 1) + lab i) * (n + 1) + ol (colB i) + (n + 1)) (indF eΩ S.dom))))
      ((colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).lowerPart k) := by
  rw [colLower_key F hint htr hinv hne b₀ J hJl hlowJ hhighJ hk (fun v => lab (eΩ v))
    (fun v w => by rw [hlab]; simp) ol hol]
  refine colPartVal eΩ S _ _ (fun v => by omega) fun v w => ?_
  rw [Nat.add_right_cancel_iff, colRadix_inj (hlabn _) (holn _) (hlabn _) (holn _), hrl, hrl,
    hcol, hcol, colCB_dom, colCB_dom]
  simp only [Prod.mk.injEq]
  rfl

include hcol hol in
/-- **The upper part of level `k`**: key `gU (colB i) + n + 1`, where `gU d` is the least orbit
label over the points `o` of row `i0` whose level-`k` label equals that of `d`. -/
theorem colUpper_val {k : ℕ} (hk : k < S.hier.length) (lab : Fin n → ℕ)
    (hlab : ∀ i j, lab i = lab j ↔ S.hier[k].part.r (eΩ.symm i) (eΩ.symm j)) (gU : F.B → ℕ)
    (hmin : ∀ d, (∃ o, lab (eΩ (F.e (o, F.i0))) = lab (eΩ (F.e (d, F.i0))) ∧ ol o = gU d) ∧
      ∀ o, lab (eΩ (F.e (o, F.i0))) = lab (eΩ (F.e (d, F.i0))) → gU d ≤ ol o) :
    PartitionValC eΩ (encFun (Cls.repOf (Cls.keyOf (fun i => gU (colB i) + n + 1)
      (indF eΩ S.dom)))) ((colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).upperPart k) := by
  set I := (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).toColumnPre
  have hblk := colBlk_lab F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ lab hk hlab
  have hkey : ∀ c d, gU c = gU d ↔ d ∈ I.sat (k + 1) c :=
    colSatKey I (k + 1) ol gU hol (fun d => by
      obtain ⟨⟨o, ho, he⟩, hle⟩ := hmin d
      refine ⟨⟨o, (hblk d o).2 ho.symm, he⟩, fun o' h' => hle o' ((hblk d o').1 h').symm⟩)
  show PartitionValC eΩ _ (I.upperPart k)
  rw [colUpper_key I k gU hkey]
  refine colPartVal eΩ S _ _ (fun v => by omega) fun v w => ?_
  rw [hcol, hcol, colCB_dom, colCB_dom]
  show gU (F.e.symm v).1 + n + 1 = gU (F.e.symm w).1 + n + 1 ↔ gU (F.e.symm v).1 = gU (F.e.symm w).1
  omega

include hol in
/-- **The ratio and the lower ratio of level `k` as counts**, with `A` labelling the level-`k`
blocks and `lab` the labels of the stored level `k`. -/
theorem colRatios_val {k : ℕ} (hk : k < S.hier.length) (lab : Fin n → ℕ)
    (hlab : ∀ i j, lab i = lab j ↔ S.hier[k].part.r (eΩ.symm i) (eΩ.symm j)) (A : F.B → ℕ)
    (hA : ∀ c d, d ∈ (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).blk k c ↔ A c = A d) :
    (RowForm.localTower F.e F.i0 (F.expLoc b₀) b₀ k).relIndex
        (RowForm.localTower F.e F.i0 (F.expLoc b₀) b₀ (k + 1)) =
      (A '' {c | lab (eΩ (F.e (c, F.i0))) = lab (eΩ (F.e (b₀, F.i0)))}).ncard ∧
    (RowForm.localTower F.e F.i0 (F.expLoc b₀) b₀ k ⊓ F.Nl).relIndex
        (RowForm.localTower F.e F.i0 (F.expLoc b₀) b₀ (k + 1) ⊓ F.Nl) =
      (A '' {c | lab (eΩ (F.e (c, F.i0))) = lab (eΩ (F.e (b₀, F.i0))) ∧ ol c = ol b₀}).ncard := by
  set I := (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).toColumnPre
  have hblk := colBlk_lab F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ lab hk hlab
  exact ⟨colRatio_labels I htr k A (fun c => lab (eΩ (F.e (c, F.i0)))) hA hblk,
    colLower_labels I k A (fun c => lab (eΩ (F.e (c, F.i0)))) ol hA hblk hol⟩

end Col

end GI.Impl
