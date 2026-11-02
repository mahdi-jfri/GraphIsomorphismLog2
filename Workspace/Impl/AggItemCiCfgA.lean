import Workspace.Impl.AggItemCiCfgG

/-!
# The configuration query: reading the answer

The `Solve` call of `cfgItem X Y` is on the pair structure `T` of the fibers (`cfgQuery`), with
the positions `Fin n × Fin n` numbered by `finProdFinEquiv`. Its canonical answer is `[]` or a
coset `x ⟨gs⟩` of permutations of `Fin (n·n)`. Every element of the answer acts diagonally
(`pairState_answer_diag`), so it is `itciD p` for a permutation `p` of `Fin n` that keeps the
pair colors from `X` to `Y`; `itciDec` reads `p` back.

* `itci_ans_read`: from a nonempty canonical answer, `x = itciD p₁` with `p₁` keeping the colors,
  and the decoded generators `gs.map itciDec` generate the automorphisms `itciAut X`.
* `itci_ans_empty`: from the empty answer, no permutation keeps the colors.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)
open scoped Pointwise

noncomputable section

variable {q : ℕ}

/-- The numbering of the pair positions. -/
abbrev itciPE (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv

/-- The diagonal action, on the numbered positions. -/
def itciD (n : ℕ) : Perm (Fin n) →* Perm (Fin (n * n)) :=
  (toFin (itciPE n)).toMonoidHom.comp (diagHom n)

theorem itciD_injective (n : ℕ) : Function.Injective (itciD n) := by
  intro a b h
  ext i
  have := congrArg (fun g : Perm (Fin (n * n)) => g (itciPE n (i, i))) h
  simp only [itciD, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    toFin, Equiv.permCongrHom, MulEquiv.coe_mk, Equiv.coe_fn_mk, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, diagHom_apply] at this
  have := congrArg Prod.fst ((itciPE n).injective this)
  simpa using congrArg Fin.val this

/-- The permutation of `Fin n` read from a diagonal one (`1` if it is not diagonal). -/
def itciDec {n : ℕ} (g : Perm (Fin (n * n))) : Perm (Fin n) :=
  if h : ∃ a, itciD n a = g then h.choose else 1

theorem itciDec_D {n : ℕ} (a : Perm (Fin n)) : itciDec (itciD n a) = a := by
  have h : ∃ b, itciD n b = itciD n a := ⟨a, rfl⟩
  rw [itciDec, dif_pos h]
  exact itciD_injective n h.choose_spec

/-- The value of a decoded permutation: the first coordinate of the image of `(i, i)`. -/
theorem itciD_apply {n : ℕ} (a : Perm (Fin n)) (i : Fin n) :
    ((itciPE n).symm (itciD n a (itciPE n (i, i)))).1 = a i := by
  simp [itciD, toFin, Equiv.permCongr_apply]

/-- The pair colors of the fiber, numbered (`pairCols`). -/
def itcqPC (X : PairCfg q) {n : ℕ} (h : X.fiber.card = n) : Fin n × Fin n → ℕ :=
  fun d => X.col (X.emb h d.1) (X.emb h d.2)

/-- The pair structure of the configuration query. -/
abbrev itcqPT (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) :
    State (Fin X.fiber.card × Fin X.fiber.card) ℕ :=
  pairState X.fiber.card (itcqPC X rfl) (itcqPC Y hc.symm)

theorem itci_cfgQuery_T {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
    {X Y : PairCfg L.q} (hc : X.fiber.card = Y.fiber.card) :
    (cfgQuery (P := P) X Y hc).T = itcqPT X Y hc := rfl

theorem itci_mem_T {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    (p : Perm (Fin X.fiber.card)) :
    diagHom _ p ∈ (itcqPT X Y hc).answer ↔ ItciKeeps X Y hc p :=
  mem_pairState_answer (x := itcqPC X rfl) (y := itcqPC Y hc.symm) p

theorem itci_keeps_aut {X Y : PairCfg q} {hc : X.fiber.card = Y.fiber.card}
    {p p' : Perm (Fin X.fiber.card)} (hp : ItciKeeps X Y hc p) (hp' : ItciKeeps X Y hc p') :
    p⁻¹ * p' ∈ itciAut X := by
  intro i k
  have h1 := hp ((p⁻¹ * p') i) ((p⁻¹ * p') k)
  simp only [Perm.mul_apply, Perm.apply_inv_self] at h1
  change X.col (X.emb rfl (p⁻¹ (p' i))) (X.emb rfl (p⁻¹ (p' k))) = _
  rw [← h1, hp']

theorem itci_keeps_mul {X Y : PairCfg q} {hc : X.fiber.card = Y.fiber.card}
    {p : Perm (Fin X.fiber.card)} (hp : ItciKeeps X Y hc p) {a : Perm (Fin X.fiber.card)}
    (ha : a ∈ itciAut X) : ItciKeeps X Y hc (p * a) := by
  intro i k
  change Y.col (Y.emb hc.symm (p (a i))) (Y.emb hc.symm (p (a k))) = _
  rw [hp]; exact ha i k

/-- The numbered answer: the image of the answer is the image of the colour-keeping maps. -/
theorem itci_img_T {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card) :
    toFin (itciPE X.fiber.card) '' (itcqPT X Y hc).answer =
      {g | ∃ p, ItciKeeps X Y hc p ∧ itciD _ p = g} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨p, rfl⟩ := pairState_answer_diag (x := itcqPC X rfl) (y := itcqPC Y hc.symm) hh
    exact ⟨p, (itci_mem_T hc p).1 hh, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨diagHom _ p, (itci_mem_T hc p).2 hp, rfl⟩

/-- **The empty answer**: no permutation keeps the colors. -/
theorem itci_ans_empty {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    (h : (itcqPT X Y hc).answer = ∅) (p : Perm (Fin X.fiber.card)) : ¬ ItciKeeps X Y hc p :=
  fun hp => by
    have := (itci_mem_T hc p).2 hp
    rw [h] at this
    exact this

/-- **A nonempty answer**: the representative is diagonal for a map that keeps the colors, and
the decoded generators generate the automorphisms. -/
theorem itci_ans_read {X Y : PairCfg q} (hc : X.fiber.card = Y.fiber.card)
    {x : Perm (Fin (X.fiber.card * X.fiber.card))} {gs : List (Perm (Fin (X.fiber.card *
      X.fiber.card)))}
    (h : toFin (itciPE X.fiber.card) '' (itcqPT X Y hc).answer = x • (gens gs : Set _)) :
    (∃ p₁, ItciKeeps X Y hc p₁ ∧ x = itciD _ p₁) ∧
      (∀ g ∈ gs, itciD _ (itciDec g) = g) ∧
      Subgroup.closure {a | a ∈ gs.map itciDec} = itciAut X := by
  classical
  rw [itci_img_T] at h
  have hx : x ∈ x • (gens gs : Set _) := ⟨1, Subgroup.one_mem _, mul_one x⟩
  rw [← h] at hx
  obtain ⟨p₁, hp₁, rfl⟩ := hx
  -- the group is the image of the automorphisms
  have hH : ∀ g, g ∈ gens gs ↔ ∃ a ∈ itciAut X, itciD _ a = g := by
    intro g
    constructor
    · intro hg
      have : itciD _ p₁ * g ∈ itciD _ p₁ • (gens gs : Set _) := ⟨g, hg, rfl⟩
      rw [← h] at this
      obtain ⟨p, hp, he⟩ := this
      refine ⟨p₁⁻¹ * p, itci_keeps_aut hp₁ hp, ?_⟩
      rw [map_mul, map_inv, he, inv_mul_cancel_left]
    · rintro ⟨a, ha, rfl⟩
      have : itciD _ (p₁ * a) ∈ itciD _ p₁ • (gens gs : Set _) := by
        rw [← h]; exact ⟨_, itci_keeps_mul hp₁ ha, rfl⟩
      obtain ⟨g, hg, he⟩ := this
      rw [map_mul] at he
      have := mul_left_cancel he
      rw [← this]; exact hg
  have hgD : ∀ g ∈ gs, itciD _ (itciDec g) = g := fun g hg => by
    obtain ⟨a, -, rfl⟩ := (hH g).1 (Subgroup.subset_closure hg)
    rw [itciDec_D]
  refine ⟨⟨p₁, hp₁, rfl⟩, hgD, ?_⟩
  apply Subgroup.map_injective (itciD_injective X.fiber.card)
  rw [MonoidHom.map_closure]
  have e1 : (itciD X.fiber.card) '' {a | a ∈ gs.map itciDec} = {g | g ∈ gs} := by
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨g', hg', rfl⟩, rfl⟩; rw [hgD g' hg']; exact hg'
    · intro hg; exact ⟨_, ⟨g, hg, rfl⟩, hgD g hg⟩
  rw [e1]
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro hg; obtain ⟨a, ha, he⟩ := (hH g).1 hg; exact ⟨a, ha, he⟩
  · rintro ⟨a, ha, rfl⟩; exact (hH _).2 ⟨a, ha, rfl⟩

end

end GI.Impl
