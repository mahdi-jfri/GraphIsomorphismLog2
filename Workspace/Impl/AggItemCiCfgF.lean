module

public import Workspace.Impl.AggItemCiCfgSk
public import Workspace.Impl.AggItemCiCfgD

@[expose] public section

/-!
# The configuration branch: its contract

`itcq_cfgSpec` proves `ItciCfgSpec` (the `cfgItem` branch of the pair part, Lemma A.12) from the
contracts of the start and step programs (`ItcqProgs`):
* the start (`itcq_stF_spec`) asks the pair structure `itcqPT X Y hc` when the fibers have the
  same size (`Canon` by `itcq_canon`, smaller by `itcq_lt` since `q² < N`), and returns the
  empty result otherwise (then `cfgItem X Y` is `.none`);
* the item relation `itcqRc Ki` holds the kept state `itcqKs X x₀ Y y₀ w` and an answer `u`;
* the step returns the empty result on an empty answer (`itcq_skF_emp`) and when the outer
  color classes of `X` and `Y` cannot be aligned (`itcq_skF_nal`, then `cfgQuery` reads
  nothing by `itcq_read_nal`), and the overcosets `itcqOs` of `itcq_item` otherwise
  (`itcq_sbF_spec`, `itcq_skF_ne`).
The bound `itcqXc` is a polynomial in the input weight and the kept bound (`itcqXc_pbu`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

/-! ### The scripts -/

section Scripts

variable {Ω C : Type} {S : State Ω C} {q : ℕ}

theorem itcq_script_pos (L : GiantLabels S) {X Y : PairCfg L.q}
    (hc : X.fiber.card = Y.fiber.card) :
    (cfgItem (P := P₀) X Y : AuxItem P₀ S L).script =
      Script.ask .solve (itcqPT X Y hc) (fun A => Script.done
        ⟨[], [(cfgQuery (P := P₀) X Y hc).read A].reduceOption.map
          (AuxItem.liftOver L X.autE)⟩) := by
  simp only [cfgItem, dif_pos hc]
  rfl

theorem itcq_script_neg (L : GiantLabels S) {X Y : PairCfg L.q}
    (hc : ¬ X.fiber.card = Y.fiber.card) :
    (cfgItem (P := P₀) X Y : AuxItem P₀ S L).script = Script.done ⟨[], []⟩ := by
  simp only [cfgItem, dif_neg hc]
  rfl

theorem itcq_read_empty (L : GiantLabels S) {X Y : PairCfg L.q}
    (hc : X.fiber.card = Y.fiber.card) :
    (cfgQuery (P := P₀) (S := S) (L := L) X Y hc).read ∅ = none := by
  unfold cfgQuery
  simp only [Set.mem_empty_iff_false, false_and, exists_false, dite_false]

variable {k : ℕ}

theorem itcq_sb_pair (e : Ω ≃ Fin k) {L : GiantLabels S} (X : PairCfg L.q) (x₀ : Fin L.q)
    (Y : PairCfg L.q) (y₀ : Fin L.q) (h : L.q ^ 5 ≤ S.N ^ 2) (ch : ItCfCh S L) :
    itCfSb e (.pair X x₀) (.pair Y y₀) ch = (cfgItem (P := P₀) X Y : AuxItem P₀ S L).script := by
  unfold itCfSb
  simp only [cfgOutItem, if_pos ((itci_rpow_iff _ _).2 h)]

end Scripts

/-! ### The program contracts and the relation -/

/-- **The contracts of the start and step programs** at `fs`, `fk`. -/
structure ItcqProgs (Pg : Program) (fs fk : ℕ) : Prop where
  st : ∀ {q : ℕ} (Kv tb w : Val) (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q)
    {W : ℕ}, (Val.list [Kv, tb, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w]).wt ≤ W →
    FunDet Pg fs (.list [Kv, tb, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w])
      (itcqStV X x₀ Y y₀ w) (itcqStC W)
  emp : ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val) {M : ℕ},
    (Val.list [itcqKs X x₀ Y y₀ w, .list []]).wt ≤ M →
    FunDet Pg fk (.list [itcqKs X x₀ Y y₀ w, .list []]) (itcqEmp w) (itcqSkC M)
  ne : ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val)
    (p₁ : Perm (Fin X.fiber.card)) (gs : List (Perm (Fin (X.fiber.card * X.fiber.card)))),
    (∀ g ∈ gs, itciD _ (itciDec g) = g) → ItciAl X Y → ∀ {M : ℕ}, q + 1 ≤ M →
    (Val.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]]).wt ≤ M →
    FunDet Pg fk (.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]])
      (itciRes (itciOV (itcqOs X (itciExt X Y p₁) (itcqSg X gs))) w) (itcqSkC M)
  nal : ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w x G : Val),
    ¬ ItciAl X Y → ∀ {M : ℕ}, (Val.list [itcqKs X x₀ Y y₀ w, .list [x, G]]).wt ≤ M →
    FunDet Pg fk (.list [itcqKs X x₀ Y y₀ w, .list [x, G]]) (itcqEmp w) (itcqSkC M)

/-- **The item relation of the configuration branch**: the item state is `[kst, u]` with the
kept state of two pair objects with fibers of the same size, an answer `u` of the pair
structure, a kept value `w` of `E`, and the scripts of `E` finished by the read answer. -/
def itcqRc (Ki : ItciKiT) : ItciRiT := fun e c S L K b oX oY ist E sb _ =>
  ∃ (X : PairCfg L.q) (x₀ : Fin L.q) (Y : PairCfg L.q) (y₀ : Fin L.q) (w u : Val)
    (hc : X.fiber.card = Y.fiber.card),
    oX = .pair X x₀ ∧ oY = .pair Y y₀ ∧ ItCfObjOf K b oX oY ∧
    ist = .list [itcqKs X x₀ Y y₀ w, u] ∧ AnsC (itciPE X.fiber.card) u (itcqPT X Y hc).answer ∧
    Ki e c S L K w E ∧ ∀ ch ∈ E, sb ch = Script.done ⟨[],
      [(cfgQuery (P := P₀) (S := S) (L := L.toGiantLabels) X Y hc).read
        (itcqPT X Y hc).answer].reduceOption.map (AuxItem.liftOver L.toGiantLabels X.autE)⟩

/-! ### The bounds -/

/-- The weight bound of the start input. -/
def itcqMs (W B : ℕ) : ℕ := 2 * (itSVB W + 5 * (2 * W + 4) ^ 2 + 3 * B) + 20

/-- The weight bound of an item state. -/
def itcqMk (W B : ℕ) : ℕ := 20 * B + 2000 * ((2 * W + 3) ^ 2 + 1) ^ 6 + 100

/-- **The bound of the configuration branch.** -/
def itcqXc (W B : ℕ) : ℕ := itcqStC (itcqMs W B) + itcqSkC (itcqMk W B) + itcqMk W B + 100

theorem itcq_ans_wt {n : ℕ} {u : Val} {A : Set (Perm (Fin n × Fin n))} {T : ℕ} (hn : n + 1 ≤ T)
    (h : AnsC (itciPE n) u A) : u.wt ≤ 700 * (T ^ 2 + 1) ^ 6 := by
  have hT1 : 1 ≤ (T ^ 2 + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hnn : n * n + 1 ≤ T ^ 2 + 1 := by
    have := Nat.mul_le_mul (show n ≤ T by omega) (show n ≤ T by omega)
    rw [sq]; omega
  have h2 : (n * n + 1) ^ 2 ≤ (T ^ 2 + 1) ^ 6 :=
    (Nat.pow_le_pow_left hnn 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h6 : (n * n + 1) ^ 6 ≤ (T ^ 2 + 1) ^ 6 := Nat.pow_le_pow_left hnn 6
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hl, -⟩
  · have : (Val.list []).wt ≤ 4 := by
      have := wt_list_le ([] : List Val)
      simp only [List.map_nil, List.sum_nil, List.length_nil] at this; omega
    omega
  · have h1 := wt_encPerm_le x
    have hg := wt_encGroup_sq (n := n * n) (kept := gs) hl
    have := wt_list2_le (encPerm x) (encGroup gs)
    omega

theorem itcq_ist_wt {q : ℕ} {X Y : PairCfg q} {x₀ y₀ : Fin q} {w u : Val} {B T : ℕ}
    (hq : q + 1 ≤ T) (hw : w.wt ≤ B) (hX : (itCfOutV (.pair X x₀)).wt ≤ B)
    (hY : (itCfOutV (.pair Y y₀)).wt ≤ B) (hu : u.wt ≤ 700 * (T ^ 2 + 1) ^ 6) :
    (Val.list [itcqKs X x₀ Y y₀ w, u]).wt ≤ 20 * B + 2000 * (T ^ 2 + 1) ^ 6 + 100 := by
  have hcX : (rcCertIn X x₀).wt < (itCfOutV (.pair X x₀)).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hcY : (rcCertIn Y y₀).wt < (itCfOutV (.pair Y y₀)).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hfX : (itcqFV X).wt ≤ 5 * (q + 1) ^ 2 := by
    refine wt_natList_le_sq (fun x hx => ?_) ?_
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
    · simp only [List.length_map, itciFl_length]
      exact Finset.card_le_univ _ |>.trans (by simp)
  have hfY : (itcqFV Y).wt ≤ 5 * (q + 1) ^ 2 := by
    refine wt_natList_le_sq (fun x hx => ?_) ?_
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
    · simp only [List.length_map, itciFl_length]
      exact Finset.card_le_univ _ |>.trans (by simp)
  have hq2 : (q + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hq 2
  have hT : T ^ 2 ≤ (T ^ 2 + 1) ^ 6 := (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
  have hk := wt_list_le [w, rcCertIn X x₀, rcCertIn Y y₀, itcqFV X, itcqFV Y]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at hk
  have := wt_list2_le (itcqKs X x₀ Y y₀ w) u
  unfold itcqKs at this ⊢
  omega

end GI.Impl
