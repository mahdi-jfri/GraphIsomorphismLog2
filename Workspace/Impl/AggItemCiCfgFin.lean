import Workspace.Impl.AggItemCiCfgF
import Workspace.Impl.AggItemCiPair

/-!
# The configuration branch: `ItciCfgSpec`

`itcq_cfgSpec`: from the program contracts `ItcqProgs`, the configuration branch satisfies
`ItciCfgSpec` with the item relation `itcqRc` and the bound `itcqXc`. `itcqXc_pbu` gives the
polynomial bound that `itciXp_pbu` needs.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

/-- The pieces-and-overcosets value weighs less than the result. -/
theorem itcq_out_wt (b w : Val) : (Val.list [.list [], b]).wt < (itciRes b w).wt := by
  have h1 : (Val.list [.list [], b]).wt ≤ (Val.list [.list [], b, w]).wt :=
    wt_list_mono ⟨[w], rfl⟩
  have h2 : (Val.list [.list [], b, w]).wt < (itciRes b w).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  omega

theorem itcq_emp_wt : (Val.list [.list [], .list []]).wt ≤ 30 := by
  have h0 : (Val.list []).wt ≤ 4 := by
    have := wt_list_le ([] : List Val)
    simp only [List.map_nil, List.sum_nil, List.length_nil] at this; omega
  have := wt_list2_le (.list []) (.list [])
  omega

variable {I : Iface} {Pg : Program}

set_option maxHeartbeats 1000000 in
/-- **The configuration branch satisfies its contract** (Lemma A.12, with the overcosets of
`itcq_item`). -/
theorem itcq_cfgSpec {F : Funs} {fs fk : ℕ} (hP : ItcqProgs Pg fs fk) :
    ItciCfgSpec I Pg F fs fk itcqXc := by
  classical
  refine ⟨itcqRc, fun Ki Bk {Ω C k} e c S sv lv L hcall K hK _ hne hKw hobj => ?_⟩
  obtain ⟨hkq, hκ, -, -, -, hκq⟩ := itS_size I Pg F hcall
  have hv := itS_vW I Pg F hcall hK
  generalize I.inW .giant S = W₀ at hkq hκ hv ⊢
  have hX100 : 100 ≤ itcqXc W₀ Bk := by unfold itcqXc; omega
  have hMk : itcqMk W₀ Bk ≤ itcqXc W₀ Bk := by unfold itcqXc; omega
  have hSk : itcqSkC (itcqMk W₀ Bk) ≤ itcqXc W₀ Bk := by unfold itcqXc; omega
  have hSt : itcqStC (itcqMs W₀ Bk) ≤ itcqXc W₀ Bk := by unfold itcqXc; omega
  have hqT : L.q + 1 ≤ 2 * W₀ + 3 := by omega
  have hnq : ∀ X : PairCfg L.q, X.fiber.card ≤ L.q := fun X => by
    have := X.fiber.card_le_univ; simpa using this
  -- the weight of an item state
  have hist : ∀ (b : Fin (P₀.κ + 1) → Fin L.q) (X : PairCfg L.q) (x₀ : Fin L.q) (Y : PairCfg L.q)
      (y₀ : Fin L.q) (w u : Val) (E : Set (ItCfCh S L.toGiantLabels))
      (hc : X.fiber.card = Y.fiber.card), ItCfObjOf K b (.pair X x₀) (.pair Y y₀) →
      Ki e c S L K w E → AnsC (itciPE X.fiber.card) u (itcqPT X Y hc).answer →
      (Val.list [itcqKs X x₀ Y y₀ w, u]).wt ≤ itcqMk W₀ Bk := by
    intro b X x₀ Y y₀ w u E hc hob hKi hu
    have := itcq_ist_wt (T := 2 * W₀ + 3) hqT (hKw w E hKi) ((hobj b _ _ hob).1 X x₀ rfl)
      ((hobj b _ _ hob).2 Y y₀ rfl) (itcq_ans_wt (by have := hnq X; omega) hu)
    unfold itcqMk; omega
  refine ⟨?_, ?_, ?_⟩
  · -- the start
    intro b X x₀ Y y₀ w E hob hKi hq5
    have hs := it_wt_src b (W := 2 * W₀ + 3) (by omega) hκ
    have hs' : (stTv b).wt ≤ 5 * (2 * W₀ + 4) ^ 2 := hs
    have hoX := (hobj b _ _ hob).1 X x₀ rfl
    have hoY := (hobj b _ _ hob).2 Y y₀ rfl
    have hw := hKw w E hKi
    have hin := wt_list_le [K.v, stTv b, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hin
    have hst := hP.st K.v (stTv b) w X x₀ Y y₀ (W := itcqMs W₀ Bk) (by unfold itcqMs; omega)
    refine FunAll.mono hst fun w' cost ⟨hw', hc'⟩ => ⟨hc'.trans hSt, ?_⟩
    subst hw'
    by_cases hc : X.fiber.card = Y.fiber.card
    · rw [itcqStV, dif_pos hc]
      have hlt : X.fiber.card * X.fiber.card < S.N :=
        lt_of_le_of_lt (Nat.mul_le_mul (hnq X) (hnq X)) (itcq_sq_lt hq5 (by omega))
      refine Or.inr ⟨by omega, .solve, _, _, itcqPT X Y hc, _, itciPE X.fiber.card,
        itcqCode (itcqCL X Y hc), itcqArg X Y hc, itcqKs X x₀ Y y₀ w, E,
        fun _ A => Script.done ⟨[], [(cfgQuery (P := P₀) (S := S) (L := L.toGiantLabels) X Y
          hc).read A].reduceOption.map (AuxItem.liftOver L.toGiantLabels X.autE)⟩,
        subset_rfl, hne w E hKi, itcqCode_injective _, Or.inl rfl, rfl, itcq_canon X Y hc,
        trivial, itcq_lt X Y hc hlt, fun ch _ => ?_, fun u hu =>
          ⟨X, x₀, Y, y₀, w, u, hc, rfl, rfl, hob, rfl, hu, hKi, fun ch _ => rfl⟩⟩
      rw [itcq_sb_pair e X x₀ Y y₀ hq5 ch, itcq_script_pos L.toGiantLabels hc]
    · rw [itcqStV, dif_neg hc]
      refine Or.inl ⟨⟨[], []⟩, [], [], w, E, rfl, subset_rfl, fun ch _ => ?_, hKi,
        ⟨List.Forall₂.nil, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _),
          fun o ho => absurd ho List.not_mem_nil⟩, ?_⟩
      · rw [itcq_sb_pair e X x₀ Y y₀ hq5 ch, itcq_script_neg L.toGiantLabels hc]
      · have := itcq_emp_wt
        exact this.trans (by omega)
  · -- the weight of an item state
    rintro b oX oY ist E sb f ⟨X, x₀, Y, y₀, w, u, hc, rfl, rfl, hob, rfl, hu, hKi, -⟩
    exact (hist b X x₀ Y y₀ w u E hc hob hKi hu).trans hMk
  · -- the step
    rintro b oX oY ist E sb f ⟨X, x₀, Y, y₀, w, u, hc, rfl, rfl, hob, rfl, hu, hKi, hsb⟩
    have hwt := hist b X x₀ Y y₀ w u E hc hob hKi hu
    rcases hu with ⟨rfl, hA⟩ | ⟨x, gs, rfl, -, hA⟩
    · have he := hP.emp X x₀ Y y₀ w hwt
      refine FunAll.mono he fun w' cost ⟨hw', hc'⟩ => ⟨hc'.trans hSk, ?_⟩
      subst hw'
      refine Or.inl ⟨⟨[], []⟩, [], [], w, E, rfl, subset_rfl, fun ch hch => ?_, hKi,
        ⟨List.Forall₂.nil, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _),
          fun o ho => absurd ho List.not_mem_nil⟩, ?_⟩
      · rw [hsb ch hch, hA]
        erw [itcq_read_empty L.toGiantLabels hc]
        rfl
      · have := itcq_emp_wt
        exact this.trans (by omega)
    · by_cases hal : ItciAl X Y
      swap
      · -- the outer classes cannot be aligned: the query reads nothing
        have he := hP.nal X x₀ Y y₀ w (encPerm x) (encGroup gs) hal hwt
        refine FunAll.mono he fun w' cost ⟨hw', hc'⟩ => ⟨hc'.trans hSk, ?_⟩
        subst hw'
        refine Or.inl ⟨⟨[], []⟩, [], [], w, E, rfl, subset_rfl, fun ch hch => ?_, hKi,
          ⟨List.Forall₂.nil, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _),
            fun o ho => absurd ho List.not_mem_nil⟩, ?_⟩
        · rw [hsb ch hch]
          erw [itcq_read_nal L.toGiantLabels hc hal]
          rfl
        · have := itcq_emp_wt
          exact this.trans (by omega)
      obtain ⟨⟨p₁, hp₁, rfl⟩, hgD, hcl⟩ := itci_ans_read hc hA
      have hS : gens (itcqSg X gs) = itciMG X := itcq_mg_gens X (itcq_closure_one hcl)
      obtain ⟨-, ovs, hovs, hF⟩ := itcq_item L.toGiantLabels hc hp₁ hal hS
      have hn := hP.ne X x₀ Y y₀ w p₁ gs hgD hal (M := itcqMk W₀ Bk) (by
        have h1 : 2 * W₀ + 3 ≤ (2 * W₀ + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
        have h2 : (2 * W₀ + 3) ^ 2 + 1 ≤ ((2 * W₀ + 3) ^ 2 + 1) ^ 6 :=
          Nat.le_self_pow (by norm_num) _
        unfold itcqMk; omega) hwt
      have hout := hn.wt_lt
      refine FunAll.mono hn fun w' cost ⟨hw', hc'⟩ => ⟨hc'.trans hSk, ?_⟩
      subst hw'
      refine Or.inl ⟨⟨[], ovs⟩, [], itcqOs X (itciExt X Y p₁) (itcqSg X gs), w, E, rfl,
        subset_rfl, fun ch hch => ?_, hKi,
        ⟨hF, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _), itcqOs_gens hS⟩, ?_⟩
      · rw [hsb ch hch, hovs]
      · have := itcq_out_wt (itciOV (itcqOs X (itciExt X Y p₁) (itcqSg X gs))) w
        exact (Nat.le_of_lt this).trans (hout.le.trans hSk)

/-! ### The bound is polynomial -/

/-- Substituting a polynomial for the second argument keeps a uniform bound. -/
theorem itcq_pbu_sub {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ} (hf : PBU fun _ W B => f W B)
    (hg : PBU fun _ W _ => g W) : PBU fun _ W _ => f W (g W) := by
  obtain ⟨C, D, h⟩ := hf
  refine (PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.add PBU.W hg) PBU.k) 2) D)).mono ?_
  intro k W B
  exact h k W (g W)

theorem itcqXc_pbu2 : PBU fun _ W B => itcqXc W B := by
  simp only [itcqXc, itcqStC, itcqSkC, itcqSbC, itcqOuC, itcqMs, itcqMk, itSVB, cmOutB, cmPb,
    cmNb, itcqFlC, itcqArgC, itcqSA, itcqSV, itcqAV, itcqDsC, itcqCsC, itcqAlC, itcqCoC]
  norm_poly

/-- **The bound of the configuration branch is polynomial**, in the form `itciXp_pbu` needs. -/
theorem itcqXc_pbu {Xs : ℕ → ℕ} (hs : PBU fun _ W _ => Xs W) :
    PBU fun _ W _ => itcqXc W (itciBk Xs W) := by
  refine itcq_pbu_sub itcqXc_pbu2 ?_
  have ho : PBU fun _ W _ => itciOW W := by
    simp only [itciOW, itCfObjB]
    norm_poly
  exact PBU.add hs ho

end GI.Impl
