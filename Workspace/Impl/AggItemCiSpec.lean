import Workspace.Impl.AggItemCiDisp
import Workspace.Impl.AggItemOKC1

/-!
# Cases 2b and 3: the item stage

`itci_itemSpec`: the contract `ItCfItemSpec` of the item stage, from the contract of its pair
part (`ItciPairSpec`), the colored-partition program (`ItciOk`) and the start program `itciDF`.
The init and step programs are those of the pair part. The start program
* for two partitions: they are vertex-class partitions (`itci_objOf_part`), and the overcosets
  of the program are those of the model's item `objItem` (`itci_classPart`);
* for two pair configurations: calls the start of the pair part;
* otherwise: the model has no item (`itci_sb_none`), and the program returns the empty result.

The bound `itciXt Xp` is polynomial when `Xp` is (`itciXt_pbu`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

/-- The weights of the start program apart from the pair part, in the input weight `W₀`. -/
def itciWc (W₀ : ℕ) : ℕ :=
  2 * (itSVB W₀ + 5 * (2 * W₀ + 3 + 1) ^ 2 + 2 * itciVB (2 * W₀ + 3) + 18) + 9 +
    800 * (2 * W₀ + 3 + 1) ^ 3 + 4 * itciMB (2 * W₀ + 3) + 100

/-- The weight bound of the start program, with the pair bound `Bp`. -/
def itciWd (Bp W₀ : ℕ) : ℕ := itciWc W₀ + 10 * Bp

/-- The cost bound of a branch of the start program. -/
def itciBd (Bp W₀ : ℕ) : ℕ :=
  2 * Bp + 40 * (itciWd Bp W₀ + 1) + itciFC (itciMB (2 * W₀ + 3)) + 10

/-- **The bound of the item stage**, with the pair bound `Xp`. -/
def itciXt (Xp : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  50 * (itciWd (Xp W₀) W₀ + 1) + 8 * itciBd (Xp W₀) W₀ + 7

variable (I : Iface) (Pg : Program)

set_option maxHeartbeats 4000000 in
/-- **The item stage of Cases 2b and 3**, from its pair part. -/
theorem itci_itemSpec {F : Funs} {fi fs fq fk : ℕ} {Ii : ItciIdx} {Xp : ℕ → ℕ}
    (hP : ItciPairSpec I Pg F fi fq fk Xp) (hI : ItciOk Pg Ii)
    (hf : Pg.funs[fs]? = some (itciDF Ii.f fq)) :
    ItCfItemSpec I Pg F fi fs fk (itciXt Xp) := by
  classical
  obtain ⟨R, hR⟩ := hP
  refine ⟨itciR R, fun {Ω C k} e c S sv lv L hc K hK hcase => ?_⟩
  have pa := hR e c S sv lv L hc K hK hcase
  obtain ⟨hkq, hκ, hpow, -, -, -⟩ := itS_size I Pg F hc
  have hv := itS_vW I Pg F hc hK
  generalize I.inW .giant S = W₀ at pa hkq hκ hpow hv ⊢
  have hBpB : Xp W₀ ≤ itciXt Xp W₀ := by unfold itciXt itciBd; omega
  refine ⟨pa.init.mono fun w cost ⟨E, h1, h2⟩ => ⟨E, h1, h2.trans hBpB⟩, pa.ne,
    fun w E h => (pa.wtK w E h).trans hBpB, ?_, ?_, ?_⟩
  rotate_left
  · rintro b oX oY ist E sb f ⟨f', -, h⟩
    exact (pa.wtR _ _ _ _ _ _ _ h).trans hBpB
  · rintro b oX oY ist E sb f ⟨f', hf', h⟩
    exact (pa.step _ _ _ _ _ _ _ h).mono fun w cost ⟨h1, h2⟩ =>
      ⟨h1.trans hBpB, itci_post_mono h2 hf' hBpB⟩
  -- the start
  intro b oX oY w E hob hKi
  have htb : (stTv b).wt ≤ 5 * (2 * W₀ + 3 + 1) ^ 2 := it_wt_src b (by omega) hκ
  have hw := pa.wtK w E hKi
  obtain ⟨hpX, hpY⟩ := itci_objOf_sides hK hcase hob
  obtain ⟨hoX, hoY⟩ := pa.objW b oX oY hob
  have hVX : (itCfOutV oX).wt ≤ itciVB (2 * W₀ + 3) + (Xp W₀) + 9 := by
    cases oX with
    | none => have := itci_none_wt (q := L.q); omega
    | part z =>
      obtain ⟨f, rfl, hf⟩ := hpX z rfl
      have := itci_partV_wt hf (by omega) hpow; omega
    | pair X x₀ => have := hoX X x₀ rfl; omega
  have hVY : (itCfOutV oY).wt ≤ itciVB (2 * W₀ + 3) + (Xp W₀) + 9 := by
    cases oY with
    | none => have := itci_none_wt (q := L.q); omega
    | part z =>
      obtain ⟨f, rfl, hf⟩ := hpY z rfl
      have := itci_partV_wt hf (by omega) hpow; omega
    | pair Y y₀ => have := hoY Y y₀ rfl; omega
  have hin0 : (itciIn K.v (stTv b) (itCfOutV oX) (itCfOutV oY) w).wt ≤ itciWd (Xp W₀) W₀ := by
    have := wt_list_le [K.v, stTv b, itCfOutV oX, itCfOutV oY, w]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    unfold itciIn; unfold itciWd itciWc; omega
  have h6 : 6 ≤ itciWd (Xp W₀) W₀ := by unfold itciWd itciWc; omega
  have hq3 : (L.q + 1) ^ 3 ≤ (2 * W₀ + 3 + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  obtain ⟨tX, xs, hxX, hX2, hX1⟩ := itci_kind oX
  obtain ⟨tY, ys, hyY, hY2, hY1⟩ := itci_kind oY
  have hin := hin0
  rw [hxX, hyY] at hin
  have key := itci_df_spec (P := Pg) (fp := Ii.f) (fq := fq) (Bd := itciBd (Xp W₀) W₀)
    (Pst := ItCfIPost (itciR R) e c S L K b oX oY E (itCfSb e oX oY) (itciXt Xp W₀) (itciXt Xp W₀)) hin h6
    (fun h2 h3 => by
      obtain ⟨X, x₀, rfl⟩ := hX2.1 h2
      obtain ⟨Y, y₀, rfl⟩ := hY2.1 h3
      rw [← hxX, ← hyY]
      refine EvalAll.call_funAll (StDC.var' (W := itciWd (Xp W₀) W₀) rfl hin0) fun v ca ⟨hv, hca⟩ => ?_
      subst hv
      refine (pa.start b X x₀ Y y₀ w E hob hKi).wt_lt.mono fun w' cb ⟨⟨h1, h2⟩, h3⟩ =>
        ⟨itci_post_mono h2 hBpB hBpB, ?_⟩
      unfold itciBd; omega)
    (fun h1 h3 => by
      obtain ⟨zX, rfl⟩ := hX1.1 h1
      obtain ⟨zY, rfl⟩ := hY1.1 h3
      obtain ⟨fX, rfl, hfX⟩ := hpX zX rfl
      obtain ⟨fY, rfl, hfY⟩ := hpY zY rfl
      simp only [itCfOutV, Val.list.injEq, List.cons.injEq] at hxX hyY
      obtain ⟨-, rfl⟩ := hxX
      obtain ⟨-, rfl⟩ := hyY
      have hMX := itci_col_wt hfX (by omega) hpow
      have hMY := itci_col_wt hfY (by omega) hpow
      obtain ⟨ovs, hs, hfa, hg⟩ := itci_classPart (P := P₀) L.toGiantLabels fX fY
      have hOV := itciOV_wt (itciOs_props fX fY (evenStab (q := L.q) (classPart fX))).1
        (itciOs_props fX fY (evenStab (q := L.q) (classPart fX))).2
      set os := itciOs fX fY (itciOt fX) (evenStab (q := L.q) (classPart fX))
      have hpg := itci_prog hI fX fY hMX hMY (evenStab (q := L.q) (classPart fX))
      have ha : (Val.list [encFun fX, encFun fY]).wt ≤ itciWd (Xp W₀) W₀ := by
        have := wt_list2_le (encFun fX) (encFun fY)
        unfold itciWd itciWc; omega
      have hr : (itciRes (itciOV os) w).wt ≤ itciWd (Xp W₀) W₀ := by
        have h1 := wt_list2_le (.nat 0) (.list [.list [], itciOV os, w])
        have h2 := wt_list3_le (.list []) (itciOV os) w
        have := wt_nat_le 0
        unfold itciRes; unfold itciWd itciWc; simp only [wt_list_nil] at h2; omega
      refine itci_of_det (itci_part_spec hin rfl rfl rfl rfl hpg ha hr h6) ?_ ?_
      · refine Or.inl ⟨⟨[], ovs⟩, [], os, w, E, rfl, subset_rfl, fun ch _ => ?_, hKi,
          ⟨hfa, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _), hg⟩, ?_⟩
        · rw [itci_sb_part]; exact hs
        · have := wt_list2_le (.list []) (itciOV os)
          show (Val.list [.list [], itciOV os]).wt ≤ itciXt Xp W₀
          unfold itciXt itciBd itciWd itciWc; simp only [wt_list_nil] at this
          omega
      · unfold itciBd; omega)
    (fun h2 h1 => by
      have h2' : ¬ ((∃ X x₀, oX = .pair X x₀) ∧ ∃ Y y₀, oY = .pair Y y₀) :=
        fun h => h2 ⟨hX2.2 h.1, hY2.2 h.2⟩
      have h1' : ¬ ((∃ z, oX = .part z) ∧ ∃ z, oY = .part z) :=
        fun h => h1 ⟨hX1.2 h.1, hY1.2 h.2⟩
      have hr : (itciRes (.list []) w).wt ≤ itciWd (Xp W₀) W₀ := by
        have h1 := wt_list2_le (.nat 0) (.list [.list [], .list [], w])
        have h2 := wt_list3_le (.list []) (.list []) w
        have := wt_nat_le 0
        unfold itciRes; unfold itciWd itciWc; simp only [wt_list_nil] at h2; omega
      refine itci_of_det (itci_emp_spec hin hr h6) ?_ ?_
      · refine Or.inl ⟨⟨[], []⟩, [], [], w, E, rfl, subset_rfl,
          fun ch _ => itci_sb_none e h2' h1' ch, hKi,
          ⟨List.Forall₂.nil, rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _),
            fun o ho => absurd ho (List.not_mem_nil)⟩, ?_⟩
        show (Val.list [.list [], .list []]).wt ≤ itciXt Xp W₀
        have := wt_list2_le (.list []) (.list [])
        simp only [wt_list_nil] at this
        unfold itciXt; omega
      · unfold itciBd; omega)
  rw [← hxX, ← hyY] at key
  refine FunAll.intro hf (key.mono fun w' cost ⟨hp, hc'⟩ => ⟨?_, hp⟩)
  unfold itciXt; omega

/-- **The bound of the item stage is polynomial** when the pair bound is. -/
theorem itciXt_pbu {Xp : ℕ → ℕ} (h : PBU fun _ W _ => Xp W) :
    PBU fun _ W _ => itciXt Xp W := by
  have hc : PBU fun _ W _ => 50 * (itciWc W + 1) + 8 * (40 * (itciWc W + 1) +
      itciFC (itciMB (2 * W + 3)) + 10) + 7 := by
    simp only [itciWc, itciVB, itciMB, itciFC, itSVB, cmOutB, cmPb, cmNb]
    norm_poly
  refine PBU.mono (PBU.add hc (PBU.smul 4016 h)) fun _ W _ => ?_
  unfold itciXt itciBd itciWd
  omega

end GI.Impl
