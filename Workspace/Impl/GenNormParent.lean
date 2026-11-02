import Workspace.Impl.GenNormGraph
import Workspace.Impl.GenExposeCand

/-!
# Attaching Cameron point images to position generators

The exposed class numbers and their ordered representatives compute each generator's block
permutation. The incidence loops then recover its point permutation. The same program can
be used after the normalized position generators are cut down to a canonical list.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- The generator's block action in exactly the exposed quotient coordinates. -/
theorem normActList_eq {Ω C : Type} {S : State Ω C} {n : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) {num : Fin n → ℕ} {reps : List ℕ}
    (hd : reps.length = Q.d) (hb : ∀ v ∈ S.dom, (Q.blk v : ℕ) = num (en v))
    (hr : ∀ t (ht : t < reps.length), ∃ h : reps[t] < n, en.symm ⟨_, h⟩ ∈ S.dom ∧
      num ⟨_, h⟩ = t)
    (a : Perm (Fin n)) (ha : (toFin en).symm a ∈ S.G) :
    natList (actList num reps a) = encPerm (Q.ρ ⟨(toFin en).symm a, ha⟩) := by
  have hg : ∀ g : Perm (Fin n), (toFin en).symm g ∈ S.G → ∀ r : Fin n,
      en.symm r ∈ S.dom → ∀ hlt : num r < Q.d,
        ((homFin en Q.ρ g) ⟨num r, hlt⟩ : ℕ) = num (g r) := by
    intro g hg r hR hlt
    have h1 : (⟨num r, hlt⟩ : Fin Q.d) = Q.blk (en.symm r) :=
      Fin.ext (by rw [hb _ hR, Equiv.apply_symm_apply])
    have hgr : (toFin en).symm g (en.symm r) = en.symm (g r) := by
      simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]
    unfold homFin
    rw [dif_pos hg, h1, ← Q.equivariant ⟨_, hg⟩ _ hR]
    rw [hgr, hb _ (by rw [← hgr]; exact (S.dom_inv _ hg _).2 hR), Equiv.apply_symm_apply]
  have h := actList_eq hd hr hg ha
  simpa only [homFin, dif_pos ha] using h

/-- On `[[num,reps,E,blockIds,pointIds],a]`, attach the point action of `a`. -/
def normParentF (act recover : ℕ) : Expr :=
  .letE (.call act (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1)))
    (mk2 (arg 1) (.call recover (mk2
      (Expr.mkList [.get (arg 0) (.nat 2), .var 1, .get (arg 0) (.nat 3),
        .get (arg 0) (.nat 4)]) (.get (arg 0) (.nat 4)))))

private theorem normParentGet {Pg : Program} {fields : List Val} {entry : Val} {j : ℕ} {v : Val}
    (hj : fields[j]? = some v) {rest : List Val} :
    Det Pg (.list [.list fields, entry] :: rest) (.get (arg 0) (.nat j)) v
      (5 * (Val.list [.list fields, entry]).wt + j + 20) := by
  have hc : (Val.list fields).wt < (Val.list [.list fields, entry]).wt := wt_le_wt_list (by simp)
  have hv : v.wt < (Val.list fields).wt := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact wt_getElem_lt _ _ h
  exact (Det.get' (Det.arg' (j := 0) rfl) (Det.nat j) hj).mono (by omega)

set_option maxHeartbeats 2000000 in
/-- Attaching a point image is polynomial in the prepared context and the two degrees. -/
theorem normParent_spec {Pg : Program} {f act bg recover point filter cand all test mem n m k : ℕ}
    (hf : Pg.funs[f]? = some (normParentF act recover))
    (hact : Pg.funs[act]? = some (actF bg)) (hgather : Pg.HasAt bg (gatherFuns bg))
    (hmap : Pg.HasAt recover (mapFuns recover point))
    (hpoint : Pg.funs[point]? = some (normPointF filter))
    (hfilter : Pg.HasAt filter (filterFuns filter cand))
    (hcand : Pg.funs[cand]? = some (normCandidateF all))
    (hall : Pg.HasAt all (allFuns all test))
    (htest : Pg.funs[test]? = some (normIncTestF mem)) (hmem : Pg.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (num : Fin n → ℕ) (reps : List ℕ) (hnum : ∀ i, num i ≤ n)
    (hreps : ∀ r ∈ reps, r < n) (hd : reps.length = Q.d)
    (hb : ∀ v ∈ S.dom, (Q.blk v : ℕ) = num (en v))
    (hr : ∀ t (ht : t < reps.length), ∃ h : reps[t] < n, en.symm ⟨_, h⟩ ∈ S.dom ∧ num ⟨_, h⟩ = t)
    (a : Perm (Fin n)) (ha : (toFin en).symm a ∈ S.G) :
    FunDet Pg f (.list [.list [encFun num, natList reps, encKSetTuples e,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], encPerm a])
      (.list [encPerm a, encPerm (Q.permHom e hS (Q.ρ.rangeRestrict ⟨_, ha⟩))])
      (10 ^ 28 * ((Val.list [.list [encFun num, natList reps, encKSetTuples e,
        encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], encPerm a]).wt + n + m + 20) ^ 12) := by
  let fields := [encFun num, natList reps, encKSetTuples e,
    encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]
  let ctx := Val.list fields
  let inp := Val.list [ctx, encPerm a]
  let Z := inp.wt + n + m + 20
  let x : Q.ρ.range := Q.ρ.rangeRestrict ⟨(toFin en).symm a, ha⟩
  let rc := Val.list [encKSetTuples e, encPerm x.1, encPerm (1 : Perm (Fin Q.d)),
    encPerm (1 : Perm (Fin m))]
  have hZ20 : 20 ≤ Z := by dsimp only [Z]; omega
  have hnZ : n + 1 ≤ Z := by dsimp only [Z]; omega
  have hmZ : m + 1 ≤ Z := by dsimp only [Z]; omega
  have hdN := Q.d_le_card en
  have hdZ : Q.d + 1 ≤ Z := by omega
  have wc : ctx.wt < inp.wt := wt_le_wt_list (by simp)
  have wfields : ∀ v ∈ fields, v.wt ≤ Z := by
    intro v hv
    have h : v.wt < ctx.wt := wt_le_wt_list hv
    dsimp only [Z]
    omega
  have wn : (encFun num).wt ≤ Z := wfields _ (by simp [fields])
  have wr : (natList reps).wt ≤ Z := wfields _ (by simp [fields])
  have wE : (encKSetTuples e).wt ≤ Z := wfields _ (by simp [fields])
  have wd : (encPerm (1 : Perm (Fin Q.d))).wt ≤ Z := wfields _ (by simp [fields])
  have wm : (encPerm (1 : Perm (Fin m))).wt ≤ Z := wfields _ (by simp [fields])
  have wx : (encPerm x.1).wt ≤ 4 * Z ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdZ 2))
  have h12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have rsize : normRecoverSize e x.1 ≤ 10 * Z ^ 2 := by
    unfold normRecoverSize
    dsimp only [Z] at hnZ hmZ hdZ
    omega
  have hrec := normRecover_spec hmap hpoint hfilter hcand hall htest hmem Q e hS x rsize
  have hblock := actF_det hact hgather num reps hnum hreps (by omega) le_rfl a
  rw [normActList_eq en Q hd hb hr a ha] at hblock
  have d0 : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 0)) (encFun num) (5 * inp.wt + 20) :=
    fun rest => normParentGet rfl
  have d1 : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 1)) (natList reps) (5 * inp.wt + 21) :=
    fun rest => normParentGet rfl
  have d2 : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 2)) (encKSetTuples e) (5 * inp.wt + 22) :=
    fun rest => normParentGet rfl
  have d3 : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 3)) (encPerm (1 : Perm (Fin Q.d)))
      (5 * inp.wt + 23) := fun rest => normParentGet rfl
  have d4 : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 4)) (encPerm (1 : Perm (Fin m)))
      (5 * inp.wt + 24) := fun rest => normParentGet rfl
  have da : ∀ rest, Det Pg (inp :: rest) (arg 1) (encPerm a) (2 * inp.wt + 6) :=
    fun rest => Det.arg' (j := 1) rfl
  have dc := Det.call (Det.mk2 (Det.mk2 (d0 []) (d1 [])) (da [])) hblock
  have dvar : Det Pg [inp, encPerm x.1] (.var 1) (encPerm x.1) ((encPerm x.1).wt + 2) :=
    (Det.var' rfl).mono (by omega)
  have dl := Det.mkList (P := Pg) (env := [inp, encPerm x.1])
    (c := 5 * inp.wt + 30 + 4 * Z ^ 2)
    [(.get (arg 0) (.nat 2), encKSetTuples e), (.var 1, encPerm x.1),
      (.get (arg 0) (.nat 3), encPerm (1 : Perm (Fin Q.d))),
      (.get (arg 0) (.nat 4), encPerm (1 : Perm (Fin m)))] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (d2 _).mono (by omega)
      · exact dvar.mono (by omega)
      · exact (d3 _).mono (by omega)
      · exact (d4 _).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  have dr := Det.call (Det.mk2 dl (d4 _)) hrec
  refine FunDet.intro hf ((Det.letE dc (Det.mk2 (da [encPerm x.1]) dr)).mono ?_)
  have wo := wt_encPerm_le (Q.permHom e hS x)
  have wa := wt_encPerm_le a
  have wp := wt_list2_le (encPerm a) (encPerm (Q.permHom e hS x))
  have wab := wt_list2_le (encFun num) (natList reps)
  have wbb := wt_list2_le (.list [encFun num, natList reps]) (encPerm a)
  have wrc := wt_list4_le (encKSetTuples e) (encPerm x.1)
    (encPerm (1 : Perm (Fin Q.d))) (encPerm (1 : Perm (Fin m)))
  have wrr := wt_list2_le rc (encPerm (1 : Perm (Fin m)))
  have wrcZ : rc.wt ≤ 20 * Z ^ 2 := by dsimp only [rc]; omega
  have wrrZ : (Val.list [.list [encKSetTuples e, encPerm x.1,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], encPerm (1 : Perm (Fin m))]).wt ≤
      50 * Z ^ 2 := by change (Val.list [rc, encPerm (1 : Perm (Fin m))]).wt ≤ _; omega
  have wx' : (encPerm (Q.ρ ⟨(toFin en).symm a, ha⟩)).wt ≤ 4 * Z ^ 2 := wx
  have hpow : (10 * Z ^ 2) ^ 6 = 10 ^ 6 * Z ^ 12 := by ring
  have hn6 : (n + 1) ^ 6 ≤ Z ^ 12 :=
    (Nat.pow_le_pow_left hnZ 6).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hm2 : (m + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hmZ 2
  have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hnZ 2
  have h212 : Z ^ 2 ≤ Z ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hZinp : inp.wt ≤ Z := by dsimp only [Z]; omega
  change _ ≤ 10 ^ 28 * Z ^ 12
  rw [hpow]
  omega

end GI.Impl
