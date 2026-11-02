import Workspace.CleanComplementLocalization

/-! LG2 under the unconditional linear fiber bound k > f. The source group,
outside-block permutation actions, and simultaneous fixed-point lift are constructed. -/
namespace GI.CleanLocalization
variable {I V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I)
variable (T : Finset I) {k : ℕ} (e : Fin k ≃ T)

def supportedTop : alternatingGroup (Fin k) →* alternatingGroup I where
  toFun p := ⟨Equiv.Perm.ofSubtype (relabelPerm e p.val), by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    change Equiv.Perm.sign (e.permCongr p.val) = 1
    rw [Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp p.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' p q := by apply Subtype.ext; simp

theorem supportedTop_fixes (p : alternatingGroup (Fin k)) (i : I) (hi : i ∉ T) :
    (supportedTop T e p).val i = i := Equiv.Perm.ofSubtype_apply_of_not_mem _ hi

theorem supportedTop_covers (p : alternatingGroup I) (hp : ∀ i, i ∉ T → p.val i = i) :
    ∃ s : alternatingGroup (Fin k), supportedTop T e s = p := by
  classical
  letI : Fintype T := Subtype.fintype (fun i : I => i ∈ T)
  have hpres : ∀ i, i ∈ T ↔ p.val i ∈ T := by
    intro i
    constructor
    · intro hi
      by_contra hn
      have he : p.val i = i := p.val.injective (hp (p.val i) hn)
      apply hn
      rw [he]
      exact hi
    · intro hi
      by_contra hn
      rw [hp i hn] at hi
      exact hn hi
  -- `subtypePerm` now takes `p (f x) ↔ p x`.
  replace hpres : ∀ i, p.val i ∈ T ↔ i ∈ T := fun i => (hpres i).symm
  have hsupport : ∀ i, p.val i ≠ i → i ∈ T := by
    intro i hi
    by_cases hm : i ∈ T
    · exact hm
    · exact False.elim (hi (hp i hm))
  let r : Equiv.Perm T := p.val.subtypePerm hpres
  let s : Equiv.Perm (Fin k) := relabelPerm e.symm r
  have hs : s ∈ alternatingGroup (Fin k) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (e.symm.permCongr r) = 1
    rw [Equiv.Perm.sign_permCongr]
    dsimp [r]
    rw [Equiv.Perm.sign_subtypePerm p.val hpres hsupport]
    exact Equiv.Perm.mem_alternatingGroup.mp p.property
  refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
  have hc : relabelPerm e (relabelPerm e.symm r) = r := by
    apply Equiv.ext
    intro x
    change e (e.symm (r (e (e.symm x)))) = r x
    rw [e.apply_symm_apply, e.apply_symm_apply]
  change Equiv.Perm.ofSubtype (relabelPerm e (relabelPerm e.symm r)) = p.val
  rw [hc]
  exact Equiv.Perm.ofSubtype_subtypePerm hpres hsupport

/-- Pull back the supported top embedding along the supplied top action. -/
def localSource : Subgroup (G × alternatingGroup (Fin k)) where
  carrier := {x | A.top x.1 = supportedTop T e x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change A.top (x.1 * y.1) = supportedTop T e (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change A.top x.1⁻¹ = supportedTop T e x.2⁻¹
    rw [map_inv, map_inv, hx]

def localTop : localSource A T e →* alternatingGroup (Fin k) :=
  (MonoidHom.snd G (alternatingGroup (Fin k))).comp (localSource A T e).subtype

theorem localTop_surjective : Function.Surjective (localTop A T e) := by
  intro p
  obtain ⟨g, hg⟩ := A.top_surjective (supportedTop T e p)
  exact ⟨⟨(g, p), hg⟩, rfl⟩

theorem outside_preserved (j : {i : I // i ∉ T}) (g : localSource A T e) (x : V) :
    A.label x = j.val ↔ A.label (g.val.1.val x) = j.val := by
  have hf : (A.top g.val.1).val j.val = j.val := by
    rw [g.property]
    exact supportedTop_fixes T e g.val.2 j.val j.property
  rw [A.action]
  calc
    A.label x = j.val ↔ (A.top g.val.1).val (A.label x) = (A.top g.val.1).val j.val :=
      (A.top g.val.1).val.injective.eq_iff.symm
    _ ↔ (A.top g.val.1).val (A.label x) = j.val := by rw [hf]

def outsideAction (j : {i : I // i ∉ T}) :
    localSource A T e →* Equiv.Perm {x : V // A.label x = j.val} where
  toFun g := g.val.1.val.subtypePerm (fun x => (outside_preserved A T e j g x).symm)
  map_one' := by apply Equiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' g h := by apply Equiv.ext; intro x; apply Subtype.ext; rfl

include e in
/-- Actual LG2, with k > every outside fiber degree. There is no transitivity
premise and no assumed local quotient or kernel-image conclusion. -/
theorem localLiftAvailable_of_linear_degree [Fintype V] (hk : 5 ≤ k)
    (hdegree : ∀ i, i ∉ T → Fintype.card {x : V // A.label x = i} < k) :
    LocalLiftAvailable A (T : Set I) := by
  classical
  intro p hp
  obtain ⟨s, hs⟩ := supportedTop_covers T e p hp
  obtain ⟨g, hg, hfix⟩ := small_degree_simultaneous_lift
    (fun j : {i : I // i ∉ T} => {x : V // A.label x = j.val}) hk
    (fun j => hdegree j.val j.property) (localTop A T e) (localTop_surjective A T e)
    (outsideAction A T e) s
  change g.val.2 = s at hg
  refine ⟨g.val.1, ?_, ?_⟩
  · exact g.property.trans ((congrArg (supportedTop T e) hg).trans hs)
  · intro x hx
    let j : {i : I // i ∉ T} := ⟨A.label x, hx⟩
    have he := congrArg
      (fun f : Equiv.Perm {y : V // A.label y = j.val} => (f ⟨x, rfl⟩).val) (hfix j)
    exact he

theorem localLiftAvailable_linear [Fintype V] (hk : 5 ≤ T.card)
    (hdegree : ∀ i, i ∉ T → Fintype.card {x : V // A.label x = i} < T.card) :
    LocalLiftAvailable A (T : Set I) := by
  classical
  apply localLiftAvailable_of_linear_degree A T (Fintype.equivFin T).symm
  · simpa using hk
  · intro i hi
    simpa using hdegree i hi

end GI.CleanLocalization
