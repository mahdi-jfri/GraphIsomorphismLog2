module

public import Workspace.Degree.GraphStep
public import Workspace.Degree.GraphSlots
public import Workspace.Degree.Class

/-!
# The invariants of the rooted comparison

Lemmas 9.3 and 9.4 of the paper, as facts on one step of the loop. Fix a graph `X`
with levels `ℓ`, and a second graph `Y` with the same levels.

* `fwd ℓ X u`: the forward neighbours of `u`, in increasing order.
* `step_coset`: `T ∈ C_r(X, Y)` and an element of the query give an element of `C_{r+1}(X, Y)`.
* `step_empty`: if the query is empty, then `C_{r+1}(X, Y)` is empty.
* `step_group`: the images of generators of the query generate `A_{r+1}`.
* `gammaHat_ballGroup`: Lemma 9.3.
-/

@[expose] public section

namespace GI.Degree

open Equiv

variable {n D : ℕ} {ℓ : Fin n → ℕ} {r R : ℕ} {X Y : SimpleGraph (Fin n)}

open Classical in
/-- The forward neighbours of `u`, in increasing order. -/
noncomputable def fwd (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun w => X.Adj u w ∧ ℓ w = ℓ u + 1

theorem fwdOK (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) : FwdOK ℓ X (fwd ℓ X) := by
  classical
  refine ⟨fun u => (List.nodup_finRange n).filter _, fun u w => ?_⟩
  simp [fwd]

/-- A level function is kept by the pull along a permutation that keeps it. -/
theorem HasLevels.pull {T : Perm (Fin n)} (hY : HasLevels Y ℓ R) (hT : ∀ u, ℓ (T u) = ℓ u) :
    HasLevels (GI.Degree.pull T Y) ℓ R := by
  refine ⟨?_, fun u v h hu => ?_, fun w h1 h2 => ?_⟩
  · exact hY.root
  · have := hY.step _ _ h (by rwa [hT])
    rwa [hT, hT] at this
  · obtain ⟨u, hu, he⟩ := hY.back (T w) (by rwa [hT]) (by rwa [hT])
    refine ⟨T⁻¹ u, ?_, ?_⟩
    · simpa using hu
    · have e : ℓ (T⁻¹ u) = ℓ u := by
        have := hT (T⁻¹ u)
        simpa using this.symm
      rw [e, he, hT]

theorem forall₂_right {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {b : β} (hb : b ∈ m) : ∃ a ∈ l, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, by simp [ha], hr⟩

theorem forall₂_left {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {a : α} (ha : a ∈ l) : ∃ b ∈ m, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, by simp [hb], hr⟩

section Step

variable {fX fY : Fin n → List (Fin n)} {par : Fin n → Fin n × Fin D} {z : Fin D}

/-- `Y^T` has the same adjacencies below level `r` as `X`, and we may step. If the query is empty,
then `C_{r+1}(X, Y)` is empty. -/
theorem step_empty (z : Fin D) {T : Perm (Fin n)} (hT : T ∈ Ball ℓ r X Y)
    (fXok : FwdOK ℓ X fX) (fYok : FwdOK ℓ (GI.Degree.pull T Y) fY)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par)
    (hQ : Query D ℓ r X (GI.Degree.pull T Y) fX fY = ∅) {h : Perm (Fin n)}
    (hh : h ∈ Ball ℓ (r + 1) X Y) : False := by
  have hT' : ∀ u, r + 1 < ℓ u → T u = u := fun u hu => hT.2.1 u (by omega)
  have h1 : T⁻¹ * h ∈ Ball ℓ (r + 1) X (GI.Degree.pull T Y) :=
    (mem_ball_pull hT.1 hT').2 (by simpa using hh)
  obtain ⟨g, hg, -⟩ := query_lift (z := z) fXok fYok hDX hpar (one_mem_ball_pull hT) h1
  rw [hQ]  at hg
  exact hg

/-- An element of the query gives the next coset representative. -/
theorem step_coset {T : Perm (Fin n)} (hT : T ∈ Ball ℓ r X Y) (hX : HasLevels X ℓ R)
    (hY : HasLevels Y ℓ R) (hr : r + 1 ≤ R)
    (fXok : FwdOK ℓ X fX) (fYok : FwdOK ℓ (GI.Degree.pull T Y) fY)
    (hDX : ∀ u, (fX u).length ≤ D) (hDY : ∀ u, (fY u).length ≤ D) (hpar : ParOK ℓ r fX par)
    {g : Perm (Fin n × Fin D)} (hg : g ∈ Query D ℓ r X (GI.Degree.pull T Y) fX fY) :
    ∃ e : Perm (Fin n), (∀ u, e u = decMap ℓ r fY par z g u) ∧ T * e ∈ Ball ℓ (r + 1) X Y := by
  have hT' : ∀ u, r + 1 < ℓ u → T u = u := fun u hu => hT.2.1 u (by omega)
  obtain ⟨e, he, heq⟩ := query_dec (z := z) hX (hY.pull hT.1) hr fXok fYok hDX hDY hpar
    (one_mem_ball_pull hT) hg
  exact ⟨e, heq, (mem_ball_pull hT.1 hT').1 he⟩

/-- The value of `dec` on the identity. -/
theorem dec_one (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par) (u : Fin n) :
    decMap ℓ r fX par z (1 : Perm (Fin n × Fin D)) u = u := by
  have h1 : (1 : Perm (Fin n × Fin D)) ∈ Query D ℓ r X X fX fX :=
    ⟨Subgroup.one_mem _, fun _ _ => rfl⟩
  obtain ⟨e, -, he⟩ := query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar one_mem_ball_self h1
  have h2 := query_dec_mul (z := z) hpar fXok h1 h1 u
  rw [one_mul, ← he u, ← he (e u)] at h2
  rw [← he u]
  exact (e.injective h2).symm

/-- The query of a pair `X, X` is a subgroup. -/
def querySub (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) (X : SimpleGraph (Fin n)) (fX : Fin n → List (Fin n)) :
    Subgroup (Perm (Fin n × Fin D)) where
  carrier := Query D ℓ r X X fX fX
  one_mem' := ⟨Subgroup.one_mem _, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨Subgroup.mul_mem _ h1 h3, fun s s' => (h2 _ _).trans (h4 _ _)⟩
  inv_mem' := by
    rintro f ⟨h1, h2⟩
    refine ⟨Subgroup.inv_mem _ h1, fun s s' => ?_⟩
    have := h2 (f⁻¹ s) (f⁻¹ s')
    simpa using this.symm

/-- `dec` as a homomorphism on the query. -/
noncomputable def decHom (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par) (z : Fin D) :
    querySub D ℓ r X fX →* Perm (Fin n) :=
  MonoidHom.mk' (fun g => (query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar one_mem_ball_self
      g.2).choose) fun f g => by
    ext u
    have h := fun (g : querySub D ℓ r X fX) => (query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar
      one_mem_ball_self g.2).choose_spec.2
    rw [h, Perm.mul_apply, h, h]
    exact congrArg _ (query_dec_mul hpar fXok f.2 g.2 u)

theorem decHom_apply (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par) (g : querySub D ℓ r X fX) (u : Fin n) :
    decHom hX hr fXok hDX hpar z g u = decMap ℓ r fX par z g.1 u :=
  (query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar one_mem_ball_self g.2).choose_spec.2 u

theorem decHom_mem (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par) (g : querySub D ℓ r X fX) :
    decHom hX hr fXok hDX hpar z g ∈ ballGroup ℓ (r + 1) X :=
  (query_dec (z := z) hX hX hr fXok fXok hDX hDX hpar one_mem_ball_self g.2).choose_spec.1

theorem decHom_range (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par) :
    (decHom (z := z) hX hr fXok hDX hpar).range = ballGroup ℓ (r + 1) X := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact decHom_mem hX hr fXok hDX hpar g
  · intro h hh
    obtain ⟨g, hg, he⟩ := query_lift (z := z) fXok fXok hDX hpar one_mem_ball_self hh
    refine ⟨⟨g, hg⟩, Equiv.ext fun u => ?_⟩
    rw [decHom_apply]
    exact he u

/-- The images of generators of the query generate `A_{r+1}`. -/
theorem step_group (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (fXok : FwdOK ℓ X fX)
    (hDX : ∀ u, (fX u).length ≤ D) (hpar : ParOK ℓ r fX par)
    {hs : List (Perm (Fin n × Fin D))} {es : List (Perm (Fin n))}
    (hc : Subgroup.closure {g | g ∈ hs} = querySub D ℓ r X fX)
    (hes : List.Forall₂ (fun h e => ∀ u, e u = decMap ℓ r fX par z h u) hs es) :
    Subgroup.closure {e | e ∈ es} = ballGroup ℓ (r + 1) X := by
  have hsQ : ∀ h ∈ hs, h ∈ querySub D ℓ r X fX := fun h hh => hc ▸ Subgroup.subset_closure hh
  have hmem : ∀ e ∈ es, ∃ h, ∃ hh : h ∈ querySub D ℓ r X fX,
      decHom (z := z) hX hr fXok hDX hpar ⟨h, hh⟩ = e := by
    intro e he
    obtain ⟨h, hh, hR⟩ := forall₂_right hes he
    refine ⟨h, hsQ h hh, Equiv.ext fun u => ?_⟩
    rw [decHom_apply, hR u]
  have hmem' : ∀ h (hh : h ∈ hs), ∃ e ∈ es,
      decHom (z := z) hX hr fXok hDX hpar ⟨h, hsQ h hh⟩ = e := by
    intro h hh
    obtain ⟨e, he, hR⟩ := forall₂_left hes hh
    refine ⟨e, he, Equiv.ext fun u => ?_⟩
    rw [decHom_apply, hR u]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro e he
    obtain ⟨h, hh, rfl⟩ := hmem e he
    exact decHom_mem hX hr fXok hDX hpar _
  · rw [← decHom_range (z := z) hX hr fXok hDX hpar]
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hg' : g ∈ Subgroup.closure {g | g ∈ hs} := hc ▸ hg
    suffices H : ∀ g (hg' : g ∈ Subgroup.closure {g | g ∈ hs}) (hgQ : g ∈ querySub D ℓ r X fX),
        decHom (z := z) hX hr fXok hDX hpar ⟨g, hgQ⟩ ∈ Subgroup.closure {e | e ∈ es} from H g hg' hg
    intro g hg'
    induction hg' using Subgroup.closure_induction with
    | mem x hx =>
      intro hq
      obtain ⟨e, he, hR⟩ := hmem' x hx
      exact Subgroup.subset_closure (hR ▸ he)
    | one =>
      intro hq
      have : (⟨1, hq⟩ : querySub D ℓ r X fX) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro hq
      have hxq : x ∈ querySub D ℓ r X fX := by
        rw [← hc]; exact hx
      have hyq : y ∈ querySub D ℓ r X fX := by
        rw [← hc]; exact hy
      have : (⟨x * y, hq⟩ : querySub D ℓ r X fX) = ⟨x, hxq⟩ * ⟨y, hyq⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (ihx hxq) (ihy hyq)
    | inv x hx ih =>
      intro hq
      have hxq : x ∈ querySub D ℓ r X fX := by
        rw [← hc]; exact hx
      have : (⟨x⁻¹, hq⟩ : querySub D ℓ r X fX) = (⟨x, hxq⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (ih hxq)

end Step

/-- `A_0` is trivial. -/
theorem ballGroup_zero (hX : HasLevels X ℓ R) : ballGroup ℓ 0 X = ⊥ := by
  obtain ⟨o, ho⟩ := hX.root
  rw [eq_bot_iff]
  intro g hg
  refine Subgroup.mem_bot.2 (Equiv.ext fun u => ?_)
  by_cases h : ℓ u = 0
  · have h1 : u = o := (ho u).1 h
    subst h1
    have h2 : ℓ (g u) = 0 := by rw [hg.1, h]
    exact (ho _).1 h2
  · exact hg.2.1 u (by omega)

/-- A parent slot exists for each vertex of level `r + 1`. -/
theorem exists_parOK (hX : HasLevels X ℓ R) (hr : r + 1 ≤ R) (z : Fin D)
    (hDX : ∀ u, (fwd ℓ X u).length ≤ D) : ∃ par : Fin n → Fin n × Fin D,
      ParOK ℓ r (fwd ℓ X) par := by
  classical
  have h : ∀ w, ∃ s : Fin n × Fin D, ℓ w = r + 1 → ℓ s.1 = r ∧ tgt (fwd ℓ X) s = some w := by
    intro w
    by_cases hw : ℓ w = r + 1
    · obtain ⟨u, hu, he⟩ := hX.back w (by omega) (by omega)
      have hlu : ℓ u = r := by omega
      obtain ⟨i, hi⟩ := exists_tgt (hDX u) (((fwdOK ℓ X).mem u w).2 ⟨hu, by omega⟩)
      exact ⟨(u, i), fun _ => ⟨hlu, hi⟩⟩
    · exact ⟨(w, z), fun h => absurd h hw⟩
  choose par hpar using h
  exact ⟨par, hpar⟩

/-- **Lemma 9.3.** -/
theorem gammaHat_ballGroup (hX : HasLevels X ℓ R) (hD : 1 ≤ D)
    (hDX : ∀ u, (fwd ℓ X u).length ≤ D) {r : ℕ} (hr : r ≤ R) :
    GammaHat D (ballGroup ℓ r X) := by
  have z : Fin D := ⟨0, hD⟩
  induction r with
  | zero =>
    rw [ballGroup_zero hX]
    exact ((gammaHat_perm D).subgroup ⊥).of_injective
      ((1 : (⊥ : Subgroup (Perm (Fin n))) →* (⊥ : Subgroup (Perm (Fin D))))) fun a b _ =>
        Subsingleton.elim a b
  | succ r ih =>
    obtain ⟨par, hpar⟩ := exists_parOK hX hr z hDX
    have h1 : GammaHat D (slotGroup D (ballGroup ℓ r X)) :=
      gammaHat_slotGroup z (ih (by omega))
    have hsub : querySub D ℓ r X (fwd ℓ X) ≤ slotGroup D (ballGroup ℓ r X) := fun g hg => hg.1
    have h2 : GammaHat D (querySub D ℓ r X (fwd ℓ X)) :=
      h1.of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
    let φ := decHom (z := z) hX hr (fwdOK ℓ X) hDX hpar
    let φ' : querySub D ℓ r X (fwd ℓ X) →* ballGroup ℓ (r + 1) X :=
      φ.codRestrict _ fun g => decHom_mem hX hr (fwdOK ℓ X) hDX hpar g
    refine h2.of_surjective φ' fun e => ?_
    have he : (e : Perm (Fin n)) ∈ φ.range := by
      rw [decHom_range]
      exact e.2
    obtain ⟨g, hg⟩ := he
    exact ⟨g, Subtype.ext hg⟩

end GI.Degree
