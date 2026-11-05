module

public import Workspace.Impl.VsPKey
public import Workspace.Proved.VsPGrowMath

@[expose] public section

/-!
# What the key computes

* `vsPLocL_eq_iff`: stored local matrices are equal iff the local matrices are.
* `vsQLam_pow`: `Λ(c^a) = Λ(c)^a`.
* `vsPKeyIdx_eq`: if `Λ⁅y, g⁆ = Λ(c0)^t` with `t < r` and the powers `Λ(c0)^a`, `a < r`, are
  distinct, then the key entry is `t`.
-/

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I}

theorem vsPLocL_eq_iff (hs : VsQStOK s) (g h : Perm (Fin I.n)) :
    vsPLocL I s.ws' (vsQCs s) g = vsPLocL I s.ws' (vsQCs s) h ↔ vsQLam s g = vsQLam s h := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  constructor
  · intro e
    show vsWM I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) g) = vsWM I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) h)
    rw [e]
  · intro e
    have hg := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) g
    have hh := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) h
    have hg' : VsFSq I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) g) := ⟨hg.2, fun a ha => hg.1 a ha⟩
    have hh' : VsFSq I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) h) := ⟨hh.2, fun a ha => hh.1 a ha⟩
    have e' : vsFMatrix I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) g) =
        vsFMatrix I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) h) := by
      rw [vsFMatrix_loc, vsFMatrix_loc, e]
    rw [vsQL_of_sq hg', vsQL_of_sq hh', e']

theorem vsQLam_pow (hs : VsQStOK s) {c : Perm (Fin I.n)} (hc : c ∈ gens s.hs) :
    ∀ a : ℕ, vsQLam s (c ^ a) = vsQLam s c ^ a
  | 0 => by rw [pow_zero, pow_zero, vsQLam_one hs]
  | a + 1 => by rw [pow_succ, pow_succ, vsQLam_mul hs (pow_mem hc a) hc, vsQLam_pow hs hc a]

/-- **The key entry is the discrete logarithm.** -/
theorem vsPKeyIdx_eq (hs : VsQStOK s) {c0 y g : Perm (Fin I.n)} (hc0 : c0 ∈ gens s.hs)
    {r t : ℕ} (ht : t < r)
    (hdist : ∀ a < r, ∀ b < r, vsQLam s c0 ^ a = vsQLam s c0 ^ b → a = b)
    (he : vsQLam s ⁅y, g⁆ = vsQLam s c0 ^ t) :
    vsPKeyIdx I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) y g = t := by
  unfold vsPKeyIdx vsPZp
  have hp : ∀ a < r, (decide (vsPLocL I s.ws' (vsQCs s) (c0 ^ a) =
      vsPLocL I s.ws' (vsQCs s) ⁅y, g⁆) = true ↔ a = t) := by
    intro a ha
    rw [decide_eq_true_iff, vsPLocL_eq_iff hs, vsQLam_pow hs hc0, he]
    exact ⟨hdist a ha t ht, fun h => h ▸ rfl⟩
  rw [List.findIdx_eq (by simpa using ht)]
  simp only [List.getElem_map, List.getElem_range]
  refine ⟨(hp t ht).2 rfl, fun j hj => ?_⟩
  have := hp j (by omega)
  cases hd : decide (vsPLocL I s.ws' (vsQCs s) (c0 ^ j) = vsPLocL I s.ws' (vsQCs s) ⁅y, g⁆)
  · rfl
  · exact absurd (this.1 hd) (by omega)

end GI.Proved

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I}

theorem vsQRho_ext (hs : VsQStOK s) {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsQRho hs ⟨g, hg⟩ = vsQRho hs ⟨h, hh⟩ ↔ vsQLam s g = vsQLam s h := by
  constructor
  · intro e
    have := congrArg (fun u : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ =>
      (u : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))) e
    simp only [vsQRho_eq_toLin' hs] at this
    exact Matrix.toLin'.injective this
  · intro e
    apply Units.ext
    rw [vsQRho_eq_toLin' hs, vsQRho_eq_toLin' hs, e]

/-- **The key entry is the discrete logarithm of the images.** -/
theorem vsPKeyIdx_dl (hs : VsQStOK s) {c0 y g : Perm (Fin I.n)} (hc0 : c0 ∈ gens s.hs)
    (hy : y ∈ gens s.hs) (hg : g ∈ gens s.hs) {r : ℕ} [NeZero r]
    (hord : orderOf (vsQRho hs ⟨c0, hc0⟩) = r) {t : ZMod r}
    (he : ⁅vsQRho hs ⟨y, hy⟩, vsQRho hs ⟨g, hg⟩⁆ = vsQRho hs ⟨c0, hc0⟩ ^ t.val) :
    vsPKeyIdx I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) y g = t.val := by
  have hcm : ⁅y, g⁆ ∈ gens s.hs := by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem hy hg) (inv_mem hy)) (inv_mem hg)
  have hpow : ∀ a : ℕ, c0 ^ a ∈ gens s.hs := fun a => pow_mem hc0 a
  have hρpow : ∀ a : ℕ, vsQRho hs ⟨c0 ^ a, hpow a⟩ = vsQRho hs ⟨c0, hc0⟩ ^ a := by
    intro a; rw [← map_pow]; rfl
  refine vsPKeyIdx_eq hs hc0 (ZMod.val_lt t) (fun a ha b hb hab => ?_) ?_
  · rw [← vsQLam_pow hs hc0, ← vsQLam_pow hs hc0, ← vsQRho_ext hs (hpow a) (hpow b), hρpow,
      hρpow] at hab
    rw [pow_inj_mod, hord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    exact hab
  · rw [← vsQLam_pow hs hc0, ← vsQRho_ext hs hcm (hpow _), hρpow, ← he]
    have : vsQRho hs ⟨⁅y, g⁆, hcm⟩ = vsQRho hs (⁅(⟨y, hy⟩ : gens s.hs), ⟨g, hg⟩⁆) := rfl
    rw [this, map_commutatorElement]

end GI.Proved
