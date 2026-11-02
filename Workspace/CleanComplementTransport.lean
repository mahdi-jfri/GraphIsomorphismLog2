import Workspace.CleanComplementLocal
import Workspace.CleanComplementSplit

/-! Transport the supplied group and block action along actual coordinates. -/
namespace GI.CleanBlockAction
variable {I V W : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I) (e : V ≃ W)

def relabeledGroup : Subgroup (Equiv.Perm W) := G.map (relabelPerm e).toMonoidHom

def relabelEquiv : G ≃* relabeledGroup (G := G) e := (relabelPerm e).subgroupMap G

def relabel : CleanBlockAction (relabeledGroup (G := G) e) I where
  label x := A.label (e.symm x)
  label_surjective := by
    intro i
    obtain ⟨x, hx⟩ := A.label_surjective i
    exact ⟨e x, by simpa using hx⟩
  top := A.top.comp (relabelEquiv (G := G) e).symm.toMonoidHom
  top_surjective := by
    intro p
    obtain ⟨g, hg⟩ := A.top_surjective p
    exact ⟨relabelEquiv (G := G) e g, by simpa using hg⟩
  action := by
    intro g x
    have h := A.action ((relabelEquiv (G := G) e).symm g) (e.symm x)
    change A.label (e.symm (g.val (e (e.symm x)))) = _ at h
    simpa only [e.apply_symm_apply] using h

theorem relabel_top (g : G) : (A.relabel e).top (relabelEquiv (G := G) e g) = A.top g := by
  change A.top ((relabelEquiv (G := G) e).symm (relabelEquiv (G := G) e g)) = _
  rw [MulEquiv.symm_apply_apply]

theorem relabel_localized {p : Equiv.Perm I} {g : Equiv.Perm V}
    (hg : LocalizedBlockLift A.label p g) :
    LocalizedBlockLift (A.relabel e).label p (relabelPerm e g) where
  action := by
    intro x
    change A.label (e.symm (e (g (e.symm x)))) = p (A.label (e.symm x))
    rw [e.symm_apply_apply]
    exact hg.action (e.symm x)
  fixes := by
    intro x hx
    change e (g (e.symm x)) = x
    rw [hg.fixes (e.symm x) hx, e.apply_symm_apply]

end GI.CleanBlockAction
