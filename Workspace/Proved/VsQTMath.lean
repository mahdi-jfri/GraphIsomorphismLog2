import Workspace.Proved.VsWKey

/-!
# The subspace of a key

A key `vsWKey p d us` determines the span of `us` (`vsWKey_eq_iff`). Here we recover the span
from the key by a kernel: `span (vsWKer p (vsWKey p d us)) = span us` (`vsWKey_ker`). The
tuple small orbit transporter uses this to act on keys.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

theorem vsWKey_length (d : ℕ) (us : List (List ℕ)) : (vsWKey p d us).length = d := by
  simp [vsWKey]

/-- **The kernel of the key is the span.** -/
theorem vsWKey_ker (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (hu : VsWFit p d us) :
    vsWSp p d (vsWKer p (vsWKey p d us)) = vsWSp p d us := by
  set K := vsWKey p d us
  have hK : VsWFit p d K := vsWKey_fit hp.one_lt us
  have hKl : K.length = d := vsWKey_length d us
  have hfit := vsWKer_fit hp.one_lt hK
  have hspan : Submodule.span (ZMod p) {w | w ∈ (vsWKer p K).map (vsF p)} = vsWSpN p (vsWKer p K) :=
    (vsWSpN_eq_span_list _).symm
  have hsuppK : vsWSpN p (vsWKer p K) ≤ vsWSupp p d := by
    have := vsWSpN_le_supp (p := p) fun t ht => (hfit t ht).2.le
    rwa [hKl] at this
  have hsuppU : vsWSpN p us ≤ vsWSupp p d := vsWSpN_le_supp fun u h => (hu u h).2.le
  have hcomb : ∀ a : ℕ → ZMod p,
      vsComb p K a = ∑ i ∈ Finset.range d, a i • vsF p (K.getD i []) := by
    intro a; rw [vsComb, hKl]
  have key : vsWSpN p (vsWKer p K) = vsWSpN p us := by
    ext a
    constructor
    · intro ha
      have haS := hsuppK ha
      have h1 := (vsUnitPairs_ker hp hK (a := a) (fun j hj => haS j (hKl ▸ hj))).mpr (by
        rw [← hspan] at ha; exact ha)
      rw [hcomb] at h1
      exact (vsWKey_mem hp hu haS).mpr h1
    · intro ha
      have haS := hsuppU ha
      have h1 := (vsWKey_mem hp hu haS).mp ha
      rw [← hcomb] at h1
      have := (vsUnitPairs_ker hp hK (a := a) (fun j hj => haS j (hKl ▸ hj))).mp h1
      rw [← hspan]; exact this
  rw [vsWSp_eq_map, vsWSp_eq_map, key]

end GI.Proved
