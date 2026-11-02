import Workspace.Impl.LinObjectMath

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectEncoding_injective {n : ℕ} : Function.Injective (tmGlObjVal (n := n)) := by
  rintro ⟨c, ls, h⟩ ⟨c', ls', h'⟩ he
  have he' : c = c' ∧ encGroup ls = encGroup ls' ∧ encPerm h = encPerm h' := by
    simpa only [tmGlObjVal, Val.list.injEq, List.cons.injEq,
      Val.nat.injEq, and_true] using he
  obtain ⟨rfl, hls, hh⟩ := he'
  obtain rfl := encGroup_injective hls
  obtain rfl := encPerm_injective hh
  rfl

theorem linObjectListEncoding_injective {n : ℕ} :
    Function.Injective (tmGlObjsVal (n := n)) := by
  intro X Y h
  exact (List.map_injective_iff.mpr linObjectEncoding_injective) (Val.list.inj h)

end GI.Impl
