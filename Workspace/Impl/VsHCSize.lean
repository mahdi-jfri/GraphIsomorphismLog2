module

public import Workspace.Impl.VsHCAb

@[expose] public section

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The repeated step-4 input permits the product transversal of size `24D`. -/
theorem vsHC_wt_in [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ks us : List (Perm (Fin I.n))}
    (hal : as.length ≤ I.n ^ 2) (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ vsQD s * vsQD s)
    (hksl : ks.length ≤ I.n ^ 2) (hus : us.length ≤ 24 * vsQD s) :
    (vsPIn s as Lb ks us).wt ≤ 10 ^ 9 * S ^ 8 := by
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have wlc := vsQ_wt_LC hS hs
  have wEG := hS.wt_group hal
  have wks := hS.wt_group hksl
  have hDD : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hSS : S * S = S ^ 2 := (sq S).symm
  have wLb : (vsFMatsVal Lb).wt ≤ 40 * (4 * S ^ 2 + 1) ^ 4 :=
    wt_vsFMatsVal_le (by omega) (by omega) (fun M hM => vsFSq_of_wSq (hLb M hM)) (by omega)
  have hN4 : (4 * S ^ 2 + 1) ^ 4 ≤ 625 * S ^ 8 := by
    have h1 : 4 * S ^ 2 + 1 ≤ 5 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    calc (4 * S ^ 2 + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 625 * S ^ 8 := by ring
  have wus : (Val.list (us.map encPerm)).wt ≤ 500 * S ^ 3 := by
    have h1 := vs_wt_list_le_of (us.map encPerm) (c := 4 * S ^ 2) (by
      intro v hv
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
      exact hS.wt_perm u)
    rw [List.length_map] at h1
    have h2 : us.length * (2 * (4 * S ^ 2) + 1) ≤ (24 * S) * (9 * S ^ 2) := Nat.mul_le_mul (by omega)
      (by have := Nat.one_le_pow 2 S hS1; omega)
    have e : (24 * S) * (9 * S ^ 2) = 216 * S ^ 3 := by ring
    have := Nat.one_le_pow 3 S hS1
    omega
  have l := wt_list_le [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ks, .list (us.map encPerm)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l
  have e : (vsPIn s as Lb ks us).wt = (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ks,
    .list (us.map encPerm)]).wt := rfl
  have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
  have q38 : S ^ 3 ≤ S ^ 8 := hS.pow_le (by omega)
  have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  omega

end GI.Impl
