import Workspace.Impl.LinPermZpow
import Workspace.Impl.LinPermWordMath
import Workspace.Lang.Prims.Repr
import Workspace.Lang.Lib.LinIntVector
import Workspace.Impl.LinFiniteActionCost

/-! Lift an integer vector to an ordered word in the supplied permutation
generators. The loop uses signed binary powers, with no enumeration of
the represented abelian group. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPermWordStep (power : ℕ) : Expr :=
  .call power (mk3
    (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.arith .add (arg 1) (.nat 1)))
    (.get (.get (arg 0) (.nat 1)) (arg 1)) (arg 2))

def linPermWordFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1)))
    (.get (.get (.get (.var 0) (.nat 0)) (.nat 1)) (.nat 0)) (linPermWordStep (b + 3)) ++
    linPermZpowFuns (b + 3)

theorem linPermWordFuns_length (b : ℕ) : (linPermWordFuns b).length = 23 := rfl

structure linPermWordAt (P : Program) (b : ℕ) : Prop where
  loop : P.HasAt b (loopFuns b (.length (.get (.var 0) (.nat 1)))
    (.get (.get (.get (.var 0) (.nat 0)) (.nat 1)) (.nat 0)) (linPermWordStep (b + 3)))
  power : linPermZpowAt P (b + 3)

theorem linPermWordAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPermWordFuns b)) : linPermWordAt P b where
  loop := h.left
  power := linPermZpowAt_of (h.block 3 rfl)

theorem linPermZpowCost_mono {W V : ℕ} (hW : W ≤ V) : linPermZpowCost W ≤ linPermZpowCost V := by
  unfold linPermZpowCost linIntCodecCost linPermPowCost linPermPowUnit
  gcongr

def linPermWordAcc (W : ℕ) : ℕ := 4 * (W + 1) ^ 2
def linPermWordArg (W : ℕ) : ℕ := 100 * (W + linPermWordAcc W + 1)
def linPermWordStepCost (W : ℕ) : ℕ :=
  10000 * (W + linPermWordAcc W + linPermZpowCost (linPermWordArg W) + 1)
def linPermWordCost (W : ℕ) : ℕ :=
  100000 * (W + 1) * (W + linPermWordAcc W + linPermZpowCost (linPermWordArg W) + 1)

set_option maxHeartbeats 150000 in
set_option maxRecDepth 2000 in
theorem linPermWord_spec {P : Program} {b n : ℕ} (h : linPermWordAt P b)
    (as : List (Equiv.Perm (Fin n))) (z : Fin as.length → ℤ) :
    let a := Val.list [encGroup as, linVecVal z]
    FunDet P b a (encPerm (linGroupWord (fun i => as.get i) z)) (linPermWordCost a.wt) := by
  let a := Val.list [encGroup as, linVecVal z]
  let W := a.wt
  let t := as.length
  let word := linGroupWordPrefix (fun i => as.get i) z
  let M := linPermWordAcc W
  have wg : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have wz : (linVecVal z).wt < W := wt_le_wt_list (by simp [a, W])
  have wgs : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt := wt_le_wt_list (by
    simp [encGroup, encPerms])
  have wone : (encPerm (1 : Equiv.Perm (Fin n))).wt < (Val.list ((1 :: as).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change n < (encPerm (1 : Equiv.Perm (Fin n))).wt at hh
    omega
  have ht : t ≤ W := by
    have hh := length_lt_wt_list ((List.finRange t).map fun i => encInt (z i))
    simp only [List.length_map, List.length_finRange] at hh
    change t < (linVecVal z).wt at hh
    omega
  have hw (i : ℕ) : (encPerm (word i)).wt ≤ M :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have dk := Det.length (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1) rfl)
  simp only [List.length_map, List.length_finRange] at dk
  have dg := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 0) rfl
  have dl := Det.get' dg (Det.nat 1) rfl
  have di := Det.get' dl (Det.nat 0) rfl
  have hl := loopBdd_spec h.loop dk di (by
    dsimp only [a, W, encGroup, encPerms, linVecVal] at *
    omega) (Inv := fun i acc => acc = encPerm (word i))
    (M := M) (D := fun _ => linPermWordStepCost W) (by simp [word])
    (fun i acc _ he => he ▸ hw i) (fun i acc hi he => ?_)
  · refine hl.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
    have hs := Nat.mul_le_mul_right (linPermWordStepCost W) ht
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right ht 1))
      (by omega : W + t + M + 1 ≤ 2 * W + M + 1)
    change cost ≤ linPermWordCost W
    unfold linPermWordCost linPermWordStepCost at *
    dsimp only [M] at *
    nlinarith
  · subst he
    have hi' : i < t := by simpa using hi
    let j : Fin t := ⟨i, hi'⟩
    let g := as.get j
    have wg' : (encPerm g).wt < (Val.list ((1 :: as).map encPerm)).wt := wt_le_wt_list (by
      simp only [List.mem_map]
      exact ⟨g, List.mem_cons_of_mem _ (List.get_mem _ _), rfl⟩)
    have wz' := linVecEntryWt z j
    have harg : (Val.list [encPerm g, encInt (z j), encPerm (word i)]).wt ≤ linPermWordArg W := by
      have hh := wt_list3_le (encPerm g) (encInt (z j)) (encPerm (word i))
      have ha := hw i
      unfold linPermWordArg
      dsimp only [M] at *
      omega
    have hp := (linPermZpow_spec h.power g (word i) (z j)).mono (linPermZpowCost_mono harg)
    have da := Det.arg' (P := P) (vs := [a, .nat i, encPerm (word i)]) (rest := []) (j := 0) rfl
    have dix := Det.arg' (P := P) (vs := [a, .nat i, encPerm (word i)]) (rest := []) (j := 1) rfl
    have dacc := Det.arg' (P := P) (vs := [a, .nat i, encPerm (word i)]) (rest := []) (j := 2) rfl
    have dgs := Det.get' (Det.get' da (Det.nat 0) rfl) (Det.nat 1) rfl
    have dnext := Det.arith' (op := .add) dix (Det.nat 1) (z := i + 1) rfl
    have dgen := Det.get' dgs dnext (v := encPerm g) (by
      simp [g, j, List.getElem?_map, List.getElem?_eq_getElem hi'])
    have dz := Det.get' (Det.get' da (Det.nat 1) rfl) dix (v := encInt (z j)) (by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hi)]
      simp [j])
    have dout := Det.call (Det.mk3 dgen dz dacc) hp
    have hu : word (i + 1) = g ^ z j * word i :=
      linGroupWordPrefix_succ (fun j => as.get j) z j
    refine dout.post fun cost hc => ⟨?_, ?_⟩
    · exact congrArg encPerm hu.symm
    · suffices hcost : cost ≤ linPermWordStepCost W from hcost.trans (Nat.le_add_right _ _)
      have wstep := wt_list3_le a (.nat i) (encPerm (word i))
      have wcall := wt_list3_le (encPerm g) (encInt (z j)) (encPerm (word i))
      have wcurrent := hw i
      have wnext := hw (i + 1)
      rw [hu] at wnext
      have widx := wt_nat_le i
      unfold linPermWordStepCost
      dsimp only [a, W, M, t, word, g, j, encGroup, encPerms, linVecVal] at *
      omega

theorem linPermWordCost_poly : PBU (fun _ W _ => linPermWordCost W) := by
  have ha : PBU (fun _ W _ => linPermWordAcc W) :=
    PBU.smul 4 (PBU.pow (PBU.addc PBU.W 1) 2)
  have hi : PBU (fun _ W _ => linPermWordArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W ha) 1)
  have hp : PBU (fun _ W _ => linPermZpowCost (linPermWordArg W)) :=
    linPoly_subst (f := fun _ W _ => linPermZpowCost W) linPermZpowCost_poly
      (PBU.const 0) hi (PBU.const 0)
  unfold linPermWordCost
  simpa only [Nat.mul_assoc] using PBU.smul 100000
    (PBU.mul (PBU.addc PBU.W 1) (PBU.addc (PBU.add (PBU.add PBU.W ha) hp) 1))

end GI.Impl
