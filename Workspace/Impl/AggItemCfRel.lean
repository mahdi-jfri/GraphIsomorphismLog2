import Workspace.Impl.AggItemCfProg
import Workspace.Impl.AggItemStepWt
import Workspace.Impl.AggItemCase
import Workspace.Impl.AggItemOK
import Workspace.Impl.GenNormPoly

/-!
# Cases 2b and 3: the bounds and the relations of the case program

**Bounds.** With `W₀` the input weight of the call and `T = Xt W₀` the bound of the item stage:
`itCfG W₀` bounds `q + 1` and the weight of `K.v`; the object part of a kept value weighs at most
`itCfWOB W₀` (`itCf_wO_wt`, from the length bound of the cache), a kept value at most
`itCfKB W₀ T`, a branch state at most `itCfRB W₀ T`.

**Relations** (`itCfRel`).
* `Kc K w D`: `w = [itCfWO H_X H_Y c_X cache, wI]` with a good cache, a kept value `wI` of the
  item stage for a choice set `E`, and `D = itCfD K cache E` (the rounds agreeing with the cache,
  with choices in `E`).
* `Rb K b bst D sb f`: either the start `[K.v, ⟨b⟩, w]` with `Kc K w D` and the item scripts, or
  a later state `[[itCfWO … cache, kst], u]` with `[kst, u]` an item state for `E`, objects
  `oX, oY`, and `D = itCfD K cache E` with `sb Ag = sbI (Ag.soj, Ag.rep)`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-! ### The bounds -/

/-- The base of the bounds. -/
def itCfG (W : ℕ) : ℕ := itSVB W + 2 * W + 5

/-- The weight bound of the object part of a kept value. -/
def itCfWOB (W : ℕ) : ℕ := 10 ^ 4 * itCfG W ^ 69

/-- The weight bound of a kept value. -/
def itCfKB (W T : ℕ) : ℕ := 4 * (itCfWOB W + T) + 10

/-- The weight bound of a branch state. -/
def itCfRB (W T : ℕ) : ℕ := 10 * (itCfKB W T + 5 * itCfG W ^ 2 + itSVB W) + 100

/-- The weight bound of the inputs of the object steps. -/
def itCfV (W T : ℕ) : ℕ := 10 * itCfRB W T + 100 * itCfG W ^ 4 + 10

/-- The bound of the callees of the object steps. -/
def itCfBp (Co Do c2 k2 W T : ℕ) : ℕ :=
  itCfB Co Do (8 * itCfV W T + 8) + itCfLkC (4 * itCfV W T + 6) + c2 * (itCfV W T + 2) ^ k2 +
    30 * itCfG W ^ 4 + stRefK * (6 * itCfV W T + 20 + 1) ^ 2

/-- The bound of the object step with its dispatch. -/
def itCfBo (Co Do c2 k2 W T : ℕ) : ℕ :=
  3 * itCfO2C (itCfV W T) (itCfBp Co Do c2 k2 W T) + 100 * (itCfV W T + 11)

/-- The cost bound of a branch step. -/
def itCfSB (Co Do c2 k2 W T : ℕ) : ℕ :=
  3 * itCfStC (itCfRB W T) (itCfBo Co Do c2 k2 W T) T + 3 * itCfCtC (itCfRB W T) T +
    200 * (itCfRB W T + 11)

/-- The cost bound of the init. -/
def itCfIB (Co Do W T : ℕ) : ℕ :=
  itCfIC (itSVB W) (itGrpC (itSVB W)) (itCfB Co Do (1000 * itCfG W ^ 3)) T

/-- **The bound of Cases 2b and 3**, for the item bound `T`. -/
def itCfXP (Co Do c2 k2 W T : ℕ) : ℕ :=
  itCfRB W T + T + itCfSB Co Do c2 k2 W T + itCfIB Co Do W T + 10

/-- **The bound of Cases 2b and 3.** -/
def itCfX (Co Do c2 k2 : ℕ) (Xt : ℕ → ℕ) (W : ℕ) : ℕ := itCfXP Co Do c2 k2 W (Xt W)

theorem itCfB_mono {C D a b : ℕ} (h : a ≤ b) : itCfB C D a ≤ itCfB C D b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ### Polynomial bounds -/

theorem itCf_pbu_base : PBU fun _ W _ => itCfG W := by
  have hK : PBU fun _ W _ => 2 * W + 3 := PBU.addc (PBU.smul 2 PBU.W) 3
  have hNb : PBU fun _ W _ => cmNb (2 * W + 3) := PBU.smul 2 (PBU.pow hK 64)
  have hPb : PBU fun _ W _ => cmPb (2 * W + 3) :=
    PBU.addc (PBU.smul 9 (PBU.addc (PBU.smul 2 (PBU.smul _ (PBU.pow (PBU.addc hK 1) 70))) 1)) 4
  have hOut : PBU fun _ W _ => cmOutB (2 * W + 3) :=
    PBU.addc (PBU.smul 6 (PBU.addc (PBU.smul 2 (PBU.addc (PBU.add (PBU.smul 2 hPb)
      (PBU.smul 14 (PBU.mul hNb hNb))) 20)) 1)) 4
  have hS : PBU fun _ W _ => itSVB W :=
    PBU.addc (PBU.smul 2 (PBU.add (PBU.addc (PBU.add hOut (PBU.smul 2 (PBU.addc (PBU.smul 2
      (PBU.smul 5 (PBU.pow (PBU.addc (PBU.pow hK 64) 1) 2))) 6))) 5)
      (PBU.smul 5 (PBU.pow (PBU.addc hK 1) 2)))) 8
  exact PBU.addc (PBU.add hS (PBU.smul 2 PBU.W)) 5

/-- **The bound of Cases 2b and 3 is polynomial** when the item bound is. -/
theorem itCfX_pbu (Co Do c2 k2 : ℕ) {Xt : ℕ → ℕ} (hXt : PBU fun _ W _ => Xt W) :
    PBU fun _ W _ => itCfX Co Do c2 k2 Xt W := by
  have hG := itCf_pbu_base
  have hS : PBU fun _ W _ => itSVB W := hG.mono fun _ W _ => by unfold itCfG; omega
  -- polynomial in `W` (through `itCfG`, `itSVB`) and `B` (the item bound)
  have hWO : PBU fun _ W _ => itCfWOB W := PBU.smul (10 ^ 4) (PBU.pow hG 69)
  have hKB : PBU fun _ W B => itCfKB W B :=
    PBU.addc (PBU.smul 4 (PBU.add hWO PBU.B)) 10
  have hRB : PBU fun _ W B => itCfRB W B :=
    PBU.addc (PBU.smul 10 (PBU.add (PBU.add hKB (PBU.smul 5 (PBU.pow hG 2))) hS)) 100
  have hV : PBU fun _ W B => itCfV W B :=
    PBU.addc (PBU.add (PBU.smul 10 hRB) (PBU.smul 100 (PBU.pow hG 4))) 10
  have hBf : ∀ {f : ℕ → ℕ → ℕ → ℕ}, PBU f → PBU fun k W B => itCfB Co Do (f k W B) :=
    fun hf => PBU.smul Co (PBU.pow (PBU.addc hf 1) Do)
  have hBp : PBU fun _ W B => itCfBp Co Do c2 k2 W B := by
    unfold itCfBp itCfLkC
    exact PBU.add (PBU.add (PBU.add (PBU.add (hBf (PBU.addc (PBU.smul 8 hV) 8))
      (PBU.smul _ (PBU.pow (PBU.addc (PBU.addc (PBU.smul 4 hV) 6) 1) 3)))
      (PBU.smul c2 (PBU.pow (PBU.addc hV 2) k2))) (PBU.smul 30 (PBU.pow hG 4)))
      (PBU.smul _ (PBU.pow (PBU.addc (PBU.addc (PBU.smul 6 hV) 20) 1) 2))
  have hBo : PBU fun _ W B => itCfBo Co Do c2 k2 W B := by
    unfold itCfBo itCfO2C
    exact PBU.add (PBU.smul 3 (PBU.smul _ (PBU.addc (PBU.add hV hBp) 1)))
      (PBU.smul 100 (PBU.addc hV 11))
  have hWr : ∀ {f : ℕ → ℕ → ℕ → ℕ}, PBU f → PBU fun k W B => itCfWrC (f k W B) :=
    fun hf => PBU.smul _ (PBU.pow (PBU.addc hf 1) 2)
  have hSB : PBU fun _ W B => itCfSB Co Do c2 k2 W B := by
    unfold itCfSB itCfStC itCfCtC
    exact PBU.add (PBU.add (PBU.smul 3 (PBU.add (PBU.smul 1000 (PBU.addc (PBU.add (PBU.add hRB hBo)
      PBU.B) 10)) (PBU.smul 5 (hWr (PBU.addc (PBU.smul 4 (PBU.add hBo PBU.B)) 6)))))
      (PBU.smul 3 (PBU.add (PBU.smul 1000 (PBU.addc (PBU.add hRB PBU.B) 10))
        (PBU.smul 5 (hWr (PBU.addc (PBU.smul 4 (PBU.add hRB PBU.B)) 6))))))
      (PBU.smul 200 (PBU.addc hRB 11))
  have hIB : PBU fun _ W B => itCfIB Co Do W B := by
    unfold itCfIB itCfIC itGrpC
    exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add hS
      (PBU.smul _ (PBU.pow (PBU.addc hS 1) 5))) (hBf (PBU.smul 1000 (PBU.pow hG 3)))) PBU.B) 10)
  have hP : PBU fun _ W B => itCfXP Co Do c2 k2 W B := by
    unfold itCfXP
    exact PBU.addc (PBU.add (PBU.add (PBU.add hRB PBU.B) hSB) hIB) 10
  exact itS_pbu_subst (P := fun W B => itCfXP Co Do c2 k2 W B) (X := Xt) hP hXt

end GI.Impl
