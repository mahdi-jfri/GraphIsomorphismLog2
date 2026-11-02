/-
The `simp` set `machine_simps`: the lemmas that evaluate expressions and statement effects of the
machine in a symbolic state. Use it as `simp only [machine_simps, h₀, h₁]`, where `h₀, h₁` give
the values of the registers.
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register

/-- Lemmas that evaluate machine expressions and the states after `assign` and `store`. -/
register_simp_attr machine_simps
