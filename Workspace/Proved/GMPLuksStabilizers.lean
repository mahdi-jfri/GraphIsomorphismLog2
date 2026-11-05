module

public import Workspace.Proved.GMPLuksAction

@[expose] public section

/-! # The first kernel in Luks's normal-subgroup centralizer construction -/

namespace GI.Proved

variable {H V : Type*} [Group H] [MulAction H V]

/-- Conjugation transports the actual point stabilizers of a normal subgroup. -/
theorem gmp_stabilizer_conjugation (N : Subgroup H) [N.Normal] (h : H) (x : V) :
    (MulAction.stabilizer N x).map (MulAut.conjNormal h).toMonoidHom =
      MulAction.stabilizer N (h • x) := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    change (h * m.val * h⁻¹) • (h • x) = h • x
    rw [mul_smul, mul_smul, inv_smul_smul]
    change h • (m • x) = h • x
    rw [show m • x = x from hm]
  · intro hn
    refine ⟨MulAut.conjNormal h⁻¹ n, ?_, ?_⟩
    · change (h⁻¹ * n.val * h⁻¹⁻¹) • x = x
      rw [inv_inv, mul_smul, mul_smul]
      change h⁻¹ • (n • (h • x)) = x
      rw [show n • (h • x) = h • x from hn, inv_smul_smul]
    · rw [map_inv]
      change (MulAut.conjNormal h) ((MulAut.conjNormal h)⁻¹ n) = n
      exact MulAut.apply_inv_self N (MulAut.conjNormal h) n

def gmpStabilizerSetoid (N : Subgroup H) : Setoid V :=
  Setoid.ker (MulAction.stabilizer N)

theorem gmp_stabilizer_rel (N : Subgroup H) [N.Normal] (h : H)
    {x y : V} (hxy : (gmpStabilizerSetoid (V := V) N).r x y) :
    (gmpStabilizerSetoid (V := V) N).r (h • x) (h • y) := by
  change MulAction.stabilizer N (h • x) = MulAction.stabilizer N (h • y)
  rw [← gmp_stabilizer_conjugation N h x, ← gmp_stabilizer_conjugation N h y]
  exact congrArg (fun S : Subgroup N => S.map (MulAut.conjNormal h).toMonoidHom) hxy

/-- The action on equality classes of normal-subgroup point stabilizers. -/
def gmpLuksFirstAction (N : Subgroup H) [N.Normal] :
    H →* Equiv.Perm (Quotient (gmpStabilizerSetoid (V := V) N)) where
  toFun h :=
    { toFun := Quotient.map' (fun x : V => h • x) (fun _ _ => gmp_stabilizer_rel N h)
      invFun := Quotient.map' (fun x : V => h⁻¹ • x) (fun _ _ => gmp_stabilizer_rel N h⁻¹)
      left_inv := by
        intro q
        refine Quotient.inductionOn q (fun x => ?_)
        change (Quotient.mk'' (h⁻¹ • (h • x)) : Quotient (gmpStabilizerSetoid N)) = _
        rw [inv_smul_smul]
      right_inv := by
        intro q
        refine Quotient.inductionOn q (fun x => ?_)
        change (Quotient.mk'' (h • (h⁻¹ • x)) : Quotient (gmpStabilizerSetoid N)) = _
        rw [smul_inv_smul] }
  map_one' := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' ((1 : H) • x) : Quotient (gmpStabilizerSetoid N)) = _
    rw [one_smul]
    rfl
  map_mul' h k := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' ((h * k) • x) : Quotient (gmpStabilizerSetoid N)) = _
    rw [mul_smul]
    rfl

/-- The first kernel fixes each point stabilizer under conjugation. -/
theorem gmpLuksFirstAction_mem_ker (N : Subgroup H) [N.Normal] (h : H) :
    h ∈ (gmpLuksFirstAction (V := V) N).ker ↔
      ∀ x : V, MulAction.stabilizer N (h • x) = MulAction.stabilizer N x := by
  constructor
  · intro hh x
    have hx := congrArg (fun p : Equiv.Perm (Quotient (gmpStabilizerSetoid (V := V) N)) =>
      p (Quotient.mk'' x)) hh
    change (Quotient.mk'' (h • x) : Quotient (gmpStabilizerSetoid N)) = Quotient.mk'' x at hx
    exact Quotient.exact hx
  · intro hh
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' (h • x) : Quotient (gmpStabilizerSetoid N)) = Quotient.mk'' x
    exact Quotient.sound (hh x)

/-- This supplies the stabilizer-preservation hypothesis of the second action. -/
theorem gmpLuksFirstAction_preserves (N : Subgroup H) [N.Normal]
    (k : (gmpLuksFirstAction (V := V) N).ker) (x : V) :
    MulAction.stabilizer N x ≤
      (MulAction.stabilizer N x).comap (MulAut.conjNormal k.val).toMonoidHom := by
  apply Subgroup.map_le_iff_le_comap.mp
  rw [gmp_stabilizer_conjugation N k.val x,
    (gmpLuksFirstAction_mem_ker N k.val).mp k.property x]

/-- There are at most as many stabilizer classes as original points. -/
theorem gmpLuksFirstAction_degree (N : Subgroup H) [Finite V] :
    Nat.card (Quotient (gmpStabilizerSetoid (V := V) N)) ≤ Nat.card V :=
  Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk''_surjective

end GI.Proved
