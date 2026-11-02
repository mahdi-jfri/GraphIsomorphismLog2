import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.SetTheory.Cardinal.Finite

namespace GI.Cited

/-- **Automorphism groups of nonabelian simple groups are small.**
For every finite nonabelian simple group `T`, `|Aut(T)| ≤ |T|^2`.

*Source.* Paper, proof of Lemma A.8 (`lem:budget-primitive-valuation`), paragraph on
the regular/diagonal cases: "the standard bound `|Aut(T)| ≤ |T|^2` suffices. For
example it follows from the outer-automorphism estimate in [GMP, Lemma 7.7], applied
to the regular representation." [GMP] = Guralnick, Maróti, Pyber, *Normalizers of
primitive permutation groups*, Adv. Math. 310 (2017) 1017-1063, Lemma 7.7, an estimate
for `|Out(T)|` in terms of a faithful permutation degree of `T`. By the paper, applying
it to the regular representation (degree `|T|`) gives `|Out(T)| ≤ |T|`, that is
`|Aut(T)| = |T| |Out(T)| ≤ |T|^2`. (The exact wording of [GMP, Lemma 7.7] was not
rechecked here; the inequality itself is checked against CFSG below.)

*Why it is true.* By the classification of finite simple groups (CFSG), `Out(T)` is
known for every `T`: it is trivial or at most 4 for alternating (`|Out(A_6)| = 4`) and
sporadic groups (at most 2), and for a group of Lie type of rank `r` over `𝔽_q`,
`q = p^f`, it is the product of diagonal, field and graph parts, of order at most
a constant times `(r+1) f` (paper, proof of Lemma A.8), far below `|T|`. The smallest case `T = A_5` has `|Aut T| = 120 ≤ 3600`.
The ratio `|Out T|/|T|` is largest for small groups such as `PSL_3(4)`
(`|Out| = 12`, `|T| = 20160`), still far below `1`.

*Why it is the weakest form needed.* The paper uses exactly this inequality, once,
to bound `v_3(|G|) ≤ s log_3 |Aut T| + v_3(s!)` for `G ≤ Aut(T) wr Sym(s)`.
Only nonabelian simple `T` occur (the socle factors of a primitive group with
nonabelian socle). It is stated for groups in `Type` (universe 0), which is where all
socle factors of permutation groups on `Fin n` live. -/
def AutCardLeSq : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ x y : T, x * y ≠ y * x) →
    Nat.card (MulAut T) ≤ Nat.card T ^ 2

end GI.Cited
