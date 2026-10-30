module
public import LogicLineages.ModelsAlgebra.PGroups.RawSemanticsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

def RawGroupStructure.AbelianLaws {G : Type u} (R : RawGroupStructure G) : Prop :=
  (∀ x y z, R.add (R.add x y) z = R.add x (R.add y z)) ∧
  (∀ x y, R.add x y = R.add y x) ∧
  (∀ x, R.add R.zero x = x) ∧
  (∀ x, R.add (R.neg x) x = R.zero)

def abelianGroupMatrix : QF 3 :=
  let x : GroupTerm 3 := .var 0
  let y : GroupTerm 3 := .var 1
  let z : GroupTerm 3 := .var 2
  .and (.equal (.add (.add x y) z) (.add x (.add y z)))
    (.and (.equal (.add x y) (.add y x))
      (.and (.equal (.add .zero x) x) (.equal (.add (.neg x) x) .zero)))

def abelianGroupAxioms : Formula 0 :=
  .conjAll {0} (fun _ => 3) (fun _ => .qf abelianGroupMatrix)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
