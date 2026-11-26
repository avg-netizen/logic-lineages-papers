module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
import LogicLineages.PermittedControl.SharedRankResidueRowStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open FiniteStripCollectorRecovery
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (Layout)
open StatementChecks (fixed_sharedRankResidueRowCodeExact)

abbrev ConjoinArgs := Layout × RawArgs × Option Nat
private abbrev Prepared := List NamedCode × Nat

theorem conjoinPrimitive : Primrec (fun p : ConjoinArgs => conjoinCode p.1 p.2.1 p.2.2) := by
  have layout : Primrec (fun p : ConjoinArgs => p.1) := Primrec.fst
  have row : Primrec (fun p : ConjoinArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have compile := fixed_sharedRankResidueRowCodeExact.2.1.comp (layout.pair row)
  let Merge := ConjoinArgs × Prepared
  let Join := Merge × Nat
  have rest : Primrec (fun p : Merge => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have code : Primrec (fun p : Join => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have tail : Primrec (Prod.snd : Join → Nat) := Primrec.snd
  have both : Primrec (fun p : Join => 6 * Nat.pair p.1.2.2 p.2 + 4) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp code tail))
      (Primrec.const 4)
  apply (Primrec.option_bind compile (Primrec.option_map rest both.to₂).to₂).of_eq
  rintro ⟨layout,row,tail⟩
  unfold conjoinCode
  cases SharedRankResidueRow.prepareCode (layout,row) with
  | none => rfl
  | some head => cases tail <;> rfl

theorem conjoinNone (layout : Layout) (r : RawArgs) (tail : Option Nat) :
    conjoinCode layout r tail = none ↔ r.1 = 0 ∨ tail = none := by
  by_cases zero : r.1 = 0
  · simp [conjoinCode,SharedRankResidueRow.prepareCode,zero]
  · cases tail <;> simp [conjoinCode,SharedRankResidueRow.prepareCode,zero]

end LogicLineages.PermittedControl.SignedCongruenceMatrix
