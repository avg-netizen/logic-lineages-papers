module

public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentNumericProof
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (rowAuxPair)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

/-- Use the original tag-6 row's argument-side arm. Parent term bits
are separately required, and both exact raw function slots are identical. -/
theorem exact_ClosedArgumentParentBit (hp : HeadPairs) (dom cod fn a b : Nat)
    (arg : (bits hp a b).1 = true)
    (left : (syntaxBits (auxRaw dom cod fn a)).1 = true)
    (right : (syntaxBits (auxRaw dom cod fn b)).1 = true) :
    (bits hp (auxRaw dom cod fn a) (auxRaw dom cod fn b)).1 = true := by
  have argRow : (row hp a b).1 = true := by
    simp only [bits,Bool.and_eq_true,and_assoc] at arg
    exact arg.2.2
  have parentRow : (row hp (auxRaw dom cod fn a) (auxRaw dom cod fn b)).1 = true := by
    rw [rowAuxPair]
    simp [argRow]
  simp [bits,left,right,parentRow]

#print axioms exact_ClosedArgumentParentBit
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentNumericProof
