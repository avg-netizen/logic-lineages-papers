module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof

@[expose] public section
/-! Literal finite self-argument construction and auxiliary application for Select.
Numbered self copies retain the original head/base/extras and only reset their
result type. Application is the actual auxiliary app constructor, not a change
to original functional-head semantics. The numeric selected occurrence keeps
the existing list index, type guard and positive-label condition.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplication
open Source Source.SourceSpecialApplication NumberedAuxiliaryCoding NumberedExchangeCode

abbrev SelfData (Symbol : Type) := Nat × HeadCode Symbol × Code Symbol × List Ty × Code Symbol

def selfEntries {Symbol : Type} (d : SelfData Symbol) (types : List Ty) : List (Ty × Code Symbol) :=
  types.map (fun tau => (tau,Code.numbered d.1 d.2.1 tau d.2.2.1 d.2.2.2.1 d.2.2.2.2))

def selfCode {Symbol : Type} (d : SelfData Symbol) : List Ty → Code Symbol
  | [] => .argumentsNil
  | tau::types => .argumentsCons tau (.numbered d.1 d.2.1 tau d.2.2.1 d.2.2.2.1 d.2.2.2.2) (selfCode d types)

def applyCode {Symbol : Type} (q : Code Symbol) (entries : List (Ty × Code Symbol)) : Code Symbol :=
  entries.foldl (fun current entry => .app entry.1 current entry.2) q

def selectCode {Symbol : Type} (types : List Ty) (index : Nat) (tau : Ty) : Code Symbol → Option (Code Symbol)
  | .numbered (k+1) head _ base extraTypes extras => do
    let bs ← argumentEntries base
    let es ← argumentEntries extras
    let selected ← (bs++es)[index]?
    if selected.1=arrows types tau then
      pure (applyCode selected.2 (selfEntries (k,head,base,extraTypes,extras) types))
    else none
  | _ => none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplication
