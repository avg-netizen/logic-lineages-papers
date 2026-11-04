module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftTargets
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryShift

def ActualCodeShiftPrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : Nat × Code (Fin n) => shiftCode p.1 p.2)

def ActualTypedShiftCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (binders Gamma : List Ty) (sigma tau : Ty) (q : AuxTerm Symbol arity (binders++Gamma) tau),
  termCode (rename q (prefixWeakening binders Gamma sigma))=shiftCode binders.length (termCode q)

def ActualArgumentShiftCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (binders Gamma types : List Ty) (sigma : Ty) (args : AuxArguments Symbol arity (binders++Gamma) types),
  argumentsCode (renameArguments args (prefixWeakening binders Gamma sigma))=shiftCode binders.length (argumentsCode args)

def ActualPackedWeakeningPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma : Ty),
  Primrec (@weakenPacked n arity Gamma sigma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftTargets
