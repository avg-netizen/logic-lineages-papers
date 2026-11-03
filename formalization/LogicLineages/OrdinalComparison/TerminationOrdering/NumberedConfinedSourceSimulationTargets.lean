module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationTargets
open Source Source.SourceMarkedSyntax LiteralContexts NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowCertificates NumberedWindowTraces NumberedOrdinaryWindow
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedConfinedSourceSimulation

/-- Both original and translated endpoints lie in the source's exact type window. -/
def ActualSourceWindow : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
    ConfinedStrict above s t →
    SubtypeClosed (fun u => u ∈ sourceWindow s) ∧
    OriginalGood (symbols n) (sourceWindow s) ⟨tau, embed s⟩ ∧
    OriginalGood (symbols n) (sourceWindow s) ⟨tau, embed t⟩ ∧
    InUniverse (symbols n) (sourceWindow s) (translateOriginal s) ∧
    InUniverse (symbols n) (sourceWindow s) (translateOriginal t)

/-- A confined strict comparison gives a positive actual trace within Ty(s). -/
def ActualStrictWindowTrace : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
    ConfinedStrict above s t →
    ∃ (count : Nat) (_ : 0 < count)
      (path : WindowTrace (Fin n) arity (symbols n) (sourceWindow s) above Gamma
        count (translated s) (translated t)),
      allBoundaries path

/-- The same positive trace descends to the actual least-code quotient. -/
def ActualStrictQuotientPath : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (above : Fin n → Fin n → Prop)
    (Gamma : List Ty) (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
    ConfinedStrict above s t →
    PositivePath (QuotientEdge n arity (symbols n) (sourceWindow s) above Gamma)
      (representativeCode (symbols n) (sourceWindow s) (translated s))
      (representativeCode (symbols n) (sourceWindow s) (translated t))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationTargets
