module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)

/-- The literal original independent raw syntax guard, not the whole
finite-context check or a guard inferred from acceptance. -/
def ActualRawSyntax (syntaxProg : Program 1) : Prop :=
  ∀ q, evaluate syntaxProg (q ::ᵥ nil) = ((NumberedWindowSyntaxAlgorithm.syntaxBits q).1).toNat

/-- The original lexical context is the successfully unpacked ordered
list. An undecodable packed value is rejected, not read as []. -/
def packedWindow (s : Settings) (ctx ty q : Nat) : Bool :=
  (unpack ctx).any (fun g => admitted s g ty q)

def ActualPackedWindow (s : Settings) (windowProg : Program 3) : Prop :=
  ∀ ctx ty q, evaluate windowProg (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) = (packedWindow s ctx ty q).toNat

/-- All original inputs, including every malformed code. All four
calibrations refer to named original source functions, not abstract
Boolean predicates or an untyped repair of the endpoint guards. -/
def ExactTypedRaw5Calibration : Prop :=
  ∀ (entries : Entries) (s : Settings) (root other windowProg : Program 3)
    (syntaxProg : Program 1),
    ActualRoot (NumberedWindowConcreteCheckers.root entries s) root →
    ActualFallback other → ActualRawSyntax syntaxProg → ActualPackedWindow s windowProg →
    ActualRawCalibration entries s (typedRaw5 root other windowProg syntaxProg)

/-- The genuine object graph of the same selected inputs and callbacks.
Unit output is equivalent to ALL five original unit graph calls, with
the input context/type shared exactly and no arithmetic truth reflection. -/
def ExactOpenTypedRaw5 : Prop :=
  ∀ (body : Positive (Fin 1)) (root other windowProg : Program 3)
    (syntaxProg : Program 1) (α : Type) (Γ : List (Formula α)) (ctx ty q w r : OTerm α),
    let raw := programGraph (typedRaw5 root other windowProg syntaxProg) (suc z) ![ctx,ty,q,w,r]
    let guards :=
      ((programGraph syntaxProg (suc z) ![q] ⊓ programGraph syntaxProg (suc z) ![r]) ⊓
        programGraph (ownRun root other) (suc z) ![q,w,r]) ⊓
      (programGraph windowProg (suc z) ![ctx,ty,q] ⊓ programGraph windowProg (suc z) ![ctx,ty,r])
    Nonempty (Derivation body Γ ((raw.imp guards) ⊓ (guards.imp raw)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
