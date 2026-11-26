module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (certain childAt measureAt)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)

def typeAt (T : Program 1) (i : Nat) : Program 4 := unaryAfter T (childAt i)

def auxAccept (T : Program 1) : Program 4 :=
  conjunction (typeAt T 0) (conjunction (typeAt T 1) (conjunction (measureAt 2) (measureAt 3)))

/-- New selected unary memo. Use the original tag-six recursive row only
for the physical four-field header and earlier child addresses; on
other rows, the exact previous V program still evaluates the same key. -/
def auxSyntaxUpdate (V T : Program 1) : Program 4 :=
  branch certain (unaryAfter V currentKey) (auxAccept T)

def auxSyntax (V T : Program 1) : Program 1 := selectedMeasure (auxSyntaxUpdate V T)

abbrev auxTape {α : Type} (dom cod fn arg old : OTerm α) : Fin 4 → OTerm α :=
  ![memoPrior dom cod fn arg,old,z,z]

def ExactCoverAuxSyntaxSource : Prop :=
  ∀ (raw dom cod fn arg : Nat),
    unpackNode raw = some (6,[dom,cod,fn,arg]) →
    fn < raw ∧ arg < raw ∧
    (syntaxBits raw).1 = (typeBit dom && typeBit cod && (syntaxBits fn).1 && (syntaxBits arg).1)

def ExactCoverAuxSyntaxStepCalibration : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = (syntaxBits n).1.toNat) →
    evaluate (auxSyntaxUpdate V T) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = (syntaxBits (i+1)).1.toNat

def ExactCoverAuxSyntaxCalibration : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
    TermSyntaxCalibrated (auxSyntax V T)

def auxSyntaxChildren {α : Type} (V T : Program 1) (dom cod fn arg : OTerm α) : Formula α :=
  (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (unary (auxSyntax V T) (suc z) fn ⊓ unary (auxSyntax V T) (suc z) arg)

def ExactOpenCoverAuxSyntaxRow : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old : OTerm α),
    Nonempty (Derivation body Γ (tableAt (auxSyntaxUpdate V T) old (memoPrior dom cod fn arg))) →
    Nonempty (Derivation body Γ
      (programGraph (auxSyntaxUpdate V T) (suc z) (auxTape dom cod fn arg old))) →
    Nonempty (Derivation body Γ (auxSyntaxChildren V T dom cod fn arg))

def ExactOpenCoverAuxSyntaxParent : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ (unary (auxSyntax V T) (suc z) (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (auxSyntaxChildren V T dom cod fn arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
