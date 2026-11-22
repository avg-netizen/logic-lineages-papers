module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt measureAt)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)

def TypeSyntaxCalibrated (T : Program 1) : Prop := ∀ n, run T n = (typeBit n).toNat

def lambdaShape : Program 4 := unaryAfter (header 2 2) currentKey
def lambdaGuard : Program 4 := conjunction lambdaShape (earlierAt 1)
def lambdaTypeSlot (T : Program 1) : Program 4 := unaryAfter T (childAt 0)
def lambdaAccept (T : Program 1) : Program 4 := conjunction (lambdaTypeSlot T) (measureAt 1)

/-- Fresh reselected memo update. Only the original canonical lambda
branch reads its literal body slot from this same earlier table. All
other raw nodes still use the supplied original syntax program V. -/
def lambdaSyntaxUpdate (V T : Program 1) : Program 4 :=
  branch lambdaGuard (unaryAfter V currentKey) (lambdaAccept T)

/-- The same generic physical scratch-row reader and zero parameters,
now applied to the actual literal lambda update. This is not an AST
identity with V or the previously selected header-only guard. -/
def lambdaSyntax (V T : Program 1) : Program 1 :=
  selectedMeasure (lambdaSyntaxUpdate V T)

abbrev lambdaPrior {α : Type} (ty q : OTerm α) :=
  pairTerm (numeral 2) (packedBody [ty,q])

abbrev lambdaTape {α : Type} (ty q old : OTerm α) : Fin 4 → OTerm α :=
  ![lambdaPrior ty q,old,z,z]

def ExactCoverLambdaSyntaxStepCalibration : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = (syntaxBits n).1.toNat) →
    evaluate (lambdaSyntaxUpdate V T) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = (syntaxBits (i+1)).1.toNat

def ExactCoverLambdaSyntaxCalibration : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
    TermSyntaxCalibrated (lambdaSyntax V T)

def lambdaRecovered {α : Type} (V T : Program 1) (ty q old : OTerm α) : Formula α :=
  unary T (suc z) ty ⊓
    (unary (lambdaSyntax V T) (suc z) q ⊓
      programGraph (measureAt 1) (suc z) (lambdaTape ty q old))

/-- Genuine acceptance of one literal recursive lambda update on the
supplied actual prior table supplies the same child selected bit,
literal annotation bit, and exact lookup. The child bit is not input. -/
def ExactOpenCoverLambdaSyntaxRow : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q old : OTerm α),
    Nonempty (Derivation body Γ (tableAt (lambdaSyntaxUpdate V T) old (lambdaPrior ty q))) →
    Nonempty (Derivation body Γ (programGraph (lambdaSyntaxUpdate V T) (suc z) (lambdaTape ty q old))) →
    Nonempty (Derivation body Γ (lambdaRecovered V T ty q old))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
