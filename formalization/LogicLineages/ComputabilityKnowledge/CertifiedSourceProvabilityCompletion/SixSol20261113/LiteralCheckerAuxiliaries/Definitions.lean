module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries
open GorbowSyntax GorbowPRProgram GorbowPRChildTags GorbowPRDefiningEquations List.Vector HistoryRuleSuffix

/-- Literal auxiliary replacements, NOT AST identities with the old witnesses.
Native certificate-code totality must justify removing the external decode guard. -/
def bound : Program 1 := .projection 0
def initial : Program 1 := applyTwo HistoryCodec.pair (constant 1 1) (.projection 0)

/-- Finalizer inputs remain [state,context,sortedFormulaCode,certificate]. -/
def optionField : Program 4 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def historyField : Program 4 := applyOne HistoryCodec.predecessor optionField
def entryField : Program 4 := applyOne HistoryLookup.head historyField
def contextField : Program 4 := applyOne (HistoryDecoder.decoder false) entryField
def rawField : Program 4 := applyOne (HistoryDecoder.decoder true) entryField
def doubledRaw : Program 4 := applyTwo HistoryCodec.add rawField rawField
def finalizer : Program 4 :=
  choose optionField (constant 4 0)
    (choose historyField (constant 4 0)
      (conjunction (applyTwo equalCode (.projection 1) contextField)
        (applyTwo equalCode (.projection 2) doubledRaw)))

def unaryCall {ctx : Nat} (tag : Nat) (a : Term ctx) : Term ctx := call tag (a ::ᵥ nil)
def finalCall {ctx : Nat} (tag : Nat) (state context formula certificate : Term ctx) : Term ctx :=
  call tag (state ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil)
def successfulState {ctx : Nat} (ptag ctag : Nat) (context raw tail lines : Term ctx) : Term ctx :=
  HistoryKernel.pairCall ptag (.succ (HistoryKernel.pairCall ctag (HistoryKernel.pairCall ptag context raw) tail)) lines

def finishCharacterization {ctx : Nat} (ftag ptag ctag : Nat)
    (context raw tail lines requested formula certificate : Term ctx) : Formula ctx :=
  let accepted := Formula.equal
    (finalCall ftag (successfulState ptag ctag context raw tail lines) requested formula certificate) (.succ .zero)
  let matchedFields : Formula ctx := Formula.conj (.equal requested context) (.equal formula (.add raw raw))
  .conj (.imp accepted matchedFields) (.imp matchedFields accepted)
def finishFailure {ctx : Nat} (ftag ptag : Nat) (lines requested formula certificate : Term ctx) : Formula ctx :=
  .conj (.equal (finalCall ftag (HistoryKernel.pairCall ptag .zero lines) requested formula certificate) .zero)
    (.equal (finalCall ftag (HistoryKernel.pairCall ptag (.succ .zero) lines) requested formula certificate) .zero)

def coreTag (pF : Program 1) (v l a : Program 1) (x : Program 3) : Nat :=
  SixSol20261112.HistoryMachine.coreCheckerTag (GorbowNamedInternalProvability.checkerTag pF)
    (LiteralKernelSource.coreChecker v l a x bound initial finalizer)
def finalizerTag (pF : Program 1) (v l a : Program 1) (x : Program 3) : Nat := coreTag pF v l a x+1
def loopTag (pF : Program 1) (v l a : Program 1) (x : Program 3) : Nat :=
  coreTag pF v l a x + argumentTag finalizer
    (SixSol20261112.HistoryMachine.checkerArguments (HistoryKernel.kernel v l a x) bound initial) 0
def boundTag (pF : Program 1) (v l a : Program 1) (x : Program 3) : Nat :=
  loopTag pF v l a x + argumentTag (SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x))
    (SixSol20261112.HistoryMachine.loopArguments bound initial) 0 + 1
def initialTag (pF : Program 1) (v l a : Program 1) (x : Program 3) : Nat :=
  loopTag pF v l a x + argumentTag (SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x))
    (SixSol20261112.HistoryMachine.loopArguments bound initial) 1 + 1

def boundClause (pF : Program 1) (v l a : Program 1) (x : Program 3) : Sentence :=
  GorbowStandardInduction.universalClosure
    (.equal (unaryCall (boundTag pF v l a x) (.var (0 : Fin 1))) (.var 0))
def initialClause (pF : Program 1) (v l a : Program 1) (x : Program 3) : Sentence :=
  GorbowStandardInduction.universalClosure
    (.equal (unaryCall (initialTag pF v l a x) (.var (0 : Fin 1)))
      (HistoryKernel.pairCall (LiteralKernelSource.pairTag pF v l a x bound initial finalizer) (.succ .zero) (.var 0)))
def finishClause (pF : Program 1) (v l a : Program 1) (x : Program 3) : Sentence :=
  GorbowStandardInduction.universalClosure
    (finishCharacterization (finalizerTag pF v l a x)
      (LiteralKernelSource.pairTag pF v l a x bound initial finalizer)
      (LiteralKernelSource.consTag pF v l a x bound initial finalizer)
      (.var (0 : Fin 7)) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6))
def failureClause (pF : Program 1) (v l a : Program 1) (x : Program 3) : Sentence :=
  GorbowStandardInduction.universalClosure
    (finishFailure (finalizerTag pF v l a x)
      (LiteralKernelSource.pairTag pF v l a x bound initial finalizer)
      (.var (0 : Fin 4)) (.var 1) (.var 2) (.var 3))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries
