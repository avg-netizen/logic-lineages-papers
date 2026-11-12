module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
/-- Only a standalone return macrostep. Stored counters control extraction;
local typed calibration supplies their genuine values. No evaluator/fuel law. -/
def work : Program 1 := leftOf (.projection 0)
def results : Program 1 := rightOf (.projection 0)
def frame : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def rest : Program 1 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => work)
def payload : Program 1 := rightOf frame
def parent : Program 1 := leftOf payload
def counts : Program 1 := rightOf payload
def childCount : Program 1 := leftOf counts
def deletionCount : Program 1 := rightOf counts
def role : Program 1 := leftOf parent
def expectedType : Program 1 := leftOf (rightOf parent)
def rawJob : Program 1 := rightOf (rightOf parent)
def raw : Program 1 := leftOf rawJob
def parameter : Program 1 := rightOf rawJob
def packed : Program 1 := pairOf expectedType raw
def selected (P : Program 3) : Program 1 := .composition P ![childCount,deletionCount,results]
def firstSlot : Program 1 := selected OriginalHereditaryResultStackProgram.firstSlot
def secondSlot : Program 1 := selected OriginalHereditaryResultStackProgram.secondSlot
def deletionRow : Program 1 := selected OriginalHereditaryResultStackProgram.deletionRow
def oldSuffix : Program 1 := selected OriginalHereditaryResultStackProgram.oldSuffix
def termValue (R : Program 2) : Program 1 := pairOf
  (.composition (OriginalRootObservation.rootObservation R) ![packed,parameter])
  (pairOf (.composition OriginalHereditaryReturn.returnRoot ![packed,firstSlot,secondSlot]) deletionRow)
def argumentsValue : Program 1 :=
  .composition OriginalHereditaryReturn.returnArgumentsCons ![raw,firstSlot,secondSlot]
def pop (value : Program 1) : Program 1 := pairOf rest (consOf value oldSuffix)
def listStep : Program 1 :=
  OriginalTypedDecoder.ifSame (leftOf raw) (constant 1 6) (pop (constant 1 0))
    (OriginalTypedDecoder.ifSame (leftOf raw) (constant 1 7) (pop argumentsValue) (.projection 0))
/-- Empty work, non-return tags, unknown roles, unsupported list tags preserve
state. Supported tags with inconsistent counters have literal total selector
behavior only, with no typing/success claim. -/
def step (R : Program 2) : Program 1 := InternalAcceptance.branch work (.projection 0)
  (OriginalTypedDecoder.ifSame (leftOf frame) (constant 1 1)
    (OriginalTypedDecoder.ifSame role (constant 1 0) (pop (termValue R))
      (OriginalTypedDecoder.ifSame role (constant 1 1) listStep (.projection 0))) (.projection 0))
def termChildren (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) : Packed (Fin n) arity Gamma → List Nat
 | ⟨_,.var _⟩ => []
 | ⟨_,.bottom _⟩ => []
 | ⟨_,@AuxTerm.lam _ _ _ d t q⟩ => [OriginalHereditaryReturn.scalar Q c ⟨t,q⟩]
 | ⟨t,@AuxTerm.app _ _ _ d _ f a⟩ =>
     [OriginalHereditaryReturn.scalar Q c ⟨.arrow d t,f⟩,OriginalHereditaryReturn.scalar Q c ⟨d,a⟩]
 | ⟨_,.ordinary h base⟩ => [numbersNumber (OriginalRootObservation.argumentValues Q c base)]
 | ⟨_,.numbered k h _ base _ extras⟩ =>
     [numbersNumber (OriginalRootObservation.argumentValues Q c base),
      numbersNumber (OriginalRootObservation.argumentValues Q c extras)]
def argumentChildren (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
    (c : Nat) : AuxArguments (Fin n) arity Gamma types → List Nat
 | .nil => []
 | @AuxArguments.cons _ _ _ tau _ q args =>
     [OriginalHereditaryReturn.scalar Q c ⟨tau,q⟩,numbersNumber (OriginalRootObservation.argumentValues Q c args)]
def termJob {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) (q : Packed (Fin n) arity Gamma) : Nat :=
  OriginalHereditaryAnnotatedExpansion.jobNumber 0 (typeNumber q.1)
    (Nat.pair (codeNumber (NumberedAuxiliaryCoding.termCode q.2)) (Nat.pair c (typesNumber Gamma)))
def argumentJob {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
    (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) : Nat :=
  OriginalHereditaryAnnotatedExpansion.jobNumber 1 0
    (Nat.pair (codeNumber (NumberedAuxiliaryCoding.argumentsCode args)) (Nat.pair c (typesNumber Gamma)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStep
