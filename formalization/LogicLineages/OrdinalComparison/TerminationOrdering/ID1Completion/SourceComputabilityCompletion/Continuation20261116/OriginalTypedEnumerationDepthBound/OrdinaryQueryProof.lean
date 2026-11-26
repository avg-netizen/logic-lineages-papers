module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ModeChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def payload : Program 2 := .composition InternalPairing.pairing ![.projection 0,.projection 1]
def signature (H : Program 1) : Program 2 := .composition H (fun _ : Fin 1 => .projection (0 : Fin 2))
def queries (H : Program 1) : Fin 4 → Program 2 := ![payload,signature H,headOf (signature H),tailOf (signature H)]

theorem recover (H : Program 1) (head base : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries H i) (ys i) ![head,base]))) :
    Nonempty (Derivation body Delta (StepPair (ys 0) head base)) ∧
    Nonempty (Derivation body Delta (programGraph H (ys 1) ![head])) ∧
    Nonempty (Derivation body Delta (StepArrowFields (ys 1) (ys 2) (ys 3))) := by
  let xs : Fin 2 → OTerm alpha := ![head,base]
  exact ⟨binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) head base xs
      (hq 0) (projectionValue 0 xs) (projectionValue 1 xs),
    unaryRecover H (.projection 0) (ys 1) head xs (hq 1) (projectionValue 0 xs),
    OriginalTypedDecoderInternalScalarProof.arrowFields (signature H) (ys 1) (ys 2) (ys 3) xs
      (hq 1) (hq 2) (hq 3)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
