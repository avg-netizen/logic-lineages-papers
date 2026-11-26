module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.PayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ModeChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def payload : Program 4 := .composition InternalPairing.pairing ![.projection 0,.projection 1]
def extended : Program 4 := .composition InternalListCodec.consCode ![.projection 0,.projection 3]
def queries : Fin 4 → Program 4 := ![payload,extended,headOf (.projection 2),tailOf (.projection 2)]

theorem recover (domain child typ gamma : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![domain,child,typ,gamma]))) :
    Nonempty (Derivation body Delta (StepPair (ys 0) domain child)) ∧
    Nonempty (Derivation body Delta (StepCons (ys 1) domain gamma)) ∧
    Nonempty (Derivation body Delta (StepArrowFields typ (ys 2) (ys 3))) := by
  let xs : Fin 4 → OTerm alpha := ![domain,child,typ,gamma]
  exact ⟨binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) domain child xs
      (hq 0) (projectionValue 0 xs) (projectionValue 1 xs),
    binaryRecover InternalListCodec.consCode (.projection 0) (.projection 3) (ys 1) domain gamma xs
      (hq 1) (projectionValue 0 xs) (projectionValue 3 xs),
    OriginalTypedDecoderInternalScalarProof.arrowFields (.projection 2) typ (ys 2) (ys 3) xs
      (projectionValue 2 xs) (hq 2) (hq 3)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
