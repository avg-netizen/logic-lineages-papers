module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaCode (raw metadata child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw metadata child))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  have hf := lambdaFields raw z metadata child hc
  exact unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))

theorem ordinary (raw metadata child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw metadata child))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  have hf := ordinaryFields raw z metadata child hc
  exact unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))

theorem application (raw typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw typ left right))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess left raw ⊓ InternalLessThan.strictLess right raw)) := by
  have hf := applicationFields raw typ left right hc
  exact binaryChildrenStrict raw left right (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))

theorem cons (raw typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ left right))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess left raw ⊓ InternalLessThan.strictLess right raw)) := by
  have hf := consFields raw typ left right hc
  exact binaryChildrenStrict raw left right (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))

theorem numbered (raw label head typ left types right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,left,types,right]))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess left raw ⊓ InternalLessThan.strictLess right raw)) := by
  have hf := numberedFields raw label head typ left types right hc
  exact binaryChildrenStrict raw left right (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
