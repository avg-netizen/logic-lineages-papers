module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open Continuation20261115 OriginalBoundsRecombination
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def constructor (cons : Bool) := if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor

theorem rootValue (cons : Bool) (n : Nat) (raw typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (root n) (if cons then z else suc (suc z)) raw)) := by
  cases cons
  · have ht := applicationTag (.projection 0) raw typ left right ![raw] (projectionValue 0 ![raw]) hc
    have ht' := unaryRecover InternalUnpair.left (.projection 0) (numeral 2) raw ![raw] ht (projectionValue 0 ![raw])
    exact RootProof.termRoot n 2 (by decide) (by decide) (by decide) raw (suc (suc z)) hg ht'
      InternalApplicationValidityStackAppendTransitionProof.pairOneZero
  · have ht := consTag (.projection 0) raw typ left right ![raw] (projectionValue 0 ![raw]) hc
    have ht' := unaryRecover InternalUnpair.left (.projection 0) (numeral 7) raw ![raw] ht (projectionValue 0 ![raw])
    exact RootProof.consRoot n raw hg ht'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
