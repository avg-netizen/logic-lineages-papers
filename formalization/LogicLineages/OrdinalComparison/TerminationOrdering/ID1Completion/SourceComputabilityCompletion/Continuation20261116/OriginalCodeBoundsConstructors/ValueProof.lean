module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MergeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261115 OriginalCodeBoundsRecursion OriginalBoundsRecombination
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem fromValues (n : Nat) (raw values rootValue collected out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsEquation.answers n) values raw z)))
    (hr : Nonempty (Derivation body Delta (graph1 (root n) rootValue raw)))
    (hc : Nonempty (Derivation body Delta (graph1 collect collected values)))
    (hm : Nonempty (Derivation body Delta (graph2 merge out rootValue collected))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  have hr' := unaryValue (root n) (.projection 0) rootValue raw ![raw,values]
    hr (projectionValue 0 ![raw,values])
  have hc' := unaryValue collect (.projection 1) collected values ![raw,values]
    hc (projectionValue 1 ![raw,values])
  have hv := binaryValue merge (.composition (root n) (fun _ : Fin 1 => .projection 0))
    (.composition collect (fun _ : Fin 1 => .projection 1)) out rootValue collected ![raw,values] hm hr' hc'
  have hs := OriginalCodeBoundsRecursion.SupportProof.recombineSuccess n raw values out hg hv
  exact AnswersProof.fromLayer n raw values out ha
    (OriginalCodeBoundsRecursion.SupportProof.positiveValue n raw values z (suc out) hg hs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
