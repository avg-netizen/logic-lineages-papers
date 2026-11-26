module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem numeralRename {alpha beta : Type} (n : Nat) (j : alpha → beta) :
    (numeral n : OTerm alpha).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih => simpa only [numeral,sucRelabel] using congrArg suc ih

/-- Keep the Program opaque while transporting a literal selector graph. -/
theorem literalGraphRename {body : Positive (Fin 1)} {alpha : Type}
    {Delta : List (Formula alpha)} (p : Program 1) (tag : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 p (numeral tag) raw)))
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Nonempty (Derivation body Theta (graph1 p (numeral tag) (raw.relabel j))) := by
  simpa only [graph1Rename,numeralRename] using
    InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
