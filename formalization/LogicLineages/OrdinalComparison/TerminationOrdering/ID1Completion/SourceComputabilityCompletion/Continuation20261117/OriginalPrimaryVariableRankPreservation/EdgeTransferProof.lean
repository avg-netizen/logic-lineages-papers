module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgePackedSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem preserved (n : Nat) (arity : Fin n → Nat)
 (source target parameter ref : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw ref source)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter))) :
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw ref target)) := by
 apply InternalAcceptanceSupportProof.programCases OriginalRawSyntaxTransport.variableRankPackedRaw (Fin.cons target Fin.elim0) _
 intro beta j Theta rank hj hr
 rw [graph1Rename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hr
 have hs' := renameInto hs j Theta hj
 rw [graph1Rename] at hs'
 have he' := renameInto he j Theta hj
 simp only [graph3Rename,numeral,sucRelabel,zRelabel] at he'
 have hEq := EdgePackedSourceProof.preserved n arity (source.relabel j) (target.relabel j) (parameter.relabel j) (ref.relabel j) rank hs' hr he'
 obtain ⟨hEq⟩ := hEq
 exact outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw rank (ref.relabel j) (Fin.cons (target.relabel j) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm hEq⟩ hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.EdgeTransferProof
