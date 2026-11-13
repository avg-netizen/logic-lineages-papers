module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem rankAtValues (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter lr rr : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw lr left)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rr right))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn lr rr)) := by
 apply sameCases R left right parameter _ (andRight (andRight ha))
 intro beta j Theta code hj hc
 have hsl := renameInto (andLeft ha) j Theta hj
 have hsr := renameInto (andLeft (andRight ha)) j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl hsr hl' hr'
 rw [InternalTagArithmeticSyntaxProof.eqnRelabel]
 exact SixSol20261113.Erasure.EvaluatorRankProof.actualRankDeterminacy R H G M W body beta Theta
   (left.relabel j) (right.relabel j) (parameter.relabel j) code (lr.relabel j) (rr.relabel j)
   hsl hsr (andLeft hc) (andRight hc) hl' hr'
theorem rankValue (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter rank : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank left))) :
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank right)) := by
 apply programCases OriginalRawSyntaxTransport.variableRankPackedRaw (Fin.cons right Fin.elim0) _
 intro beta j Theta value hj hv
 have ha' := renameInto ha j Theta hj
 have hl' := renameInto hl j Theta hj
 rw [admittedRename] at ha'
 rw [graph1Rename] at hl' ⊢
 simp only [consTermRename,emptyRename] at hv
 obtain ⟨he⟩ := rankAtValues R H G M W (left.relabel j) (right.relabel j) (parameter.relabel j)
   (rank.relabel j) value ha' hl' hv
 exact outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw value (rank.relabel j)
   (Fin.cons (right.relabel j) Fin.elim0) ⟨symm he⟩ hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherRankProof
