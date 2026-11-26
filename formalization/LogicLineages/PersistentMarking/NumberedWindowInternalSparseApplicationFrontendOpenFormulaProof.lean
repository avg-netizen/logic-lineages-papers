module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqnRelabel eqnSubst sucRelabel sucSubst zRelabel zSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (numeralSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst graph3Subst)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports addressTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (reportBody reportBinder reportUnfold reportRename auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)

attribute [local irreducible] programGraph

private theorem addressRename {α β : Type} (c t k : OTerm α) (j : α → β) :
    (addressTerm c t k).relabel j = addressTerm (c.relabel j) (t.relabel j) (k.relabel j) := by
  simp only [addressTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem addressSubst {α β : Type} (c t k : OTerm α) (ts : α → OTerm β) :
    (addressTerm c t k).subst ts = addressTerm (c.subst ts) (t.subst ts) (k.subst ts) := by
  simp only [addressTerm,consTerm,pairTerm,addSubst,mulSubst,sucSubst,zSubst,numeralSubst]

theorem auxiliarySubst {α β : Type} (d e l r : OTerm α) (ts : α → OTerm β) :
    (auxiliaryTerm d e l r).subst ts =
      auxiliaryTerm (d.subst ts) (e.subst ts) (l.subst ts) (r.subst ts) := by
  simp only [auxiliaryTerm,rawConsSubst,numeralSubst,zSubst]

private theorem literalUnaryRename {α β : Type} (p : Program 1) (out x : OTerm α) (j : α → β) :
    (programGraph p out ![x]).relabel j = programGraph p (out.relabel j) ![x.relabel j] :=
  unaryRename p out x j

private theorem literalUnarySubst {α β : Type} (p : Program 1) (out x : OTerm α) (ts : α → OTerm β) :
    (programGraph p out ![x]).subst (fun a => emb (ts a)) =
      programGraph p (out.subst ts) ![x.subst ts] :=
  unarySubst p out x ts

theorem inputsRename {α β : Type} (f u c r d e l k : OTerm α) (j : α → β) :
    (parsedApplicationInputs f u c r d e l k).relabel j = parsedApplicationInputs
      (f.relabel j) (u.relabel j) (c.relabel j) (r.relabel j)
      (d.relabel j) (e.relabel j) (l.relabel j) (k.relabel j) := by
  simp only [parsedApplicationInputs,addressReports,arrowReports,conjunctionRename,unaryRename,literalUnaryRename,
    eqnRelabel,addressRename,rawConsRename,sucRelabel,zRelabel]

theorem inputsSubst {α β : Type} (f u c r d e l k : OTerm α) (ts : α → OTerm β) :
    (parsedApplicationInputs f u c r d e l k).subst (fun a => emb (ts a)) =
      parsedApplicationInputs (f.subst ts) (u.subst ts) (c.subst ts) (r.subst ts)
        (d.subst ts) (e.subst ts) (l.subst ts) (k.subst ts) := by
  simp only [parsedApplicationInputs,addressReports,arrowReports,conjunctionSubst,unarySubst,literalUnarySubst,
    eqnSubst,addressSubst,rawConsSubst,sucSubst,zSubst]

private theorem outputBodySubst {α β : Type} (least : Program 3) (c e raw y k : OTerm α) (ts : α → OTerm β) :
    (reportBody least c e raw y k).subst (fun a => emb (ts a)) =
      reportBody least (c.subst ts) (e.subst ts) (raw.subst ts) (y.subst ts) (k.subst ts) := by
  simp only [reportBody,conjunctionSubst,graph3Subst,sucSubst,eqnSubst,addressSubst]

theorem outputReportSubst {α β : Type} (least : Program 3) (c e raw y : OTerm α) (ts : α → OTerm β) :
    (outputReport least c e raw y).subst (fun a => emb (ts a)) =
      outputReport least (c.subst ts) (e.subst ts) (raw.subst ts) (y.subst ts) := by
  rw [reportUnfold,reportUnfold,existsSubst,liftedEmbedding]
  unfold reportBinder
  rw [outputBodySubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
