module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalFiniteBlocksSubstitutionProof (renameIdentity)
open InternalSliceInductionSyntaxProof (eqnRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalRawExpansionLookupTargets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof (refl symm)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalInternalIndexedPrefixCasesTargets (bump)
open OriginalInternalRawExpansionLookupCallbacksProof
open InternalOriginalOrderSyntaxProof (orderRename)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
theorem actualCases : OriginalInternalRawExpansionLookupTargets.ActualCases := by
 intro body alpha Delta raw parameter jobs count index child psi hexp hl hb hv firstCase secondCase deletedCase
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply InternalAcceptanceSupportProof.programCompositionCases InternalApplicationValidityStackAppend.append
   ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs psi hexp
 intro beta j ys Theta hj happ hs
 let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hs
 have htuple : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have happend : Nonempty (Derivation body Theta
   (graph2 InternalApplicationValidityStackAppend.append (jobs.relabel j) (ys 0) (ys 1))) := by
   simpa only [graph2,htuple] using happ
 have hl' := renameInto hl j Theta hj
 have hb' := renameInto hb j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,lengthRename,Below,orderRename] at hl' hb' hv'
 exact OriginalInternalRawExpansionLookupQueryProof.atRows (raw.relabel j) (parameter.relabel j)
   (index.relabel j) (child.relabel j) (ys 0) (ys 1) (jobs.relabel j) (count.relabel j) (psi.relabel j)
   (hs 0) (hs 1) happend hl' hb' hv'
   (firstRename psi raw parameter index child firstCase j Theta hj)
   (secondRename psi raw parameter index child secondCase j Theta hj)
   (deletedRename psi raw parameter index child deletedCase j Theta hj)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
