module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupQueryProof
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
theorem atRows (raw parameter index child front suffix joined count : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index joined)))
 (firstCase : First body Delta psi raw parameter index child)
 (secondCase : Second body Delta psi raw parameter index child)
 (deletedCase : Deleted body Delta psi raw parameter index child) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases raw parameter psi
 intro beta j Theta first second middle hj hf hs ht
 have hc' := renameInto hc j Theta hj
 have hd' := renameInto hd j Theta hj
 have ha' := renameInto ha j Theta hj
 have hl' := renameInto hl j Theta hj
 have hb' := renameInto hb j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,lengthRename,Below,orderRename] at hc' hd' ha' hl' hb' hv'
 exact OriginalInternalRawExpansionLookupDispatchProof.atKnown
   (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) (front.relabel j)
   first middle second (suffix.relabel j) (joined.relabel j) (count.relabel j) (psi.relabel j)
   hf hs ht hc' hd' ha' hl' hb' hv'
   (firstRename psi raw parameter index child firstCase j Theta hj)
   (secondRename psi raw parameter index child secondCase j Theta hj)
   (deletedRename psi raw parameter index child deletedCase j Theta hj)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupQueryProof
