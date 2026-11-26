module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupDispatchProof
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
theorem atKnown (raw parameter index child front first middle second suffix joined count : OTerm alpha) (psi : Formula alpha)
 (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
 (ht : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index joined)))
 (firstCase : First body Delta psi raw parameter index child)
 (secondCase : Second body Delta psi raw parameter index child)
 (deletedCase : Deleted body Delta psi raw parameter index child) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalExpansionArityCasesProof.childArityCases raw parameter psi
 · intro beta j Theta hj harity
   have hf' := renameInto hf j Theta hj
   have hs' := renameInto hs j Theta hj
   have ht' := renameInto ht j Theta hj
   have hc' := renameInto hc j Theta hj
   have hd' := renameInto hd j Theta hj
   have ha' := renameInto ha j Theta hj
   have hl' := renameInto hl j Theta hj
   have hb' := renameInto hb j Theta hj
   have hv' := renameInto hv j Theta hj
   simp only [graph2Rename,consGraphRename,lengthRename,Below,orderRename,zRelabel] at hf' hs' ht' hc' hd' ha' hl' hb' hv'
   have firstCase' := firstRename psi raw parameter index child firstCase j Theta hj
   have secondCase' := secondRename psi raw parameter index child secondCase j Theta hj
   have deletedCase' := deletedRename psi raw parameter index child deletedCase j Theta hj
   have hz := OriginalHereditaryInternalExpansionChildrenProof.otherRow 0 (by decide) (by decide)
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (front.relabel j) harity hc'
   have he := valueUnique (OriginalRawSyntaxTransport.constant 2 0) (front.relabel j) z
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hz (constantValue 0 (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
   have happ := headTransport InternalApplicationValidityStackAppend.append (joined.relabel j) (front.relabel j) z
     (Fin.cons (suffix.relabel j) Fin.elim0) he ha'
   have hfields := OriginalHereditaryInternalFinitePrefixZeroProof.zeroSuffix (suffix.relabel j) (joined.relabel j)
     (count.relabel j) (index.relabel j) (child.relabel j) happ hl' hv'
   have hh := deletedCase' beta id Theta 0 (suffix.relabel j) (index.relabel j) (count.relabel j)
     (by omega) (by intro f hf; simpa only [renameIdentity] using hf)
     (by simpa only [Term.relabel_id] using harity)
     (by simpa only [Term.relabel_id,bump] using (Nonempty.intro (refl (index.relabel j)) : Nonempty (Derivation body Theta (eqn (index.relabel j) (index.relabel j)))))
     (by simpa only [Term.relabel_id] using hd') hfields.1 hb'
     (by simpa only [Term.relabel_id] using hfields.2)
   simpa only [renameIdentity] using hh
 · intro beta j Theta hj harity hunused
   have hf' := renameInto hf j Theta hj
   have hs' := renameInto hs j Theta hj
   have ht' := renameInto ht j Theta hj
   have hc' := renameInto hc j Theta hj
   have hd' := renameInto hd j Theta hj
   have ha' := renameInto ha j Theta hj
   have hl' := renameInto hl j Theta hj
   have hb' := renameInto hb j Theta hj
   have hv' := renameInto hv j Theta hj
   simp only [graph2Rename,consGraphRename,lengthRename,Below,orderRename,zRelabel] at hf' hs' ht' hc' hd' ha' hl' hb' hv'
   have firstCase' := firstRename psi raw parameter index child firstCase j Theta hj
   have secondCase' := secondRename psi raw parameter index child secondCase j Theta hj
   have deletedCase' := deletedRename psi raw parameter index child deletedCase j Theta hj
   have hfront := OriginalHereditaryInternalExpansionChildrenProof.unaryCons
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (front.relabel j) (first.relabel j) harity hc' hf' 
   exact OriginalInternalRawExpansionLookupRowsProof.unaryAt
     (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) (front.relabel j) (first.relabel j) (middle.relabel j) (second.relabel j) (suffix.relabel j) (joined.relabel j) (count.relabel j) (psi.relabel j)
     harity hf' hs' hfront ht' hd' ha' hl' hb' hv' firstCase' secondCase' deletedCase'
 · intro beta j Theta hj harity hunused
   have hf' := renameInto hf j Theta hj
   have hs' := renameInto hs j Theta hj
   have ht' := renameInto ht j Theta hj
   have hc' := renameInto hc j Theta hj
   have hd' := renameInto hd j Theta hj
   have ha' := renameInto ha j Theta hj
   have hl' := renameInto hl j Theta hj
   have hb' := renameInto hb j Theta hj
   have hv' := renameInto hv j Theta hj
   simp only [graph2Rename,consGraphRename,lengthRename,Below,orderRename,zRelabel] at hf' hs' ht' hc' hd' ha' hl' hb' hv'
   have firstCase' := firstRename psi raw parameter index child firstCase j Theta hj
   have secondCase' := secondRename psi raw parameter index child secondCase j Theta hj
   have deletedCase' := deletedRename psi raw parameter index child deletedCase j Theta hj
   have hfront := OriginalHereditaryInternalExpansionChildrenProof.binaryCons
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (front.relabel j) (first.relabel j) (second.relabel j) (middle.relabel j) harity hc' hf' hs' ht'
   exact OriginalInternalRawExpansionLookupRowsProof.binaryAt
     (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) (front.relabel j) (first.relabel j) (middle.relabel j) (second.relabel j) (suffix.relabel j) (joined.relabel j) (count.relabel j) (psi.relabel j)
     harity hf' hs' hfront ht' hd' ha' hl' hb' hv' firstCase' secondCase' deletedCase'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupDispatchProof
