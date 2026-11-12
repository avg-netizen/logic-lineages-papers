module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
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
theorem unaryAt (raw parameter index child front first middle second suffix joined count : OTerm alpha) (psi : Formula alpha)
 (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw parameter)))
 (hfirst : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
 (hsecond : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
 (hc : Nonempty (Derivation body Delta (consGraph front first z)))
 (ht : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
 (happ : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index joined)))
 (firstCase : First body Delta psi raw parameter index child)
 (secondCase : Second body Delta psi raw parameter index child)
 (deletedCase : Deleted body Delta psi raw parameter index child) : Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalIndexedPrefixCasesProof.unaryCases body alpha Delta
   front first suffix joined count index child psi hc happ hl hb hv
 · intro beta j Theta hj hindex he
   have ha' := renameInto ha j Theta hj
   have hf' := renameInto hfirst j Theta hj
   simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ha' hf'
   have hchild := outputTransport OriginalHereditaryExpansion.firstJob (first.relabel j) (child.relabel j)
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
     (by obtain ⟨he⟩ := he; exact ⟨symm he⟩) hf'
   exact firstCase beta j Theta 1 (by omega) hj ha' hindex hchild
 · intro beta j Theta cutoff size hj hindex hlength hbound hlookup
   have ha' := renameInto ha j Theta hj
   have hd' := renameInto hd j Theta hj
   simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ha' hd'
   exact deletedCase beta j Theta 1 (suffix.relabel j) cutoff size (by omega) hj
     ha' hindex hd' hlength hbound hlookup

theorem binaryAt (raw parameter index child front first middle second suffix joined count : OTerm alpha) (psi : Formula alpha)
 (ha : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw parameter)))
 (hfirst : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
 (hsecond : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
 (hc : Nonempty (Derivation body Delta (consGraph front first middle)))
 (ht : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
 (happ : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index joined)))
 (firstCase : First body Delta psi raw parameter index child)
 (secondCase : Second body Delta psi raw parameter index child)
 (deletedCase : Deleted body Delta psi raw parameter index child) : Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalIndexedPrefixCasesProof.binaryCases body alpha Delta
   front first middle second suffix joined count index child psi hc ht happ hl hb hv
 · intro beta j Theta hj hindex he
   have ha' := renameInto ha j Theta hj
   have hf' := renameInto hfirst j Theta hj
   simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ha' hf'
   have hchild := outputTransport OriginalHereditaryExpansion.firstJob (first.relabel j) (child.relabel j)
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
     (by obtain ⟨he⟩ := he; exact ⟨symm he⟩) hf'
   exact firstCase beta j Theta 2 (by omega) hj ha' hindex hchild
 · intro beta j Theta hj hindex he
   have ha' := renameInto ha j Theta hj
   have hf' := renameInto hsecond j Theta hj
   simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ha' hf'
   have hchild := outputTransport OriginalHereditaryExpansion.secondJob (second.relabel j) (child.relabel j)
     (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
     (by obtain ⟨he⟩ := he; exact ⟨symm he⟩) hf'
   exact secondCase beta j Theta hj ha' hindex hchild
 · intro beta j Theta cutoff size hj hindex hlength hbound hlookup
   have ha' := renameInto ha j Theta hj
   have hd' := renameInto hd j Theta hj
   simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ha' hd'
   exact deletedCase beta j Theta 2 (suffix.relabel j) cutoff size (by omega) hj
     ha' hindex hd' hlength hbound hlookup

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupRowsProof
