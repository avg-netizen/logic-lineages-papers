module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEmptyExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalBottomEmptyExpansionProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof (arityTag3)
open OriginalHereditaryInternalVisitSupportProof
open InternalApplicationValidityStackAppendListProof (appendZeroValue)
open OriginalContextInsertionLengthProof (lengthZero)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem coordinates {n : Nat} (q : Program n) (xs : Fin n → OTerm alpha)
 (job typed typ rawJob raw parameter : OTerm alpha)
 (hq : Nonempty (Derivation body Delta (programGraph q job xs)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter))) :
 Nonempty (Derivation body Delta (programGraph (leftOf q) z xs)) ∧
 Nonempty (Derivation body Delta (programGraph (leftOf (rightOf q)) typ xs)) ∧
 Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf q))) raw xs)) ∧
 Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf q))) parameter xs)) := by
 have hy := unaryValue InternalUnpair.right q typed job xs (pairRight job z typed hj) hq
 have hraw := unaryValue InternalUnpair.right (rightOf q) rawJob typed xs (pairRight typed typ rawJob ht) hy
 exact ⟨unaryValue InternalUnpair.left q z job xs (pairLeft job z typed hj) hq,
   unaryValue InternalUnpair.left (rightOf q) typ typed xs (pairLeft typed typ rawJob ht) hy,
   unaryValue InternalUnpair.left (rightOf (rightOf q)) raw rawJob xs (pairLeft rawJob raw parameter hr) hraw,
   unaryValue InternalUnpair.right (rightOf (rightOf q)) parameter rawJob xs (pairRight rawJob raw parameter hr) hraw⟩

theorem annotatedZero (job typed typ rawJob raw parameter c : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c z))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion z job)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 obtain ⟨hrole,htyp,hraw,hparam⟩ := coordinates (.projection 0) xs job typed typ rawJob raw parameter (projectionValue 0 xs) hj ht hr
 have he := binaryValue OriginalHereditaryExpansion.expansion (leftOf OriginalHereditaryAnnotatedExpansion.originalJob)
   (rightOf OriginalHereditaryAnnotatedExpansion.originalJob) z raw parameter xs (rawZero raw typ parameter c hb hp) hraw hparam
 let ys : Fin 4 → OTerm alpha := Fin.cons z (Fin.cons typ (Fin.cons raw (Fin.cons z Fin.elim0)))
 apply compositionValue OriginalHereditaryAnnotatedExpansion.decorateAll _ z xs ys (allZero z typ raw)
 intro i
 refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) i
 · exact hrole
 · exact htyp
 · exact hraw
 · exact he

theorem visit (R : Program 2) (raw typ c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c z)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visitFrame z job)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work z)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts z z)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing middle returnWork z)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visitFrame z)))
 (hret : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnWork frame z))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) middle input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hparent := parentGraph input work z visitFrame z job hs hw hv
 obtain ⟨hrole,htyp,hraw,hparam⟩ := coordinates OriginalHereditaryAnnotatedVisit.parent xs job typed typ rawJob raw parameter hparent hj ht hr
 have htag := unaryValue InternalUnpair.left OriginalHereditaryAnnotatedVisit.raw (numeral 3) raw xs (pairLeft raw (numeral 3) typ hb) hraw
 have hary := arityTag3 OriginalHereditaryAnnotatedVisit.raw xs htag
 have hgamma := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedVisit.parameter z parameter xs (pairRight parameter c z hp) hparam
 have hlen := unaryValue OriginalContextInsertion.length (rightOf OriginalHereditaryAnnotatedVisit.parameter) z z xs lengthZero hgamma
 have hcounts := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.arityOf OriginalHereditaryAnnotatedVisit.raw)
   (.composition OriginalContextInsertion.length (fun _ : Fin 1 => rightOf OriginalHereditaryAnnotatedVisit.parameter)) counts z z xs hc hary hlen
 have hpayload := binaryValue InternalPairing.pairing OriginalHereditaryAnnotatedVisit.parent _ payload job counts xs hpay hparent hcounts
 have hframe := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 1) _ frame (numeral 1) payload xs hf (constantValue 1 xs) hpayload
 have hexpanded : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.expanded z input)) :=
   unaryValue OriginalHereditaryAnnotatedExpansion.expansion OriginalHereditaryAnnotatedVisit.parent z job xs
     (annotatedZero job typed typ rawJob raw parameter c hj ht hr hb hp) hparent
 have htagged := unaryValue OriginalHereditaryVisitScheduler.tagVisits OriginalHereditaryAnnotatedVisit.expanded z z xs
   OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagNil hexpanded
 have hrest := restGraph input work z visitFrame z hs hw
 have hreturn := binaryValue InternalListCodec.consCode OriginalHereditaryAnnotatedVisit.returnFrame OriginalHereditaryAnnotatedVisit.rest returnWork frame z xs hret hframe hrest
 have hscheduled := binaryValue InternalApplicationValidityStackAppend.append
   (.composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => OriginalHereditaryAnnotatedVisit.expanded))
   (consOf OriginalHereditaryAnnotatedVisit.returnFrame OriginalHereditaryAnnotatedVisit.rest) returnWork z returnWork xs (appendZeroValue returnWork) htagged hreturn
 exact control R input work z visitFrame z job middle hs hw hv
   (binaryValue InternalPairing.pairing OriginalHereditaryAnnotatedVisit.scheduled OriginalHereditaryAnnotatedVisit.results middle returnWork z xs hm hscheduled (resultsGraph input work z hs))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomVisitProof
