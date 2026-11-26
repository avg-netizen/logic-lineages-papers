module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryInternalFinitePrefixAppendProof
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def LengthView (count out : OTerm alpha) : Formula alpha :=
 lengthGraph count out ⊔ (lengthGraph (suc count) out ⊔ lengthGraph (suc (suc count)) out)

theorem lengthViewRename {beta : Type} (count out : OTerm alpha) (rho : alpha → beta) :
 (LengthView count out).relabel rho = LengthView (count.relabel rho) (out.relabel rho) := by
 simp only [LengthView,OriginalRawSyntaxTransportInternalConstructorArityProof.orRename,lengthRename,sucRelabel]

theorem unaryLength (front first suffix out count : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front first z)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (lengthGraph (suc count) out)) :=
 lengthCons out first suffix count (unaryAppended front first suffix out hc ha) hl

theorem binaryLength (front first middle second suffix out count : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front first middle)))
 (ht : Nonempty (Derivation body Delta (consGraph middle second z)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (lengthGraph (suc (suc count)) out)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons second (Fin.cons suffix Fin.elim0)
 apply programCases InternalListCodec.consCode xs _
 intro beta rho Theta result hrho hcons
 simp only [lengthRename,sucRelabel]
 let xx : Fin 2 → OTerm beta := Fin.cons (second.relabel rho) (Fin.cons (suffix.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hcons
 have hc' := renameInto hc rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 simp only [consGraphRename,zRelabel,graph2Rename,lengthRename] at hc' ht' ha' hl'
 have hout := binaryAppended (front.relabel rho) (first.relabel rho) (middle.relabel rho)
   (second.relabel rho) (suffix.relabel rho) result (out.relabel rho) hc' ht' hcons ha'
 exact lengthCons (out.relabel rho) (first.relabel rho) result (suc (count.relabel rho)) hout
   (lengthCons result (second.relabel rho) (suffix.relabel rho) (count.relabel rho) hcons hl')

theorem atChildren (input parameter front suffix out count first second middle : OTerm alpha)
 (hfirst : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first input parameter)))
 (hsecond : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second input parameter)))
 (hmiddle : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hsuffix : Nonempty (Derivation body Delta (lengthGraph count suffix))) : Nonempty (Derivation body Delta (LengthView count out)) := by
 apply OriginalHereditaryInternalExpansionArityCasesProof.childArityCases input parameter _
 · intro beta rho Theta hrho ha
   rw [lengthViewRename]
   have hfirst' := renameInto hfirst rho Theta hrho
   have hsecond' := renameInto hsecond rho Theta hrho
   have hmiddle' := renameInto hmiddle rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,consGraphRename,zRelabel,lengthRename] at hfirst' hsecond' hmiddle' hchildren' happend' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hz := OriginalHereditaryInternalExpansionChildrenProof.otherRow 0 (by decide) (by decide) xs (front.relabel rho) ha hchildren'
   have he := valueUnique (OriginalRawSyntaxTransport.constant 2 0) (front.relabel rho) z xs hz (constantValue 0 xs)
   have happ := headTransport InternalApplicationValidityStackAppend.append (out.relabel rho) (front.relabel rho) z
     (Fin.cons (suffix.relabel rho) Fin.elim0) he happend'
   obtain ⟨heq⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover (out.relabel rho) (suffix.relabel rho) happ
   obtain ⟨hlen⟩ := headTransport length (count.relabel rho) (suffix.relabel rho) (out.relabel rho) Fin.elim0 ⟨symm heq⟩ hsuffix'
   exact ⟨orLeft hlen⟩
 · intro beta rho Theta hrho ha ha1
   rw [lengthViewRename]
   have hfirst' := renameInto hfirst rho Theta hrho
   have hsecond' := renameInto hsecond rho Theta hrho
   have hmiddle' := renameInto hmiddle rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,consGraphRename,zRelabel,lengthRename] at hfirst' hsecond' hmiddle' hchildren' happend' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hc := OriginalHereditaryInternalExpansionChildrenProof.unaryCons xs (front.relabel rho) (first.relabel rho) ha hchildren' hfirst'
   obtain ⟨hlen⟩ := unaryLength (front.relabel rho) (first.relabel rho) (suffix.relabel rho) (out.relabel rho) (count.relabel rho) hc happend' hsuffix'
   exact ⟨orRight (orLeft hlen)⟩
 · intro beta rho Theta hrho ha ha1
   rw [lengthViewRename]
   have hfirst' := renameInto hfirst rho Theta hrho
   have hsecond' := renameInto hsecond rho Theta hrho
   have hmiddle' := renameInto hmiddle rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,consGraphRename,zRelabel,lengthRename] at hfirst' hsecond' hmiddle' hchildren' happend' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hc := OriginalHereditaryInternalExpansionChildrenProof.binaryCons xs (front.relabel rho)
     (first.relabel rho) (second.relabel rho) (middle.relabel rho) ha hchildren' hfirst' hsecond' hmiddle'
   obtain ⟨hlen⟩ := binaryLength (front.relabel rho) (first.relabel rho) (middle.relabel rho)
     (second.relabel rho) (suffix.relabel rho) (out.relabel rho) (count.relabel rho) hc hmiddle' happend' hsuffix'
   exact ⟨orRight (orRight hlen)⟩

theorem rowsLengthView (input parameter front suffix out count : OTerm alpha)
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hsuffix : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (LengthView count out)) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases input parameter _
 intro beta rho Theta first second middle hrho hf hs hm
 rw [lengthViewRename]
 have hc := renameInto hchildren rho Theta hrho
 have ha := renameInto happend rho Theta hrho
 have hl := renameInto hsuffix rho Theta hrho
 simp only [graph2Rename,lengthRename] at hc ha hl
 exact atChildren (input.relabel rho) (parameter.relabel rho) (front.relabel rho) (suffix.relabel rho)
   (out.relabel rho) (count.relabel rho) first second middle hf hs hm hc ha hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthRowsProof
