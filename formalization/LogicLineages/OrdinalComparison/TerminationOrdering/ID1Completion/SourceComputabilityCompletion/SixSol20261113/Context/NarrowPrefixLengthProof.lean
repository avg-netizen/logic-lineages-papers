module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowPrefixLengthProof
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


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowPrefixLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowPrefixLengthProof
