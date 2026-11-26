module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountSupport
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowPrefixLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowCountRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add)
open InternalListCodecSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open NarrowPrefixLengthProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SixSol20261112.Runtime.ScheduleCountSupport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lengthSumTransport (arity count actual jobs : OTerm alpha)
 (he : Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn (add arity count) actual)))
 (hl : Nonempty (Derivation body Delta (lengthGraph actual jobs))) :
 Nonempty (Derivation body Delta (lengthGraph (add arity count) jobs)) := by
 obtain ⟨he⟩ := he
 exact outputTransport length actual (add arity count) (Fin.cons jobs Fin.elim0) ⟨symm he⟩ hl
theorem atChildren (input parameter front suffix out arity count first second middle : OTerm alpha)
 (hfirst : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first input parameter)))
 (hsecond : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second input parameter)))
 (hmiddle : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (harity : Nonempty (Derivation body Delta
   (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity input parameter)))
 (hsuffix : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (lengthGraph (add arity count) out)) := by
 apply OriginalHereditaryInternalExpansionArityCasesProof.childArityCases input parameter _
 · intro beta rho Theta hrho ha
   simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have harity' := renameInto harity rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,lengthRename] at hchildren' happend' harity' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hecount := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0))
     (arity.relabel rho) (SourceComputabilityFormulaSupportProof.numeral 0) xs harity' ha
   have hz := OriginalHereditaryInternalExpansionChildrenProof.otherRow 0 (by decide) (by decide)
     xs (front.relabel rho) ha hchildren'
   have he := valueUnique (OriginalRawSyntaxTransport.constant 2 0) (front.relabel rho) z xs hz (constantValue 0 xs)
   have happ := headTransport InternalApplicationValidityStackAppend.append (out.relabel rho) (front.relabel rho) z
     (Fin.cons (suffix.relabel rho) Fin.elim0) he happend'
   obtain ⟨heq⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover
     (out.relabel rho) (suffix.relabel rho) happ
   have hlen := headTransport length (count.relabel rho) (suffix.relabel rho) (out.relabel rho)
     Fin.elim0 ⟨symm heq⟩ hsuffix'
   exact lengthSumTransport _ _ _ _ (sumZero _ _ hecount) hlen
 · intro beta rho Theta hrho ha ha1
   simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
   have hfirst' := renameInto hfirst rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have harity' := renameInto harity rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,lengthRename] at hfirst' hchildren' happend' harity' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hecount := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0))
     (arity.relabel rho) (SourceComputabilityFormulaSupportProof.numeral 1) xs harity' ha
   have hc := OriginalHereditaryInternalExpansionChildrenProof.unaryCons xs (front.relabel rho) (first.relabel rho)
     ha hchildren' hfirst'
   have hlen := unaryLength (front.relabel rho) (first.relabel rho) (suffix.relabel rho)
     (out.relabel rho) (count.relabel rho) hc happend' hsuffix'
   exact lengthSumTransport _ _ _ _ (sumOne _ _ hecount) hlen
 · intro beta rho Theta hrho ha ha1
   simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
   have hfirst' := renameInto hfirst rho Theta hrho
   have hsecond' := renameInto hsecond rho Theta hrho
   have hmiddle' := renameInto hmiddle rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have harity' := renameInto harity rho Theta hrho
   have hsuffix' := renameInto hsuffix rho Theta hrho
   simp only [graph2Rename,consGraphRename,zRelabel,lengthRename]
     at hfirst' hsecond' hmiddle' hchildren' happend' harity' hsuffix'
   let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
   have hecount := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0))
     (arity.relabel rho) (SourceComputabilityFormulaSupportProof.numeral 2) xs harity' ha
   have hc := OriginalHereditaryInternalExpansionChildrenProof.binaryCons xs (front.relabel rho)
     (first.relabel rho) (second.relabel rho) (middle.relabel rho) ha hchildren' hfirst' hsecond' hmiddle'
   have hlen := binaryLength (front.relabel rho) (first.relabel rho) (middle.relabel rho)
     (second.relabel rho) (suffix.relabel rho) (out.relabel rho) (count.relabel rho) hc hmiddle' happend' hsuffix'
   exact lengthSumTransport _ _ _ _ (sumTwo _ _ hecount) hlen
theorem rowsExact (input parameter front suffix out arity count : OTerm alpha)
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (harity : Nonempty (Derivation body Delta
   (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity input)))
 (hsuffix : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (lengthGraph (add arity count) out)) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases input parameter _
 intro beta rho Theta first second middle hrho hf hs hm
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 have hc := renameInto hchildren rho Theta hrho
 have ha := renameInto happend rho Theta hrho
 have hn := renameInto harity rho Theta hrho
 have hl := renameInto hsuffix rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename] at hc ha hn hl
 let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hquery := arityAt (.projection 0) (arity.relabel rho) (input.relabel rho) xs (projectionValue 0 xs) hn
 exact atChildren (input.relabel rho) (parameter.relabel rho) (front.relabel rho) (suffix.relabel rho)
   (out.relabel rho) (arity.relabel rho) (count.relabel rho) first second middle hf hs hm hc ha hquery hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowCountRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowCountRowsProof
