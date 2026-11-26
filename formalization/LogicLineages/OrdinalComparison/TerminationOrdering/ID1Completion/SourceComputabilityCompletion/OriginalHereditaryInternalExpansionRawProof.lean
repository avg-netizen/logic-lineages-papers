module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionBinaryAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawLookupDecrease (parent child parentRaw rawChild input parameter window gamma W V jobs count index : OTerm alpha)
 (hexp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs input parameter)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index jobs))) : Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 apply InternalAcceptanceSupportProof.programCompositionCases InternalApplicationValidityStackAppend.append
   ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs _ hexp
 intro beta rho ys Theta hrho happ hs
 simp only [orderRename]
 let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hs
 have htuple : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have happend : Nonempty (Derivation body Theta
   (graph2 InternalApplicationValidityStackAppend.append (jobs.relabel rho) (ys 0) (ys 1))) := by
   simpa only [graph2,htuple] using happ
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hb' := renameInto hb rho Theta hrho
 have hlookup' := renameInto hlookup rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename] at hp' hc' hr' hparam' hw' hv' hl' hb' hlookup'
 exact OriginalHereditaryInternalExpansionRowsProof.atRows
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
   (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   (W.relabel rho) (V.relabel rho) (ys 0) (ys 1) (jobs.relabel rho) (count.relabel rho) (index.relabel rho)
   hp' hc' hr' hparam' hw' hv' (hs 0) (hs 1) happend hl' hb' hlookup'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
