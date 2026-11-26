module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalNumericListSort
open OriginalNumericListSortOriginalDefinitions OriginalNumericListSortOriginalSyntaxProof OriginalNumericListSortOriginalBindingProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairedLeft {k : Nat} (p q : Program k) (state first : OTerm alpha) (xs : Fin k → OTerm alpha)
 (hp : Nonempty (Derivation body Delta (programGraph (.composition InternalPairing.pairing ![p,q]) state xs)))
 (hf : Nonempty (Derivation body Delta (programGraph p first xs))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left first state)) := by
 apply programCompositionCases InternalPairing.pairing ![p,q] state xs _ hp
 intro beta rho ys Theta hrho hpair hvalues
 simp only [graph1Rename]
 have hf' := renameInto hf rho Theta hrho
 rw [programRename] at hf'
 have he := valueUnique p (ys 0) (first.relabel rho) (fun i => (xs i).relabel rho) (hvalues 0) hf'
 have hv : ys = (![ys 0,ys 1] : Fin 2 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hv] at hpair
 exact outputTransport InternalUnpair.left (ys 0) (first.relabel rho) ![state.relabel rho] he
   (pairLeft (state.relabel rho) (ys 0) (ys 1) hpair)

theorem zeroCore (x state : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (fields z x state))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left z state)) := by
 have hb := InternalRawListRecursionProof.nilRecover insertBase insertStep state (Fin.cons x Fin.elim0) hs
 exact pairedLeft InternalRawListRecursion.zero
   (.composition InternalListCodec.consCode ![.projection 0,InternalRawListRecursion.zero])
   state z (Fin.cons x Fin.elim0) hb (InternalRawListRecursionSupportProof.constantZero (Fin.cons x Fin.elim0))

theorem stepLeft (raw head tail x state previous inserted : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (hs : Nonempty (Derivation body Delta (graph3 insertStep state head previous x))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left raw state)) := by
 have ho := OriginalNumericListSortValueProof.originalConsValue head tail inserted previous raw x hp hc
 exact pairedLeft originalCons
   (InternalAcceptance.branch (.composition InternalLessThan.ltTest ![.projection 0,.projection 2]) beforeCons afterCons)
   state raw ![head,previous,x] hs ho

theorem consAtPrevious (raw head tail x state previous : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 insertState previous tail x)))
 (hs : Nonempty (Derivation body Delta (graph3 insertStep state head previous x))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left raw state)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hl := belowRawApply raw tail x previous hi hb ht
 apply programCases InternalUnpair.right ![previous] _
 intro beta rho Theta inserted hrho hr
 rw [unaryVectorRename] at hr
 simp only [graph1Rename]
 have hl' := renameInto hl rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 simp only [graph1Rename] at hl'
 simp only [graph2Rename] at hc'
 simp only [graph3Rename] at hs'
 have hp := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta
   (previous.relabel rho) (tail.relabel rho) inserted) (andIntro hl' hr)
 exact stepLeft (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho)
   (state.relabel rho) (previous.relabel rho) inserted hc' hp hs'

theorem consCore (raw head tail x state : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hs : Nonempty (Derivation body Delta (fields raw x state))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left raw state)) := by
 have h := InternalRawListRecursionProof.consForward insertBase insertStep raw head tail state (Fin.cons x Fin.elim0) hc hs
 apply InternalRawListRecursionProof.stepCases insertBase insertStep state head tail (Fin.cons x Fin.elim0) _ h
 intro beta rho Theta previous hrho ht hstep
 simp only [graph1Rename]
 simp only [consTermRename,emptyRename] at ht hstep
 have hi' := renameInto hi rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [graph2Rename] at hc'
 exact consAtPrevious (raw.relabel rho) (head.relabel rho) (tail.relabel rho)
   (x.relabel rho) (state.relabel rho) previous hi' hc' ht hstep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalCoreProof
