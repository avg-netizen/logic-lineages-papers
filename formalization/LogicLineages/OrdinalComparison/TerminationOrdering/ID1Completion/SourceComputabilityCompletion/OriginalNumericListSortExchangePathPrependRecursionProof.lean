module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependRecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRawListRecursion InternalRawListRecursionProof InternalRawListRecursionSyntaxProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalNumericListSortExchangePathPrepend
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] mapPath entryLift

theorem atZero (value : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 mapPath z z value)) := by
 obtain ⟨he⟩ := actualOriginalListRecursionZero body 1 (zero : Program 1) mapStep alpha z (Fin.cons value Fin.elim0)
 have hz : Nonempty (Derivation body Delta (programGraph (zero : Program 1) z (Fin.cons value Fin.elim0))) := constantZeroValue (Fin.cons value Fin.elim0)
 have hv : Nonempty (Derivation body Delta (recGraph (zero : Program 1) mapStep z z (Fin.cons value Fin.elim0))) := closedApply ⟨Derivation.conjunctionRight he⟩ hz
 simpa only [mapPath,graph2,recGraph] using hv

theorem consBackward (raw entry rest value mappedEntry mappedRest out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw entry rest)))
 (he : Nonempty (Derivation body Delta (graph2 entryLift mappedEntry entry value)))
 (hr : Nonempty (Derivation body Delta (graph2 mapPath mappedRest rest value)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedEntry mappedRest))) :
 Nonempty (Derivation body Delta (graph2 mapPath out raw value)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons entry (Fin.cons mappedRest (Fin.cons value Fin.elim0))
 have he' := binaryValue entryLift (.projection 0) (.projection 2) mappedEntry entry value xs he
   (projectionValue 0 xs) (projectionValue 2 xs)
 have hs : Nonempty (Derivation body Delta (graph3 mapStep out entry mappedRest value)) :=
   binaryValue InternalListCodec.consCode (.composition entryLift ![.projection 0,.projection 2])
     (.projection 1) out mappedEntry mappedRest xs ho he' (projectionValue 1 xs)
 have hrView : Nonempty (Derivation body Delta (recGraph (zero : Program 1) mapStep mappedRest rest (Fin.cons value Fin.elim0))) := by
   simpa only [mapPath,graph2,recGraph] using hr
 obtain ⟨hr⟩ := hrView
 obtain ⟨hs⟩ := hs
 have hex : Nonempty (Derivation body Delta (consStep (zero : Program 1) mapStep out entry rest (Fin.cons value Fin.elim0))) := by
   apply Nonempty.intro
   apply Derivation.existentialIntroduction (emb mappedRest)
   rw [consStepInstance]
   exact Derivation.conjunctionIntroduction hr hs
 obtain ⟨heq⟩ := closedApply (actualOriginalListRecursionCons body 1 (zero : Program 1) mapStep
   alpha raw entry rest out (Fin.cons value Fin.elim0)) hc
 obtain ⟨hex⟩ := hex
 have hv : Nonempty (Derivation body Delta (recGraph (zero : Program 1) mapStep out raw (Fin.cons value Fin.elim0))) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hex⟩
 simpa only [mapPath,graph2,recGraph] using hv

theorem consForward (raw entry rest value mappedEntry mappedRest out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw entry rest)))
 (he : Nonempty (Derivation body Delta (graph2 entryLift mappedEntry entry value)))
 (hr : Nonempty (Derivation body Delta (graph2 mapPath mappedRest rest value)))
 (ho : Nonempty (Derivation body Delta (graph2 mapPath out raw value))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedEntry mappedRest)) := by
 apply OriginalTypedArgumentObservationsAccumulatorQueryProof.binaryCases InternalListCodec.consCode mappedEntry mappedRest _
 intro beta j Theta result hj hresult
 rw [graph2Rename]
 have hc' := renameInto hc j Theta hj
 have he' := renameInto he j Theta hj
 have hr' := renameInto hr j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [graph2Rename] at hc' he' hr' ho'
 have hm := consBackward (raw.relabel j) (entry.relabel j) (rest.relabel j) (value.relabel j)
   (mappedEntry.relabel j) (mappedRest.relabel j) result hc' he' hr' hresult
 exact outputTransport InternalListCodec.consCode result (out.relabel j)
   (Fin.cons (mappedEntry.relabel j) (Fin.cons (mappedRest.relabel j) Fin.elim0))
   (valueUnique mapPath result (out.relabel j) (Fin.cons (raw.relabel j) (Fin.cons (value.relabel j) Fin.elim0)) hm ho') hresult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependRecursionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependRecursionProof
