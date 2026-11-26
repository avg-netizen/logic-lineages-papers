module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSquareRootArithmeticSupportProof (strictTrans)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeKeyChecks (exact_OpenRawConsBounds)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev priorKey (dom cod fn arg : OTerm α) : OTerm α := pairTerm (numeral 6) (packedBody [dom,cod,fn,arg])

private theorem measureArgs (raw : OTerm α) : ∀ i : Fin 3, Nonempty (Derivation body Γ (programGraph
    ((Fin.cons (.projection 0) (Fin.cons (constantZero 1) (Fin.cons (constantZero 1) Fin.elim0)) :
      Fin 3 → Program 1) i) ((![raw,z,z] : Fin 3 → OTerm α) i) ![raw])) := by
  intro i
  exact Fin.cases (projectionValue 0 ![raw])
    (Fin.cases (zeroConstantValue ![raw]) (Fin.cases (zeroConstantValue ![raw]) (fun j => Fin.elim0 j))) i

theorem projection (R : Program 4) (out raw : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (selectedMeasure R) out ![raw])) ↔
    Nonempty (Derivation body Γ (readRow R out raw)) := by
  let ps : Fin 3 → Program 1 :=
    Fin.cons (.projection 0) (Fin.cons (constantZero 1) (Fin.cons (constantZero 1) Fin.elim0))
  constructor
  · intro h
    exact compositionRecover (scratchRow (constantZero 2) R) ps out ![raw] ![raw,z,z] h (measureArgs raw)
  · intro h
    exact compositionValue (scratchRow (constantZero 2) R) ps out ![raw] ![raw,z,z] h (measureArgs raw)

theorem bothChildBounds (dom cod fn arg : OTerm α) :
    Nonempty (Derivation body Γ (ltF fn (auxiliaryTerm dom cod fn arg))) ∧
    Nonempty (Derivation body Γ (ltF arg (auxiliaryTerm dom cod fn arg))) := by
  let last := rawCons arg z
  let fields := rawCons fn last
  let codField := rawCons cod fields
  let domField := rawCons dom codField
  let parent := rawCons (numeral 6) domField
  have fieldToParent : Nonempty (Derivation body Γ (ltF fields parent)) :=
    strictTrans fields domField parent
      (strictTrans fields codField domField (exact_OpenRawConsBounds body α Γ cod fields).2
        (exact_OpenRawConsBounds body α Γ dom codField).2)
      (exact_OpenRawConsBounds body α Γ (numeral 6) domField).2
  exact ⟨strictTrans fn fields parent (exact_OpenRawConsBounds body α Γ fn last).1 fieldToParent,
    strictTrans arg fields parent
      (strictTrans arg last fields (exact_OpenRawConsBounds body α Γ arg z).1
        (exact_OpenRawConsBounds body α Γ fn last).2) fieldToParent⟩

structure NodeReports (body : Positive (Fin 1)) (Γ : List (Formula α)) (xs : Fin 4 → OTerm α)
    (parent fn arg : OTerm α) : Prop where
  key : Nonempty (Derivation body Γ (programGraph currentKey parent xs))
  shape : Nonempty (Derivation body Γ (programGraph shapeCheck (suc z) xs))
  fnField : Nonempty (Derivation body Γ (programGraph (childAt 2) fn xs))
  argField : Nonempty (Derivation body Γ (programGraph (childAt 3) arg xs))

theorem nodeReports (dom cod fn arg old : OTerm α) :
    NodeReports body Γ ![priorKey dom cod fn arg,old,z,z] (auxiliaryTerm dom cod fn arg) fn arg := by
  let prior := priorKey dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey parent xs)) :=
    unaryGraph .succ (.projection 0) parent prior xs (successorValue ![prior]) (projectionValue 0 xs)
  obtain ⟨shape,fields⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  exact ⟨key,unaryGraph termShape currentKey (suc z) parent xs shape key,
    unaryGraph (field 2) currentKey fn parent xs fields.2.2.1 key,
    unaryGraph (field 3) currentKey arg parent xs fields.2.2.2.1 key⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
