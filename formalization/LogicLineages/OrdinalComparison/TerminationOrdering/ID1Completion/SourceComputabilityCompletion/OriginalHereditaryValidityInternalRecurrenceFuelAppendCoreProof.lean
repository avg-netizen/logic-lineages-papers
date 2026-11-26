module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem rowApply (front suffix joined first second : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (fuelAppendRow front)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first front)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (add first second) joined)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (fuelAppendBody front)
    (fun i => emb (![suffix,joined,first,second] i)) hrow
  rw [fuelAppendWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro ha (andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

 theorem zeroCore (suffix joined first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined z suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first z)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (add first second) joined)) := by
  obtain ⟨hj⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined suffix ha
  obtain ⟨hz⟩ := nilRecover first hf
  have h := headTransport workFuel second suffix joined Fin.elim0 ⟨symm hj⟩ hs
  have he := trans (InternalMultiplicationLawsProof.congAddRight second hz) (leftZero second)
  exact outputTransport workFuel second (add first second) (Fin.cons joined Fin.elim0) ⟨symm he⟩ h

 theorem consCore (front frame rest suffix joined first second : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (fuelAppendRow rest)))
    (hc : Nonempty (Derivation body Delta (WorkCons front frame rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first front)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (add first second) joined)) := by
  let qs : Fin 3 → Program 3 := ![
    .composition InternalApplicationValidityStackAppend.append ![.projection 1,.projection 2],
    .composition workFuel (fun _ : Fin 1 => .projection 1),
    .composition frameFuel (fun _ : Fin 1 => .projection 0)]
  let xs : Fin 3 → OTerm alpha := Fin.cons frame (Fin.cons rest (Fin.cons suffix Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [fuelRename,InternalOriginalOrderSyntaxProof.addRelabel]
  simp only [xs,consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Theta hj
  rw [fuelAppendRename] at hrow'
  have hc' := renameInto hc j Theta hj
  simp only [WorkCons,graph2Rename] at hc'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  have hs' := renameInto hs j Theta hj
  rw [fuelRename] at hs'
  let xx : Fin 3 → OTerm beta := Fin.cons (frame.relabel j)
    (Fin.cons (rest.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0))
  have ht := binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) (.projection 2)
    (ys 0) (rest.relabel j) (suffix.relabel j) xx (hq 0)
    (projectionValue 1 xx) (projectionValue 2 xx)
  have htail := unaryRecover workFuel (.projection 1) (ys 1) (rest.relabel j) xx
    (hq 1) (projectionValue 1 xx)
  have hframe := unaryRecover frameFuel (.projection 0) (ys 2) (frame.relabel j) xx
    (hq 2) (projectionValue 0 xx)
  have hjoined := InternalApplicationValidityStackAppendListProof.consForward
    (front.relabel j) (frame.relabel j) (rest.relabel j) (suffix.relabel j)
    (ys 0) (joined.relabel j) hc' ht ha'
  have htFuel := rowApply (rest.relabel j) (suffix.relabel j) (ys 0) (ys 1)
    (second.relabel j) hrow' ht htail hs'
  obtain ⟨hfirst⟩ := consRecover (front.relabel j) (frame.relabel j) (rest.relabel j)
    (ys 2) (ys 1) (first.relabel j) hc' hframe htail hf'
  have hvalue := consValue (joined.relabel j) (frame.relabel j) (ys 0)
    (ys 2) (add (ys 1) (second.relabel j)) hjoined hframe htFuel
  have he := trans (symm (associativity (ys 2) (ys 1) (second.relabel j)))
    (InternalMultiplicationLawsProof.congAddRight (second.relabel j) (symm hfirst))
  exact outputTransport workFuel (add (ys 2) (add (ys 1) (second.relabel j)))
    (add (first.relabel j) (second.relabel j)) (Fin.cons (joined.relabel j) Fin.elim0)
    ⟨he⟩ hvalue

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendCoreProof
