module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem withHyp {phi : Formula alpha} (h : Nonempty (Derivation body Delta phi)) (p : Formula alpha) :
    Nonempty (Derivation body (p :: Delta) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨InternalBetaTotalityProof.addHyp h p⟩

@[simp] theorem fuelRename {beta : Type} (count code : OTerm alpha) (j : alpha → beta) :
    (WorkFuelGraph count code).relabel j = WorkFuelGraph (count.relabel j) (code.relabel j) :=
  graph1Rename workFuel count code j

/-- The only positive contribution is the selected raw payload plus one. -/
theorem frameValue (frame raw parameter payload : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (FrameGraph frame raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Delta (graph1 frameFuel (suc payload) frame)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons frame Fin.elim0
  have hl := unaryValue InternalUnpair.left (.projection 0) raw frame xs
    (pairLeft frame raw parameter hf) (projectionValue 0 xs)
  have hr := unaryValue InternalUnpair.right (leftOf (.projection 0)) payload raw xs hp hl
  exact unaryValue .succ (rightOf (leftOf (.projection 0))) (suc payload) payload xs
    (InternalControlGraphSupportProof.successorValue (Fin.cons payload Fin.elim0)) hr

 theorem stepValue (frame amount tail : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 frameFuel amount frame))) :
    Nonempty (Derivation body Delta (graph2 workFuelStep (add amount tail) frame tail)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons frame (Fin.cons tail Fin.elim0)
  exact binaryValue InternalArithmeticPrograms.addition
    (.composition frameFuel (fun _ : Fin 1 => .projection 0)) (.projection 1)
    (add amount tail) amount tail xs (InternalArithmeticProgramsSupportProof.additionValue amount tail)
    (unaryValue frameFuel (.projection 0) amount frame xs hf (projectionValue 0 xs))
    (projectionValue 1 xs)

 theorem nilValue : Nonempty (Derivation body Delta (WorkFuelGraph z z)) :=
  InternalRawListRecursionProof.nilValue .zero workFuelStep z Fin.elim0 (zeroValue Fin.elim0)

 theorem nilRecover (out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (WorkFuelGraph out z))) :
    Nonempty (Derivation body Delta (eqn out z)) :=
  valueUnique workFuel out z (Fin.cons z Fin.elim0) h nilValue

 theorem consValue (code frame rest amount tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons code frame rest)))
    (hf : Nonempty (Derivation body Delta (graph1 frameFuel amount frame)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (add amount tail) code)) :=
  InternalRawListRecursionProof.consValue .zero workFuelStep code frame rest tail
    (add amount tail) Fin.elim0 hc ht (stepValue frame amount tail hf)

 theorem consRecover (code frame rest amount tail out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons code frame rest)))
    (hf : Nonempty (Derivation body Delta (graph1 frameFuel amount frame)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (ho : Nonempty (Derivation body Delta (WorkFuelGraph out code))) :
    Nonempty (Derivation body Delta (eqn out (add amount tail))) :=
  valueUnique workFuel out (add amount tail) (Fin.cons code Fin.elim0) ho
    (consValue code frame rest amount tail hc hf ht)

 theorem graphIffValue (out value code : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (WorkFuelGraph value code))) :
    Nonempty (Derivation body Delta ((WorkFuelGraph out code).iff (equal out value))) := by
  let P := WorkFuelGraph out code
  let Q := equal out value
  have hf : Nonempty (Derivation body (P :: Delta) Q) := by
    change Nonempty (Derivation body (P :: Delta) (equal out value))
    rw [equalEqn]
    exact valueUnique workFuel out value (Fin.cons code Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv P)
  have hb : Nonempty (Derivation body (Q :: Delta) P) := by
    have he : Derivation body (Q :: Delta) (eqn out value) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport workFuel value out (Fin.cons code Fin.elim0) ⟨symm he⟩
      (withHyp hv Q)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
