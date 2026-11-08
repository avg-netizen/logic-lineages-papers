module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationCarryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationTargets
open InternalParameterizedNumericIterationSyntaxProof InternalParameterizedNumericIterationBridgeProof
open InternalParameterizedNumericIterationCarryProof InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem zeroValue (P : Program 2) (value parameter : OTerm α) :
    Nonempty (Derivation body Gamma (repeatGraph P value OrdinaryArithmetic.zeroTerm value parameter)) := by
  apply pairValuesCases parameter (fun _ : Fin 1 => value) _
  intro β j Delta states hj hs
  simp only [parameterRepeatRename, zRelabel]
  exact runValue P (value.relabel j) OrdinaryArithmetic.zeroTerm (value.relabel j)
    (parameter.relabel j) (states 0) (states 0) (hs 0) (hs 0)
    (InternalNumericIterationSupportProof.repeatZeroValue (carryP P) (states 0))

theorem fixedValue (P : Program 2) (count fixed parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph P fixed (Fin.cons fixed (Fin.cons parameter Fin.elim0))))) :
    Nonempty (Derivation body Gamma (repeatGraph P fixed count fixed parameter)) := by
  apply pairValuesCases parameter (fun _ : Fin 1 => fixed) _
  intro β j Delta states hj hs
  rw [parameterRepeatRename]
  have hp' := renameInto hp j Delta hj
  simp only [programRename, consTermRename, emptyRename] at hp'
  have hc := carryValue P (states 0) (states 0) (fixed.relabel j) (fixed.relabel j)
    (parameter.relabel j) (hs 0) (hs 0) hp'
  exact runValue P (fixed.relabel j) (count.relabel j) (fixed.relabel j)
    (parameter.relabel j) (states 0) (states 0) (hs 0) (hs 0)
    (InternalNumericIterationFixedPointProof.fixedValue (carryP P) (count.relabel j) (states 0) hc)

theorem frontSuccForward (P : Program 2) (out count value next parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0)))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph P out (OrdinaryArithmetic.succTerm count) value parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph P out count next parameter)) := by
  apply pairValuesCases parameter ![value,next,out] _
  intro β j Delta states hj hs
  simp only [parameterRepeatRename]
  have h0 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 0) (parameter.relabel j) (value.relabel j))) := by
    simpa using hs 0
  have h1 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 1) (parameter.relabel j) (next.relabel j))) := by
    simpa using hs 1
  have h2 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 2) (parameter.relabel j) (out.relabel j))) := by
    simpa using hs 2
  have hp' := renameInto hp j Delta hj
  simp only [programRename, consTermRename, emptyRename] at hp'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename, sucRelabel] at hr'
  have hc := carryValue P (states 0) (states 1) (value.relabel j) (next.relabel j)
    (parameter.relabel j) h0 h1 hp'
  have hu := runRecover P (out.relabel j) (OrdinaryArithmetic.succTerm (count.relabel j))
    (value.relabel j) (parameter.relabel j) (states 0) (states 2) h0 h2 hr'
  exact runValue P (out.relabel j) (count.relabel j) (next.relabel j)
    (parameter.relabel j) (states 1) (states 2) h1 h2
    (InternalNumericIterationProof.frontSuccForward (carryP P) (count.relabel j)
      (states 2) (states 0) (states 1) hc hu)

theorem frontSuccBackward (P : Program 2) (out count value next parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0)))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph P out count next parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph P out (OrdinaryArithmetic.succTerm count) value parameter)) := by
  apply pairValuesCases parameter ![value,next,out] _
  intro β j Delta states hj hs
  simp only [parameterRepeatRename, sucRelabel]
  have h0 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 0) (parameter.relabel j) (value.relabel j))) := by
    simpa using hs 0
  have h1 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 1) (parameter.relabel j) (next.relabel j))) := by
    simpa using hs 1
  have h2 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 2) (parameter.relabel j) (out.relabel j))) := by
    simpa using hs 2
  have hp' := renameInto hp j Delta hj
  simp only [programRename, consTermRename, emptyRename] at hp'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename] at hr'
  have hc := carryValue P (states 0) (states 1) (value.relabel j) (next.relabel j)
    (parameter.relabel j) h0 h1 hp'
  have hu := runRecover P (out.relabel j) (count.relabel j)
    (next.relabel j) (parameter.relabel j) (states 1) (states 2) h1 h2 hr'
  exact runValue P (out.relabel j) (OrdinaryArithmetic.succTerm (count.relabel j)) (value.relabel j)
    (parameter.relabel j) (states 0) (states 2) h0 h2
    (InternalNumericIterationProof.frontSuccBackward (carryP P) (count.relabel j)
      (states 2) (states 0) (states 1) hc hu)

theorem fusionRecover (P : Program 2) (out first second value intermediate parameter : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph P intermediate first value parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph P out (OrdinaryArithmetic.addTerm first second) value parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph P out second intermediate parameter)) := by
  apply pairValuesCases parameter ![value,intermediate,out] _
  intro β j Delta states hj hs
  simp only [parameterRepeatRename]
  have h0 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 0) (parameter.relabel j) (value.relabel j))) := by
    simpa using hs 0
  have h1 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 1) (parameter.relabel j) (intermediate.relabel j))) := by
    simpa using hs 1
  have h2 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 2) (parameter.relabel j) (out.relabel j))) := by
    simpa using hs 2
  have hm' := renameInto hm j Delta hj
  rw [parameterRepeatRename] at hm'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename, InternalOriginalOrderSyntaxProof.addRelabel] at hr'
  have hmu := runRecover P (intermediate.relabel j) (first.relabel j) (value.relabel j)
    (parameter.relabel j) (states 0) (states 1) h0 h1 hm'
  have hru := runRecover P (out.relabel j)
    (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)) (value.relabel j)
    (parameter.relabel j) (states 0) (states 2) h0 h2 hr'
  exact runValue P (out.relabel j) (second.relabel j) (intermediate.relabel j)
    (parameter.relabel j) (states 1) (states 2) h1 h2
    (InternalNumericIterationFusionProof.fusionRecover (carryP P) (first.relabel j)
      (second.relabel j) (states 0) (states 1) (states 2) hmu hru)

theorem fusionValue (P : Program 2) (out first second value intermediate parameter : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph P intermediate first value parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph P out second intermediate parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph P out (OrdinaryArithmetic.addTerm first second) value parameter)) := by
  apply pairValuesCases parameter ![value,intermediate,out] _
  intro β j Delta states hj hs
  simp only [parameterRepeatRename, InternalOriginalOrderSyntaxProof.addRelabel]
  have h0 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 0) (parameter.relabel j) (value.relabel j))) := by
    simpa using hs 0
  have h1 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 1) (parameter.relabel j) (intermediate.relabel j))) := by
    simpa using hs 1
  have h2 : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (states 2) (parameter.relabel j) (out.relabel j))) := by
    simpa using hs 2
  have hm' := renameInto hm j Delta hj
  rw [parameterRepeatRename] at hm'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename] at hr'
  have hmu := runRecover P (intermediate.relabel j) (first.relabel j) (value.relabel j)
    (parameter.relabel j) (states 0) (states 1) h0 h1 hm'
  have hru := runRecover P (out.relabel j) (second.relabel j) (intermediate.relabel j)
    (parameter.relabel j) (states 1) (states 2) h1 h2 hr'
  exact runValue P (out.relabel j)
    (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)) (value.relabel j)
    (parameter.relabel j) (states 0) (states 2) h0 h2
    (InternalNumericIterationFusionProof.fusionValue (carryP P) (first.relabel j)
      (second.relabel j) (states 0) (states 1) (states 2) hmu hru)

theorem actualOriginalParameterizedNumericIterationZero :
    ActualOriginalParameterizedNumericIterationZero := by
  intro body P α Gamma out value parameter
  let A := repeatGraph P out OrdinaryArithmetic.zeroTerm value parameter
  let B := equal out value
  have forward : Nonempty (Derivation body (A :: Gamma) B) := by
    change Nonempty (Derivation body (A :: Gamma) (equal out value))
    rw [equalEqn]
    exact valueUnique (repeatP P) out value
      (Fin.cons OrdinaryArithmetic.zeroTerm (Fin.cons value (Fin.cons parameter Fin.elim0)))
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (zeroValue P value parameter)
  have backward : Nonempty (Derivation body (B :: Gamma) A) := by
    have he : Derivation body (B :: Gamma) (eqn out value) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (repeatP P) value out
      (Fin.cons OrdinaryArithmetic.zeroTerm (Fin.cons value (Fin.cons parameter Fin.elim0)))
      ⟨symm he⟩ (zeroValue P value parameter)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem actualOriginalParameterizedNumericIterationFrontSuccessor :
    ActualOriginalParameterizedNumericIterationFrontSuccessor := by
  intro body P α Gamma out count value next parameter
  let A := programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0))
  let B := repeatGraph P out (OrdinaryArithmetic.succTerm count) value parameter
  let C := repeatGraph P out count next parameter
  have forward : Nonempty (Derivation body (B :: A :: Gamma) C) :=
    frontSuccForward P out count value next parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body (C :: A :: Gamma) B) :=
    frontSuccBackward P out count value next parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

theorem actualOriginalParameterizedNumericIterationAdditionFusion :
    ActualOriginalParameterizedNumericIterationAdditionFusion := by
  intro body P α Gamma out first second value intermediate parameter
  let A := repeatGraph P intermediate first value parameter
  let B := repeatGraph P out (OrdinaryArithmetic.addTerm first second) value parameter
  let C := repeatGraph P out second intermediate parameter
  have forward : Nonempty (Derivation body (B :: A :: Gamma) C) :=
    fusionRecover P out first second value intermediate parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body (C :: A :: Gamma) B) :=
    fusionValue P out first second value intermediate parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

theorem actualOriginalParameterizedNumericIterationFixedPoint :
    ActualOriginalParameterizedNumericIterationFixedPoint := by
  intro body P α Gamma out count fixed parameter
  let A := programGraph P fixed (Fin.cons fixed (Fin.cons parameter Fin.elim0))
  let B := repeatGraph P out count fixed parameter
  let C := equal out fixed
  have forward : Nonempty (Derivation body (B :: A :: Gamma) C) := by
    change Nonempty (Derivation body (B :: A :: Gamma) (equal out fixed))
    rw [equalEqn]
    exact valueUnique (repeatP P) out fixed
      (Fin.cons count (Fin.cons fixed (Fin.cons parameter Fin.elim0)))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (fixedValue P count fixed parameter
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
  have backward : Nonempty (Derivation body (C :: A :: Gamma) B) := by
    have he : Derivation body (C :: A :: Gamma) (eqn out fixed) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (repeatP P) fixed out
      (Fin.cons count (Fin.cons fixed (Fin.cons parameter Fin.elim0))) ⟨symm he⟩
      (fixedValue P count fixed parameter
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof
