module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAuxBottomRefinement NumberedWindowInternalAuxBottomRefinementNumericTargets
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (literalFields)
open NumberedWindowInternalAtomicRefinementNumericControlProof (runBoth bothTrue)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeTwo compareEvaluation)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue nodeArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode nodePacked)
open NumberedWindowFieldAlgorithm (pack unpackNode)
open NumberedWindowPairAlgorithm (pair)

private theorem literalArity (tag width n : Nat) :
    run (nodeGood (literal 1 tag) width) n = 1 ↔
      ∃ fs, unpackNode n = some (tag,fs) ∧ fs.length = width :=
  nodeArity (literal 1 tag) width n tag (literalEvaluation 1 tag (n ::ᵥ nil))

private theorem outer (x : Nat) :
    run addressGood x = 1 ↔ ∃ c t k, x = packedAddress c t k := by
  change run (nodeGood (literal 1 3) 3) x = 1 ↔ _
  rw [literalArity]
  constructor
  · rintro ⟨fs,parsed,len⟩
    rcases fs with _ | ⟨c,_ | ⟨t,_ | ⟨k,_ | ⟨n,rest⟩⟩⟩⟩ <;> simp at len
    exact ⟨c,t,k,codeOfNode parsed⟩
  · rintro ⟨c,t,k,rfl⟩
    exact ⟨[c,t,k],nodePacked 3 [c,t,k],rfl⟩

private theorem auxFields (dom cod fn arg : Nat) :
    run (field 1) (auxRaw dom cod fn arg) = cod ∧
    run (field 2) (auxRaw dom cod fn arg) = fn := by
  let b := pair 6 (pack [dom,cod,fn,arg])+1
  have a0 : run cellTail b = pack [dom,cod,fn,arg] :=
    (headTailOfCell (cellAt 6 (pack [dom,cod,fn,arg]))).2
  have a1 : run cellTail (pack [dom,cod,fn,arg]) = pack [cod,fn,arg] :=
    (headTailOfCell (cellAt dom (pack [cod,fn,arg]))).2
  have a2 : run cellHead (pack [cod,fn,arg]) = cod ∧ run cellTail (pack [cod,fn,arg]) = pack [fn,arg] :=
    headTailOfCell (cellAt cod (pack [fn,arg]))
  have a3 : run cellHead (pack [fn,arg]) = fn :=
    (headTailOfCell (cellAt fn (pack [arg]))).1
  change run (field 1) b = cod ∧ run (field 2) b = fn
  exact ⟨by simp only [field,cursor,applyValue,a0,a1,a2.1],
    by simp only [field,cursor,applyValue,a0,a1,a2.2,a3]⟩

private theorem fits (x : Nat) :
    run resultFits x = 1 ↔ run rawResult x = run auxCodomain x := by
  unfold run resultFits
  rw [compositeTwo,compareEvaluation]
  split <;> simp_all

private theorem recognition (x : Nat) :
    run sourceFlag x = 1 ↔ ∃ c dom cod stored a, x = packedAuxBottom c dom cod stored a := by
  rw [sourceFlag,bothTrue,bothTrue,bothTrue,outer,fits]
  constructor
  · rintro ⟨⟨c,e,k,rfl⟩,good,bare,code⟩
    have fields := literalFields c e k
    rw [auxShell,applyValue,fields.2.2,literalArity] at good
    obtain ⟨row,readrow,len⟩ := good
    rcases row with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨a,_ | ⟨x,tail⟩⟩⟩⟩⟩ <;> simp at len
    have exactK : k = auxRaw dom cod fn a := codeOfNode readrow
    have aux := auxFields dom cod fn a
    rw [auxHeadBottom,applyValue,auxFunction,applyValue,fields.2.2,exactK,aux.2,literalArity] at bare
    obtain ⟨row,readbare,width⟩ := bare
    rcases row with _ | ⟨stored,_ | ⟨x,tail⟩⟩ <;> simp at width
    have exactF : fn = bottomRaw stored := codeOfNode readbare
    rw [fields.2.1,auxCodomain,applyValue,fields.2.2,exactK,aux.1] at code
    exact ⟨c,dom,cod,stored,a,by rw [exactK,exactF,code,packedAuxBottom]⟩
  · rintro ⟨c,dom,cod,stored,a,rfl⟩
    let fn := bottomRaw stored
    let k := auxRaw dom cod fn a
    let x := packedAddress c cod k
    have fields := literalFields c cod k
    have aux := auxFields dom cod fn a
    change (∃ c t k, x = packedAddress c t k) ∧ run auxShell x = 1 ∧
      run auxHeadBottom x = 1 ∧ run rawResult x = run auxCodomain x
    refine ⟨⟨c,cod,k,rfl⟩,?_,?_,?_⟩
    · rw [auxShell,applyValue,fields.2.2,literalArity]
      exact ⟨[dom,cod,fn,a],nodePacked 6 [dom,cod,fn,a],rfl⟩
    · rw [auxHeadBottom,applyValue,auxFunction,applyValue,fields.2.2,aux.2,literalArity]
      exact ⟨[stored],nodePacked 3 [stored],rfl⟩
    · rw [fields.2.1,auxCodomain,applyValue,fields.2.2,aux.1]

theorem exactRecognizer : ExactNumericAuxBottomRecognizer := by
  intro x
  refine ⟨recognition x,?_⟩
  rw [sourceFlag,runBoth]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericRecognitionProof
