module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericRecognitionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAuxBottomRefinement
open NumberedWindowInternalAuxBottomRefinementNumericTargets (packedAuxBottom)
open NumberedWindowInternalNeutralAuxiliaryRefinement
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
open NumberedWindowAtomicRawStep (bottomRaw freeRaw)
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

@[expose] def packedAuxFree (c dom cod stored name a : Nat) :=
  packedAddress c cod (auxRaw dom cod (freeRaw stored name) a)

theorem freeRecognition (x : Nat) :
    run freeAux x = 1 ↔ ∃ c dom cod stored name a, x = packedAuxFree c dom cod stored name a := by
  rw [freeAux,bothTrue,bothTrue,bothTrue,outer,fits]
  constructor
  · rintro ⟨⟨c,e,k,rfl⟩,good,bare,code⟩
    have fields := literalFields c e k
    rw [auxShell,applyValue,fields.2.2,literalArity] at good
    obtain ⟨row,readrow,len⟩ := good
    rcases row with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨a,_ | ⟨x,tail⟩⟩⟩⟩⟩ <;> simp at len
    have exactK : k = auxRaw dom cod fn a := codeOfNode readrow
    have aux := auxFields dom cod fn a
    rw [auxHeadFree,applyValue,auxFunction,applyValue,fields.2.2,exactK,aux.2,literalArity] at bare
    obtain ⟨row,readbare,width⟩ := bare
    rcases row with _ | ⟨stored,_ | ⟨name,_ | ⟨x,tail⟩⟩⟩ <;> simp at width
    have exactF : fn = freeRaw stored name := codeOfNode readbare
    rw [fields.2.1,auxCodomain,applyValue,fields.2.2,exactK,aux.1] at code
    exact ⟨c,dom,cod,stored,name,a,by rw [exactK,exactF,code,packedAuxFree]⟩
  · rintro ⟨c,dom,cod,stored,name,a,rfl⟩
    let fn := freeRaw stored name
    let k := auxRaw dom cod fn a
    let x := packedAddress c cod k
    have fields := literalFields c cod k
    have aux := auxFields dom cod fn a
    change (∃ c t k, x = packedAddress c t k) ∧ run auxShell x = 1 ∧
      run auxHeadFree x = 1 ∧ run rawResult x = run auxCodomain x
    refine ⟨⟨c,cod,k,rfl⟩,?_,?_,?_⟩
    · rw [auxShell,applyValue,fields.2.2,literalArity]
      exact ⟨[dom,cod,fn,a],nodePacked 6 [dom,cod,fn,a],rfl⟩
    · rw [auxHeadFree,applyValue,auxFunction,applyValue,fields.2.2,aux.2,literalArity]
      exact ⟨[stored,name],nodePacked 0 [stored,name],rfl⟩
    · rw [fields.2.1,auxCodomain,applyValue,fields.2.2,aux.1]

theorem freeBit (x : Nat) : run freeAux x = 0 ∨ run freeAux x = 1 := by
  rw [freeAux,runBoth]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The auxiliary domain is the actual field 0 of the application, not
field 0 of the atom. This single literal-node calculation supplies both. -/
private theorem nodeFirst (tag hd : Nat) (rest : List Nat) :
    run (field 0) (NumberedWindowFieldAlgorithm.packNode tag (hd :: rest)) = hd := by
  let b := pair tag (pack (hd :: rest)) + 1
  have p := (headTailOfCell (cellAt tag (pack (hd :: rest)))).2
  have q := (headTailOfCell (cellAt hd (pack rest))).1
  change run (field 0) b = hd
  simp only [field,cursor,applyValue,b,p]
  exact q

theorem auxCoordinates (c dom cod fn arg : Nat) :
    run auxDom (packedAddress c cod (auxRaw dom cod fn arg)) = dom ∧
    run auxFunction (packedAddress c cod (auxRaw dom cod fn arg)) = fn := by
  have fields := literalFields c cod (auxRaw dom cod fn arg)
  constructor
  · rw [auxDom,applyValue,fields.2.2]
    exact nodeFirst 6 dom [cod,fn,arg]
  · rw [auxFunction,applyValue,fields.2.2]
    exact (auxFields dom cod fn arg).2

theorem freeStored (c dom cod stored name arg : Nat) :
    run auxFnType (packedAuxFree c dom cod stored name arg) = stored := by
  rw [packedAuxFree,auxFnType,applyValue,(auxCoordinates c dom cod _ arg).2]
  exact nodeFirst 0 stored [name]

theorem bottomStored (c dom cod stored arg : Nat) :
    run auxFnType (packedAuxBottom c dom cod stored arg) = stored := by
  rw [packedAuxBottom,auxFnType,applyValue,(auxCoordinates c dom cod _ arg).2]
  exact nodeFirst 3 stored []

#print axioms freeRecognition
#print axioms freeBit
#print axioms auxCoordinates
#print axioms freeStored
#print axioms bottomStored

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryNumericRecognitionProof
