module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuccessProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuffixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FieldsProof EntryProof TransitionEquationsProof OptionProof

noncomputable def firstCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (a b rest : Term ctx) (h : Hilbert.Local T ctx G (.equal a b)) :
    Hilbert.Local T ctx G (.equal (pairCall tag a rest) (pairCall tag b rest)) := by
  have d := localUnary (call tag (.var 0 ::ᵥ liftTerm rest ::ᵥ nil)) a b h
  simpa only [pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,
    Support.shiftCancel,substitute,Fin.cases_zero] using d

theorem internalStepSuffix : Targets.InternalStepSuffix := by
  intro v l a x n p tag atag ptag ctag ht ha hp hc ctx index fuel h tail line rest out
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (kernelCall tag (activeState ptag ctag h line rest) index fuel) (pairCall ptag (.succ out) rest)
  let h' := HistoryAppend.appendCall atag h tail
  let N := newHistory (someTag tag v l a x) h line
  let N' := newHistory (someTag tag v l a x) h' line
  obtain ⟨hpair,hsel,heq,hdisp,hcons⟩ := kernelNodes p tag v l a x ht
  obtain ⟨hparts⟩ := SuccessProof.successfulParts p tag ptag ctag v l a x ht hp hc index fuel h line rest out
  obtain ⟨hds⟩ := HistoryDispatcher.SuffixProof.internalLineSuffix v l a x n p (dispatcherTag tag v l a x) atag hdisp ha ctx index fuel h tail line
  obtain ⟨hopt⟩ := optionAccepted p tag v l a x ht index fuel h' line
  obtain ⟨hnew⟩ := NormalProof.kernelEquation p tag ptag ctag v l a x ht hp hc index fuel h' line rest
  obtain ⟨happend⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag (outputConsTag (someTag tag v l a x)) ha hcons ctx
    (entryValue (entryWrapper (someTag tag v l a x)) line) h tail
  obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (outputPairTag tag v l a x) ptag hpair hp
    (.succ (HistoryAppend.appendCall atag out tail)) rest
  have e : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have parts := Hilbert.Local.mp (.base hparts) e
  have oldCheck := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) parts
  have oldShape := Hilbert.Local.mp (.base (.logical (.andRight _ _))) parts
  have newCheck := Hilbert.Local.mp (.base hds) oldCheck
  have optionShape := Hilbert.Local.mp (.base hopt) newCheck
  have appendEq := firstCongruence atag N out tail oldShape
  have historyShape : Hilbert.Local T ctx [E] (.equal N' (HistoryAppend.appendCall atag out tail)) :=
    localTrans _ _ _ (.base (Support.equalitySymmetry _ _ happend)) appendEq
  have successorShape : Hilbert.Local T ctx [E] (.equal (.succ N') (.succ (HistoryAppend.appendCall atag out tail))) :=
    localUnary (.succ (.var 0)) _ _ historyShape
  have pairOption := firstCongruence (outputPairTag tag v l a x) _ _ rest optionShape
  have pairHistory := firstCongruence (outputPairTag tag v l a x) _ _ rest successorShape
  have result := localTrans _ _ _ (.base hnew)
    (localTrans _ _ _ pairOption (localTrans _ _ _ pairHistory (.base hcopy)))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge result)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.SuffixProof
