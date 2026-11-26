module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.CodecTotalProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix HistoryRuleSuffix.NativeProof
open GorbowProofChecker (History Line Entry context conclusion)
open SixSol20261112.HistoryMachine (State transition)

def inputs (state : State) (index fuel : Nat) : List.Vector Nat 3 :=
  Encodable.encode state ::ᵥ index ::ᵥ fuel ::ᵥ nil

theorem optionEval (s : Option History) (ls : List Line) (index fuel : Nat) :
    evaluate stateOption (inputs (s,ls) index fuel)=Encodable.encode s := by
  rw [stateOption,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]
  change (Nat.unpair (Nat.pair (Encodable.encode s) (Encodable.encode ls))).1=Encodable.encode s
  rw [Nat.unpair_pair]

theorem linesEval (s : Option History) (ls : List Line) (index fuel : Nat) :
    evaluate stateLines (inputs (s,ls) index fuel)=Encodable.encode ls := by
  rw [stateLines,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]
  change (Nat.unpair (Nat.pair (Encodable.encode s) (Encodable.encode ls))).2=Encodable.encode ls
  rw [Nat.unpair_pair]

theorem currentEval (s : Option History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate currentLine (inputs (s,l::ls) index fuel)=Encodable.encode l := by
  rw [currentLine,oneEval,linesEval,HistoryLookup.NativeProof.headCons]

theorem remainingEval (s : Option History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate remainingLines (inputs (s,l::ls) index fuel)=Encodable.encode ls := by
  rw [remainingLines,oneEval,linesEval,HistoryLookup.NativeProof.tailList]
  rfl

theorem historyEval (h : History) (ls : List Line) (index fuel : Nat) :
    evaluate historyPayload (inputs (some h,ls) index fuel)=Encodable.encode h := by
  rw [historyPayload,oneEval,optionEval,HistoryCodec.NativeProof.evaluatePredecessor]
  rfl

theorem contextEval (s : Option History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate lineContext (inputs (s,l::ls) index fuel)=context l := by
  rw [lineContext,oneEval,currentEval,HistoryDecoder.NativeProof.evaluateDecoder]
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,HistoryDecoder.NativeProof.coordinate,Nat.unpair_pair,Bool.false_eq_true,if_false,if_true]
  rfl

theorem rawEval (s : Option History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate lineRaw (inputs (s,l::ls) index fuel)=Encodable.encode (conclusion l) := by
  rw [lineRaw,oneEval,oneEval,currentEval,HistoryDecoder.NativeProof.evaluateDecoder,
    HistoryDecoder.NativeProof.evaluateDecoder]
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,HistoryDecoder.NativeProof.coordinate,Nat.unpair_pair,Bool.false_eq_true,if_false,if_true]
  rfl

theorem checkedEval (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (hl : HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram)
    (h : History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate (checkedLine valid logical arithmetic axiomProgram) (inputs (some h,l::ls) index fuel)=
      HistoryDispatcher.truth (GorbowTheoryChecker.lineCheck
        (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,fuel)) h l) := by
  change evaluate (HistoryDispatcher.lineDispatcher valid logical arithmetic axiomProgram)
    (index ::ᵥ fuel ::ᵥ evaluate historyPayload (inputs (some h,l::ls) index fuel) ::ᵥ
      evaluate currentLine (inputs (some h,l::ls) index fuel) ::ᵥ nil) = _
  rw [historyEval,currentEval]
  exact HistoryDispatcher.NativeProof.nativeLineDispatcher valid logical arithmetic axiomProgram hl index fuel h l

theorem extendedEval (h : History) (l : Line) (ls : List Line) (index fuel : Nat) :
    evaluate someExtendedHistory (inputs (some h,l::ls) index fuel)=
      Encodable.encode (some ((context l,conclusion l)::h)) := by
  rw [someExtendedHistory,oneEval]
  change (evaluate extendedHistory (inputs (some h,l::ls) index fuel)).succ = _
  rw [extendedHistory,twoEval,entry,twoEval,contextEval,rawEval,historyEval,
    HistoryCodec.NativeProof.nativePair,HistoryCodec.NativeProof.nativeConsAllVectors]
  rfl

theorem nativeState (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (hl : HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram)
    (state : State) (index fuel : Nat) :
    evaluate (kernel valid logical arithmetic axiomProgram) (inputs state index fuel)=
      Encodable.encode (transition index fuel state) := by
  rcases state with ⟨s,ls⟩
  cases ls with
  | nil =>
      rw [kernel,chooseEval,linesEval]
      rfl
  | cons l ls =>
      rw [kernel,chooseEval,linesEval,HistoryLookup.NativeProof.encodeCons]
      simp only [Nat.succ_ne_zero,if_false]
      rw [nextState,twoEval,remainingEval,nextOption,chooseEval,optionEval]
      cases s with
      | none =>
          change evaluate HistoryCodec.pair (evaluate (constant 3 0) (inputs (none,l::ls) index fuel) ::ᵥ Encodable.encode ls ::ᵥ nil)=_
          rw [constantEval,HistoryCodec.NativeProof.nativePair]
          rfl
      | some h =>
          change evaluate HistoryCodec.pair
            ((if (Encodable.encode h).succ=0 then evaluate (constant 3 0) (inputs (some h,l::ls) index fuel)
              else evaluate (acceptedOption valid logical arithmetic axiomProgram) (inputs (some h,l::ls) index fuel)) ::ᵥ Encodable.encode ls ::ᵥ nil)=_
          simp only [Nat.succ_ne_zero,if_false]
          rw [acceptedOption,chooseEval,acceptedTest,twoEval,constantEval,checkedEval _ _ _ _ hl,
            equalEval,constantEval,extendedEval]
          cases hc : GorbowTheoryChecker.lineCheck
            (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,fuel)) h l <;>
            simp [HistoryDispatcher.truth,HistoryCodec.NativeProof.nativePair,
              transition,GorbowTheoryChecker.step,hc] <;>
            rw [HistoryCodec.NativeProof.nativePair] <;> rfl


theorem nativeKernel : Targets.NativeKernel := by
  intro valid logical arithmetic axiomProgram hl v
  have he := nativeState valid logical arithmetic axiomProgram hl
    (SixSol20261112.HistoryMachine.decodedState v.head) v.tail.head v.tail.tail.head
  rw [inputs,CodecTotalProof.encodeDecoded] at he
  have hv : v=v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ nil := by
    calc
      v = v.head ::ᵥ v.tail := (List.Vector.cons_head_tail v).symm
      _ = v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail := by rw [List.Vector.cons_head_tail v.tail]
      _ = v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ nil := by
        have hh := (List.Vector.cons_head_tail v.tail.tail).symm
        rw [List.Vector.eq_nil v.tail.tail.tail] at hh
        exact congrArg (fun t => v.head ::ᵥ v.tail.head ::ᵥ t) hh
  simpa only [← hv,SixSol20261112.HistoryMachine.kernelFunction] using he
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.NativeProof
