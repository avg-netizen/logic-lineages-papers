module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.CodecProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix HistoryRuleSuffix.NativeProof
open GorbowProofChecker (History Line Entry)
open SixSol20261112.HistoryMachine (State finish)

def inputs (state : State) (context formula certificate : Nat) : List.Vector Nat 4 :=
  Encodable.encode state ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil

theorem originalFinish (state : State) (n formula certificate : Nat) :
    finish state n formula certificate =
      match state.1 with
      | none => false
      | some [] => false
      | some ((m,raw)::_) => decide (n=m ∧ formula=Encodable.encode raw+Encodable.encode raw) := by
  obtain ⟨certLines,_,hc⟩ := CodecProof.certificateCodecTotal certificate
  rcases state with ⟨s,lines⟩
  cases s with
  | none => cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula <;> simp [finish,hf,hc]
  | some history => cases history with
    | nil => cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula <;> simp [finish,hf,hc]
    | cons entry tail =>
        rcases entry with ⟨m,raw⟩
        cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula with
        | none =>
            have hne : formula ≠ Encodable.encode raw+Encodable.encode raw := by
              intro he
              have hd := (CodecProof.formulaDecodeExact formula raw).mpr he
              rw [hf] at hd
              cases hd
            simp [finish,hf,hc,hne]
        | some decoded =>
            have he := CodecProof.formulaDecodeExact formula raw
            rw [hf] at he
            simp only [Option.some.injEq] at he
            simp only [finish,hf,hc]
            rw [← he]

theorem optionEval (s : Option History) (lines : List Line) (n formula certificate : Nat) :
    evaluate optionField (inputs (s,lines) n formula certificate)=Encodable.encode s := by
  rw [optionField,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]
  change (Nat.unpair (Nat.pair (Encodable.encode s) (Encodable.encode lines))).1=Encodable.encode s
  rw [Nat.unpair_pair]

theorem historyEval (history : History) (lines : List Line) (n formula certificate : Nat) :
    evaluate historyField (inputs (some history,lines) n formula certificate)=Encodable.encode history := by
  rw [historyField,oneEval,optionEval,HistoryCodec.NativeProof.evaluatePredecessor]
  rfl

theorem entryEval (entry : Entry) (tail : History) (lines : List Line) (n formula certificate : Nat) :
    evaluate entryField (inputs (some (entry::tail),lines) n formula certificate)=Encodable.encode entry := by
  rw [entryField,oneEval,historyEval,HistoryLookup.NativeProof.headCons]

theorem contextEval (context : Nat) (raw : List Nat) (tail : History) (lines : List Line) (n formula certificate : Nat) :
    evaluate contextField (inputs (some ((context,raw)::tail),lines) n formula certificate)=context := by
  rw [contextField,oneEval,entryEval,HistoryDecoder.NativeProof.evaluateDecoder]
  change (Nat.unpair (Nat.pair context (Encodable.encode raw))).1=context
  rw [Nat.unpair_pair]

theorem rawEval (context : Nat) (raw : List Nat) (tail : History) (lines : List Line) (n formula certificate : Nat) :
    evaluate rawField (inputs (some ((context,raw)::tail),lines) n formula certificate)=Encodable.encode raw := by
  rw [rawField,oneEval,entryEval,HistoryDecoder.NativeProof.evaluateDecoder]
  change (Nat.unpair (Nat.pair context (Encodable.encode raw))).2=Encodable.encode raw
  rw [Nat.unpair_pair]

theorem nativeState (state : State) (n formula certificate : Nat) :
    evaluate finalizer (inputs state n formula certificate) = if finish state n formula certificate then 1 else 0 := by
  rw [originalFinish]
  rcases state with ⟨s,lines⟩
  cases s with
  | none =>
      rw [finalizer,chooseEval,optionEval]
      simp only [show Encodable.encode (none : Option History)=0 from rfl,if_pos rfl,constantEval,Bool.false_eq_true,if_false]
  | some history =>
      rw [finalizer,chooseEval,optionEval]
      simp only [show Encodable.encode (some history)=(Encodable.encode history).succ from rfl,Nat.succ_ne_zero,if_false]
      rw [chooseEval,historyEval]
      cases history with
      | nil =>
          simp only [show Encodable.encode ([] : History)=0 from rfl,if_pos rfl,constantEval,Bool.false_eq_true,if_false]
      | cons entry tail =>
          rcases entry with ⟨context,raw⟩
          rw [HistoryLookup.NativeProof.encodeCons]
          simp only [Nat.succ_ne_zero,if_false]
          rw [conjunctionEval,twoEval,contextEval,equalEval,twoEval,doubledRaw,twoEval,
            rawEval,HistoryCodec.NativeProof.evaluateAdd,equalEval]
          simp only [projectionEval,inputs,get4_1,get4_2]
          by_cases hn : n=context <;> by_cases hf : formula=Encodable.encode raw+Encodable.encode raw <;> simp [hn,hf]

theorem nativeFinalizer : SixSol20261112.HistoryMachine.FinishProgram finalizer := by
  intro v
  have he := nativeState (SixSol20261112.HistoryMachine.decodedState v.head)
    v.tail.head v.tail.tail.head v.tail.tail.tail.head
  rw [inputs,HistoryKernel.CodecTotalProof.encodeDecoded] at he
  have hv : v=v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ v.tail.tail.tail.head ::ᵥ nil := by
    calc
      v = v.head ::ᵥ v.tail := (List.Vector.cons_head_tail v).symm
      _ = v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail := by rw [List.Vector.cons_head_tail v.tail]
      _ = v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ v.tail.tail.tail := by rw [List.Vector.cons_head_tail v.tail.tail]
      _ = v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ v.tail.tail.tail.head ::ᵥ nil := by
        have hh := (List.Vector.cons_head_tail v.tail.tail.tail).symm
        rw [List.Vector.eq_nil v.tail.tail.tail.tail] at hh
        exact congrArg (fun t => v.head ::ᵥ v.tail.head ::ᵥ v.tail.tail.head ::ᵥ t) hh
  simpa only [← hv,SixSol20261112.HistoryMachine.finishFunction] using he

theorem nativeAuxiliaries : Targets.NativeAuxiliaries :=
  ⟨CodecProof.nativeBound,CodecProof.nativeInitial,nativeFinalizer⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.NativeProof
