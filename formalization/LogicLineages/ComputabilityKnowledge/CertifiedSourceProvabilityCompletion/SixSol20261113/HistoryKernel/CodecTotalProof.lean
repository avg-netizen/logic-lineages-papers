module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.CodecTotalProof

def Total (α : Type) [Encodable α] : Prop := ∀ code : Nat, ∃ a : α, Encodable.encode a=code

theorem natTotal : Total Nat := fun n => ⟨n,rfl⟩
theorem prodTotal {α β : Type} [Encodable α] [Encodable β] (ha : Total α) (hb : Total β) : Total (α × β) := by
  intro code
  obtain ⟨a,hea⟩ := ha (Nat.unpair code).1
  obtain ⟨b,heb⟩ := hb (Nat.unpair code).2
  refine ⟨(a,b),?_⟩
  rw [HistoryDispatcher.NativeProof.encodeProd,hea,heb,Nat.pair_unpair]

theorem optionTotal {α : Type} [Encodable α] (ha : Total α) : Total (Option α) := by
  intro code
  cases code with
  | zero => exact ⟨none,rfl⟩
  | succ code =>
      obtain ⟨a,he⟩ := ha code
      refine ⟨some a,?_⟩
      change (Encodable.encode a).succ=code.succ
      rw [he]

theorem listTotal {α : Type} [Encodable α] (ha : Total α) : Total (List α) := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
      cases code with
      | zero => exact ⟨[],rfl⟩
      | succ code =>
          obtain ⟨a,hea⟩ := ha (Nat.unpair code).1
          obtain ⟨tail,het⟩ := ih (Nat.unpair code).2 (Nat.lt_succ_of_le (Nat.unpair_right_le code))
          refine ⟨a::tail,?_⟩
          rw [HistoryLookup.NativeProof.encodeCons,hea,het,Nat.pair_unpair]

theorem historyTotal : Total GorbowProofChecker.History :=
  listTotal (prodTotal natTotal (listTotal natTotal))
theorem lineTotal : Total GorbowProofChecker.Line :=
  prodTotal natTotal (prodTotal (listTotal natTotal)
    (prodTotal natTotal (prodTotal natTotal
      (prodTotal (listTotal (listTotal natTotal)) (prodTotal natTotal natTotal)))))
theorem stateCodecTotal : Targets.StateCodecTotal :=
  prodTotal (optionTotal historyTotal) (listTotal lineTotal)

theorem decodedEncode (s : SixSol20261112.HistoryMachine.State) :
    SixSol20261112.HistoryMachine.decodedState (Encodable.encode s)=s := by
  simp only [SixSol20261112.HistoryMachine.decodedState,Encodable.encodek,Option.getD_some]

theorem encodeDecoded (code : Nat) :
    Encodable.encode (SixSol20261112.HistoryMachine.decodedState code)=code := by
  obtain ⟨s,he⟩ := stateCodecTotal code
  rw [← he,decodedEncode]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.CodecTotalProof
