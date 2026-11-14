module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open HistoryRuleSuffix.NativeProof
theorem successor (test : Program 2) (k raw line : Nat) :
 evaluate (search test) (k.succ ::ᵥ raw ::ᵥ line ::ᵥ nil) =
 if evaluate (search test) (k ::ᵥ raw ::ᵥ line ::ᵥ nil)=0 then
  if evaluate test (evaluate HistoryLookup.drop (k ::ᵥ raw ::ᵥ nil) ::ᵥ line ::ᵥ nil)=0 then 0 else 1
 else 1 := by
 change evaluate (step test) (k ::ᵥ evaluate (search test) (k ::ᵥ raw ::ᵥ line ::ᵥ nil) ::ᵥ raw ::ᵥ line ::ᵥ nil) = _
 simp only [step,positive,testAt,candidate,chooseEval,twoEval,constantEval,projectionEval,get4_0,get4_1,get4_2,get4_3]

theorem nativeSearch : Targets.NativeSearch := by
 intro test count raw line
 induction count with
 | zero =>
  change (0=0 ∨ 0=1) ∧ (0=1 ↔ ∃ i < 0, _)
  simp
 | succ count ih =>
  rw [successor]
  by_cases hz : evaluate (search test) (count ::ᵥ raw ::ᵥ line ::ᵥ nil)=0
  · by_cases ht : evaluate test (evaluate HistoryLookup.drop (count ::ᵥ raw ::ᵥ nil) ::ᵥ line ::ᵥ nil)=0
    · simp only [hz,ht,if_true]
      constructor
      · exact Or.inl rfl
      · constructor
        · intro h; omega
        · rintro ⟨i,hi,hit⟩
          have hil : i < count := by by_contra h; have : i=count := by omega; subst i; exact hit ht
          have hh := ih.2.mpr ⟨i,hil,hit⟩
          omega
    · simp only [hz,ht,if_true,if_false]
      exact ⟨Or.inr rfl,⟨fun _ => ⟨count,Nat.lt_succ_self _,ht⟩,fun _ => rfl⟩⟩
  · simp only [hz,if_false]
    have ho : evaluate (search test) (count ::ᵥ raw ::ᵥ line ::ᵥ nil)=1 := ih.1.resolve_left hz
    obtain ⟨i,hi,hit⟩ := ih.2.mp ho
    exact ⟨Or.inr rfl,⟨fun _ => ⟨i,Nat.lt_trans hi (Nat.lt_succ_self _),hit⟩,fun _ => rfl⟩⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.NativeProof.nativeSearch
