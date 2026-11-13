module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherReferenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSelectProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix DispatcherSupportProof DispatcherCombinatorsProof DispatcherPrimitivesProof

theorem ruleSelected {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (l a : Program 1) (x : Program 3)
    (context raw ref1 index fuel history : Term ctx)
    (hmp : Computes p G HistoryDispatcher.mpBranch
      (index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context raw ref1 ::ᵥ nil) (.succ .zero)) :
    Computes p G (HistoryDispatcher.ruleDispatcher l a x)
      (index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context raw ref1 ::ᵥ nil) (.succ .zero) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let args := index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context raw ref1 ::ᵥ nil
  obtain ⟨_,_,hrule,_,_,_,_⟩ := DispatcherFieldsProof.fields p G ptag hp context raw ref1 index fuel history
  have ne20 : Derivation T (.neg (.equal (.succ (.succ (.zero : Term ctx))) .zero)) := .arithmetic (.succNotZero (.succ .zero))
  have ne21 : Derivation T (.neg (.equal (.succ (.succ (.zero : Term ctx))) (.succ .zero))) :=
    Hilbert.modusTollens (.arithmetic (.succInjective (.succ .zero) .zero)) (.arithmetic (.succNotZero .zero))
  have ht0 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 0) (.succ (.succ .zero)) .zero .zero
    hrule (constantValue p G args 0) (equalFalse p G _ _ ne20)
  have ht1 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 1) (.succ (.succ .zero)) (.succ .zero) .zero
    hrule (constantValue p G args 1) (equalFalse p G _ _ ne21)
  have ht2 := binary p G args equalCode HistoryDispatcher.ruleCode (constant 4 2) (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ .zero)
    hrule (constantValue p G args 2) (equalDiagonal p G _)
  apply chooseZero p G args _ _ _ (.succ .zero) ht0
  apply chooseZero p G args _ _ _ (.succ .zero) ht1
  exact choosePositive p G args _ _ _ .zero (.succ .zero) ht2 hmp
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSelectProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSelectProof
