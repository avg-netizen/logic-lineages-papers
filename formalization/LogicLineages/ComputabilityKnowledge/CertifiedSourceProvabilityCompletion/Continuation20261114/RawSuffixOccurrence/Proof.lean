module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof

theorem nativeSuffix : Targets.NativeSuffix := by
 intro left right
 rw [HistoryLengthOffset.NativeStatementChecks.exactNativeLength.2 left,
  HistoryRuleSuffix.NativeProof.appendList,HistoryLookup.NativeProof.evaluateDrop]
 simp

theorem internalSuffix : Targets.InternalSuffix := by
 intro n p test I ctx left right
 exact InductionProof.lengthData n p I.lengthTag I.appendTag I.dropTag I.consTag I.hl I.ha I.hd I.hc ctx left right .zero

theorem internalCoverage : Targets.InternalCoverage := by
 intro n p test I ctx left right line
 let T := GorbowPRNumeralCalculation.Theory p
 let stream := HistoryAppend.appendCall I.appendTag left right
 let l := HistoryLengthOffset.lengthCall I.lengthTag left
 let r := HistoryLengthOffset.lengthCall I.lengthTag right
 let H := Formula.equal (RawSuffixSearch.testCall I.testTag right line) (.succ .zero)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := internalSuffix n p test I ctx left right
 have htest := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [H]) I.testTag
  _ line right line (.base he) (.base (.logical (.reflexive line)))
 have hsuccess := localTrans _ _ _ htest hh
 obtain ⟨hw⟩ := RawSuffixSearch.StatementChecks.exactWitness n p test I.toInstallation ctx l r stream line
 have hout := Hilbert.Local.mp (.base hw) hsuccess
 obtain ⟨hdata⟩ := HistoryRunSplice.LengthDataProof.lengthData n p I.lengthTag I.appendTag I.dropTag I.consTag I.hl I.ha I.hd I.hc ctx left right .zero
 have hlength : Derivation T (.equal (HistoryLengthOffset.lengthCall I.lengthTag stream) (.add l r)) :=
  .mp (.logical (.andRight _ _)) (.mp (.logical (.andRight _ _)) hdata)
 have hs : Derivation T (.equal (.succ (HistoryLengthOffset.lengthCall I.lengthTag stream)) (.succ (.add l r))) :=
  Hilbert.Local.finish (localUnary (.succ (.var 0)) _ _ (.base hlength))
 have hc := RawSuffixSearch.WitnessProof.countCongruence p [H] I.searchTag _ _ stream line hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hc hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof.nativeSuffix
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof.internalSuffix
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.Proof.internalCoverage
