module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.SplitProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

def prefix {ctx : Nat} (c : Nat) : List Nat → Term ctx → Term ctx
 | [], v => v
 | a::xs, v => HistoryLookup.consCall c (Term.numeral a) (prefix c xs v)
theorem appendPrefix {n ctx : Nat} (p : Program n) (old : Program 1) (I : Installation p old)
 (xs : List Nat) (v : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (HistoryAppend.appendCall I.appendTag (prefix I.consTag xs .zero) v) (prefix I.consTag xs v))) := by
 induction xs with
 | nil => exact HistoryAppend.AppendEquationsProof.internalAppendNil n p I.appendTag I.ha ctx v
 | cons a xs ih =>
  obtain ⟨h⟩ := HistoryAppend.ConsProof.internalAppendCons n p I.appendTag I.consTag I.ha I.hc ctx (Term.numeral a) (prefix I.consTag xs .zero) v
  obtain ⟨hi⟩ := ih
  have hc := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.consTag
   (Term.numeral a) _ (Term.numeral a) _ (.base (.logical (.reflexive _))) (.base hi)
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base h) hc)⟩

theorem internalSplit : Targets.InternalSplit := by
 intro n p old I ctx t v
 let T := GorbowPRNumeralCalculation.Theory p
 let A := RawAddRightReplace.binaryValue I.consTag I.appendTag 3 t v
 let z2 : Term ctx := prefix I.consTag [0,0] .zero
 let z3 : Term ctx := prefix I.consTag [3,0,0] .zero
 obtain ⟨h2⟩ := appendPrefix p old I [0,0] v
 obtain ⟨h3⟩ := appendPrefix p old I [3,0,0] v
 have hright := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := []) I.consTag
  (Term.numeral 3) _ (Term.numeral 3) _ (.base (.logical (.reflexive _))) (.base h2)
 have hinner := localTrans _ _ _ hright (.base (Support.equalitySymmetry _ _ h3))
 have hA := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := []) I.appendTag
  A _ A _ (.base (.logical (.reflexive A))) hinner
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.StatementChecks.appendAssociativity n p I.appendTag I.consTag I.leftDecoderTag I.rightDecoderTag I.ha I.hc I.hleft I.hright ctx A z3 v
 have hmiddle := localTrans _ _ _ hA (.base (Support.equalitySymmetry _ _ hassoc))
 have hout := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := []) I.consTag
  (.zero : Term ctx) _ .zero _ (.base (.logical (.reflexive _))) hmiddle
 obtain ⟨houter⟩ := HistoryAppend.ConsProof.internalAppendCons n p I.appendTag I.consTag I.ha I.hc ctx .zero (HistoryAppend.appendCall I.appendTag A z3) v
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ hout (.base (Support.equalitySymmetry _ _ houter)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.SplitProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.SplitProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.SplitProof.appendPrefix
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.SplitProof.internalSplit
