module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.ProjectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.CompletionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open InvariantProof

theorem internalIteration : Targets.InternalIteration := by
 intro n p old a x I ctx count t u cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.vtag t
 let W := RawReflexivityDispatcher.valid I.vtag u
 let A := RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t u cert
 let G := [A,W,V]
 let s := state I.ptag t u cert
 let out := iteratorCall I.iteratorTag count s
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have ha : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have hin : Hilbert.Local T ctx G (contents I.vtag I.qctag I.ctag I.atag index fuel t u cert) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) ht) (.mp (.mp (.base (.logical (.andIntro _ _))) hu) ha)
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I t u cert
 have h1 := Hilbert.Local.mp (.mp (.base (moveFirst I.vtag I.qctag I.ctag I.atag index fuel t u cert (first I.leftTag s)))
  (.base (Support.equalitySymmetry _ _ hd1))) hin
 have h2 := Hilbert.Local.mp (.mp (.base (moveSecond I.vtag I.qctag I.ctag I.atag index fuel (first I.leftTag s) u cert (second I.leftTag I.rightTag s)))
  (.base (Support.equalitySymmetry _ _ hd2))) h1
 have h3 := Hilbert.Local.mp (.mp (.base (moveThird I.vtag I.qctag I.ctag I.atag index fuel (first I.leftTag s) (second I.leftTag I.rightTag s) cert (third I.rightTag s)))
  (.base (Support.equalitySymmetry _ _ hd3))) h2
 obtain ⟨hi⟩ := IterationProof.invariantIteration n p old a x I ctx count s index fuel
 have hout := Hilbert.Local.mp (.base hi) h3
 obtain ⟨hp⟩ := ProjectionProof.projections p old a x I count s
 have hp1 := Derivation.mp (.logical (.andLeft _ _)) hp
 have hp2 := Derivation.mp (.logical (.andRight _ _)) hp
 have he1 := HistoryAppend.PositiveProof.binaryCongruence I.prefixTag count count _ t (.logical (.reflexive count)) hd1
 have he2 := HistoryAppend.PositiveProof.binaryCongruence I.prefixTag count count _ u (.logical (.reflexive count)) hd2
 have hfirst := Logic.trans _ _ _ hp1 he1
 have hsecond := Logic.trans _ _ _ hp2 he2
 have hc1 := Hilbert.Local.mp (.mp (.base (moveFirst I.vtag I.qctag I.ctag I.atag index fuel
  (first I.leftTag out) (second I.leftTag I.rightTag out) (third I.rightTag out)
  (RawAdditionIteration.binaryCall I.prefixTag count t))) (.base hfirst)) hout
 have hc2 := Hilbert.Local.mp (.mp (.base (moveSecond I.vtag I.qctag I.ctag I.atag index fuel
  (RawAdditionIteration.binaryCall I.prefixTag count t) (second I.leftTag I.rightTag out) (third I.rightTag out)
  (RawAdditionIteration.binaryCall I.prefixTag count u))) (.base hsecond)) hc1
 have hfinal := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base hfirst))
  (.mp (.mp (.base (.logical (.andIntro _ _))) (.base hsecond)) hc2)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hfinal)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.CompletionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.CompletionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.CompletionProof.internalIteration
