module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalStep : Targets.InternalStep := by
 intro n p old a x I ctx m u z cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let t := LiteralNumeralPrefix.numeralCall I.numeralTag m
 let v := LiteralNumeralPrefix.numeralCall I.numeralTag z
 let product := mulRaw I.ctag I.atag t u
 let prefProduct := RawAdditionIteration.binaryCall I.prefixTag m product
 let prefValue := RawAdditionIteration.binaryCall I.prefixTag m v
 let answer := LiteralNumeralPrefix.numeralCall I.numeralTag (.add z m)
 let sum := RawAdditionComputation.addRaw I.ctag I.atag product t
 let next := mulRaw I.ctag I.atag t (RawAdditionComputation.succRaw I.ctag u)
 let addCert := RawIteratedSucc.third I.rightTag (RawAdditionIteration.binaryCall I.iteratorTag m product)
 let congCert := RawIteratedSucc.third I.rightTag (RawIteratedSucc.iteratorCall I.congruenceIteratorTag m
  (RawIteratedSucc.state I.ptag product v cert))
 let mulCert := RawMultiplicationCertificates.SuccCertificate.certificate I.ctag I.mulSuccTag t u
 let innerCert := RawEqualityComposition.transitivityCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag
  sum prefProduct answer addCert congCert
 let V := RawReflexivityDispatcher.valid I.vtag u
 let A := RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel product v cert
 let G := [A,V]
 have hu : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨ht⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I.toEvaluator m
 obtain ⟨hv⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I.toEvaluator z
 obtain ⟨hanswer⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I.toEvaluator (.add z m)
 obtain ⟨hproduct⟩ := ValidityProof.internalMultiplicationValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t u
 have hpv := Hilbert.Local.mp (.mp (.base hproduct) (.base ht)) hu
 obtain ⟨hsum⟩ := RawAdditionComputation.StatementChecks.exactAdditionValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx product t
 have hsv := Hilbert.Local.mp (.mp (.base hsum) hpv) (.base ht)
 obtain ⟨hsucc⟩ := RawSuccCongruence.StatementChecks.exactSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx u
 have husv := Hilbert.Local.mp (.base hsucc) hu
 obtain ⟨hnext⟩ := ValidityProof.internalMultiplicationValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t (RawAdditionComputation.succRaw I.ctag u)
 have hnv := Hilbert.Local.mp (.mp (.base hnext) (.base ht)) husv
 obtain ⟨hadd⟩ := RawRetainedAdditionIteration.StatementChecks.exactIteration n p old a x I.toEvaluator ctx m product index fuel
 have haddState := Hilbert.Local.mp (.base hadd) hpv
 have haddTail := Hilbert.Local.mp (.base (.logical (.andRight _ _))) haddState
 have haddContents := Hilbert.Local.mp (.base (.logical (.andRight _ _))) haddTail
 have hprefv := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) haddContents
 have haddCore := Hilbert.Local.mp (.base (.logical (.andRight _ _))) haddContents
 obtain ⟨hcon⟩ := RawRetainedSuccIteration.StatementChecks.exactIteration n p old (RawRetainedAddition.arithmetic a) x
  (InstallationProof.congruenceInstallation p old a x I) ctx m product v cert index fuel
 have hconState := Hilbert.Local.mp (.mp (.mp (.base hcon) hpv) (.base hv)) hin
 have hconTail := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hconState
 have hconContents := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hconTail
 obtain ⟨he⟩ := RawRetainedAdditionIteration.PrefixProof.internalPrefixNumeral n p old a x I.toEvaluator ctx z m
 have hm := RawRetainedSuccIteration.InvariantProof.moveSecond (T := T) I.vtag I.qctag I.ctag I.atag
  index fuel prefProduct prefValue congCert answer
 have hconAnswer := Hilbert.Local.mp (.mp (.base hm) (.base he)) hconContents
 have hconAnswerTail := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hconAnswer
 have hconCore := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hconAnswerTail
 obtain ⟨hinner⟩ := RawEqualityComposition.StatementChecks.exactTransitivity n p old (RawRetainedAddition.arithmetic a) x
  I.toEvaluator.toAddition.toCongruence.toEquality ctx sum prefProduct answer addCert congCert index fuel
 have hinnerCore := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base hinner) hsv) hprefv) (.base hanswer)) haddCore) hconCore
 obtain ⟨hmul⟩ := RawMultiplicationCertificates.SuccCertificate.StatementChecks.exactCore n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawCumulativeArithmetic.arithmetic a) x
  (InstallationProof.succInstallation p old a x I) ctx t u index fuel
 have hmulCore := Hilbert.Local.mp (.mp (.base hmul) (.base ht)) hu
 obtain ⟨houter⟩ := RawEqualityComposition.StatementChecks.exactTransitivity n p old (RawRetainedAddition.arithmetic a) x
  I.toEvaluator.toAddition.toCongruence.toEquality ctx next sum answer mulCert innerCert index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base houter) hnv) hsv) (.base hanswer)) hmulCore) hinnerCore
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.StepProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.StepProof.internalStep
