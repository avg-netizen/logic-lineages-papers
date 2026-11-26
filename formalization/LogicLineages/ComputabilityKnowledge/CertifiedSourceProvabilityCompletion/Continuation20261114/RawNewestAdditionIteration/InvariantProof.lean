module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open RawIteratedSucc InvariantSupport

theorem baseProperty {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (property I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag I.prefixTag .zero t index fuel (binaryCall I.iteratorTag .zero t)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag t
 let G := [H]
 have ht : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let z := RawAdditionComputation.zeroRaw I.consTag (ctx := ctx)
 let cert := RawCumulativeArithmetic.certificate I.consTag I.zeroTag t
 let out := binaryCall I.iteratorTag .zero t
 obtain ⟨hi⟩ := EquationsProof.iteratorZero p old a x I t
 obtain ⟨hb⟩ := ConstructorProof.internalBase n p old a x I ctx t
 have hout := Logic.trans _ _ _ hi hb
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I z t cert
 have h1 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hout) hd1
 have hr := HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hout
 have h2 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hr) hd2
 have h3 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hr) hd3
 obtain ⟨hn⟩ := LiteralNumeralPrefix.EquationsProof.zero p I.numeralTag I.consTag I.hnumeral I.hc (ctx := ctx)
 obtain ⟨hp⟩ := EquationsProof.prefixZero p old a x I t
 obtain ⟨hc⟩ := RawNewestAddition.StatementChecks.exactBase n p old a x I.toAddition ctx t index fuel
 have hc0 : Hilbert.Local T ctx G (contents I.validatorTag I.qctag I.consTag I.appendTag index fuel t z t cert) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) ht) (.mp (.base hc) ht)
 have hc1 := Hilbert.Local.mp (.mp (.base (moveFirst I.validatorTag I.qctag I.consTag I.appendTag index fuel t z t cert
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero))) (.base (Support.equalitySymmetry _ _ hn))) hc0
 have hc2 := Hilbert.Local.mp (.mp (.base (moveSecond I.validatorTag I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero) t cert (binaryCall I.prefixTag .zero t))) (.base (Support.equalitySymmetry _ _ hp))) hc1
 have hc3 := Hilbert.Local.mp (.mp (.base (moveThird I.validatorTag I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero) (binaryCall I.prefixTag .zero t) cert (third I.rightTag out)))
  (.base (Support.equalitySymmetry _ _ h3))) hc2
 have hfirst := Logic.trans _ _ _ h1 (Support.equalitySymmetry _ _ hn)
 have hsecond := Logic.trans _ _ _ h2 (Support.equalitySymmetry _ _ hp)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (.logical (.andIntro _ _))) (.base hfirst))
   (.mp (.mp (.base (.logical (.andIntro _ _))) (.base hsecond)) hc3)))⟩

theorem stepProperty {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count t index fuel s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (property I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag I.prefixTag count t index fuel s)
    (property I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag I.prefixTag (.succ count) t index fuel (binaryCall I.stepTag t s))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let H := property I.validatorTag I.qctag I.consTag I.appendTag I.leftTag I.rightTag I.numeralTag I.prefixTag count t index fuel s
 let G := [H,V]
 let num := LiteralNumeralPrefix.numeralCall I.numeralTag count
 let val := binaryCall I.prefixTag count t
 let cert := third I.rightTag s
 let sn := RawAdditionComputation.succRaw I.consTag num
 let sv := RawAdditionComputation.succRaw I.consTag val
 let nextCert := RawAdditionComputation.stepCertificate I.mpTag I.equalityLineTag I.replaceTag I.reflexivityTag I.addTag I.consTag I.appendTag t num val cert
 let out := binaryCall I.stepTag t s
 have ht : Hilbert.Local T ctx G V := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hfirst := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 have hsecond := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hcontents := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrest
 have hval := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcontents
 have hcert := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcontents
 obtain ⟨hnv⟩ := numeralValid p old a x I count
 obtain ⟨hsv⟩ := RawSuccCongruence.StatementChecks.exactSuccessorValidity n p I.validatorTag I.pairTag I.consTag I.hv I.hp I.hc ctx val
 have hsvValid := Hilbert.Local.mp (.base hsv) hval
 obtain ⟨hstep⟩ := RawNewestAddition.StatementChecks.exactStep n p old a x I.toAddition ctx t num val cert index fuel
 have hcomputed := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hstep) ht) (.base hnv)) hval) hcert
 have hc0 : Hilbert.Local T ctx G (contents I.validatorTag I.qctag I.consTag I.appendTag index fuel t sn sv nextCert) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hsvValid) hcomputed
 obtain ⟨hr⟩ := reconstructState p old a x I s
 have htail := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.pairTag _ cert _ cert hsecond (.base (.logical (.reflexive cert)))
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.pairTag _ _ _ _ hfirst htail
 have hcanonical := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hr)) hpair
 have hstepEq := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.stepTag t _ t _
  (.base (.logical (.reflexive t))) hcanonical
 obtain ⟨hctor⟩ := ConstructorProof.internalStep n p old a x I ctx t num val cert
 have hout := localTrans _ _ _ hstepEq (.base hctor)
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I sn sv nextCert
 have h1 := localTrans _ _ _ (unaryLocal I.leftTag _ _ hout) (.base hd1)
 have hright := unaryLocal I.rightTag _ _ hout
 have h2 := localTrans _ _ _ (unaryLocal I.leftTag _ _ hright) (.base hd2)
 have h3 := localTrans _ _ _ (unaryLocal I.rightTag _ _ hright) (.base hd3)
 obtain ⟨hn⟩ := LiteralNumeralPrefix.EquationsProof.successor p I.numeralTag I.consTag I.hnumeral I.hc count
 obtain ⟨hp⟩ := EquationsProof.prefixSuccessor p old a x I count t
 have hc1 := Hilbert.Local.mp (.mp (.base (moveFirst I.validatorTag I.qctag I.consTag I.appendTag index fuel t sn sv nextCert
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)))) (.base (Support.equalitySymmetry _ _ hn))) hc0
 have hc2 := Hilbert.Local.mp (.mp (.base (moveSecond I.validatorTag I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)) sv nextCert (binaryCall I.prefixTag (.succ count) t))) (.base (Support.equalitySymmetry _ _ hp))) hc1
 have hc3 := Hilbert.Local.mp (.mp (.base (moveThird I.validatorTag I.qctag I.consTag I.appendTag index fuel t
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)) (binaryCall I.prefixTag (.succ count) t) nextCert (third I.rightTag out)))
  (.mp (.base (Logic.symmetryRule T _ _)) h3)) hc2
 have hfirstOut := localTrans _ _ _ h1 (.base (Support.equalitySymmetry _ _ hn))
 have hsecondOut := localTrans _ _ _ h2 (.base (Support.equalitySymmetry _ _ hp))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (.mp (.mp (.base (.logical (.andIntro _ _))) hfirstOut)
   (.mp (.mp (.base (.logical (.andIntro _ _))) hsecondOut) hc3))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantProof.baseProperty
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAdditionIteration.InvariantProof.stepProperty
