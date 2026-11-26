module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RawIteratedSucc (first second third state)
open RawAdditionIteration (binaryCall)
open InvariantSupport
noncomputable def moveRight {T : Sentence → Prop} {ctx : Nat} q c a (index fuel t v cert w : Term ctx) :
 Derivation T (.imp (.equal v w)
  (.imp (RawEqualityComposition.accepted q c a index fuel t v cert)
   (RawEqualityComposition.accepted q c a index fuel t w cert))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (RawEqualityComposition.accepted q c a (liftTerm index) (liftTerm fuel) (liftTerm t) (.var 0) (liftTerm cert)) v w)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,RawEqualityComposition.accepted,
  RawEqualityComposition.eqRaw,RawSuccReplace.binaryValue,HistoryLookup.consCall,HistoryAppend.appendCall,
  LiteralCheckerAcceptance.coreCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  substituteFormula,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem baseProperty {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (m index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag .zero m index fuel
   (binaryCall I.mulIteratorTag .zero m))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let t := LiteralNumeralPrefix.numeralCall I.numeralTag m
 let zr := RawAdditionComputation.zeroRaw I.ctag (ctx := ctx)
 let cert := RawMultiplicationCertificates.ZeroCertificate.certificate I.ctag I.mulZeroTag t
 let out := binaryCall I.mulIteratorTag .zero m
 obtain ⟨hi⟩ := EquationsProof.iteratorZero p old a x I m
 obtain ⟨hb⟩ := ConstructorProof.internalBase n p old a x I ctx m
 have hout := Logic.trans _ _ _ hi hb
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I.toComputation.toEvaluator zr .zero cert
 have h1 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hout) hd1
 have hr := HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hout
 have h2 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.leftTag _ _ hr) hd2
 have h3 := Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence I.rightTag _ _ hr) hd3
 obtain ⟨hn⟩ := LiteralNumeralPrefix.EquationsProof.zero p I.numeralTag I.ctag I.hnumeral I.hc (ctx := ctx)
 have hm : Derivation T (.equal (.mul m .zero) .zero) := .arithmetic (.mulZero m)
 obtain ⟨ht⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I.toComputation.toEvaluator m
 obtain ⟨hc⟩ := RawMultiplicationComputation.StatementChecks.exactBase n p old a x I.toComputation ctx t index fuel
 have hc0 := Derivation.mp hc ht
 have hc1 : Derivation T (contents I.qctag I.ctag I.atag I.numeralTag index fuel m zr .zero cert) :=
  .mp (.mp (moveRight I.qctag I.ctag I.atag index fuel (RawMultiplicationComputation.mulRaw I.ctag I.atag t zr) zr cert
   (LiteralNumeralPrefix.numeralCall I.numeralTag .zero)) (Support.equalitySymmetry _ _ hn)) hc0
 have hc2 := Derivation.mp (.mp (moveFirst I.qctag I.ctag I.atag I.numeralTag index fuel m zr .zero cert
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero)) (Support.equalitySymmetry _ _ hn)) hc1
 have hc3 := Derivation.mp (.mp (moveSecond I.qctag I.ctag I.atag I.numeralTag index fuel m
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero) .zero cert (.mul m .zero)) (Support.equalitySymmetry _ _ hm)) hc2
 have hc4 := Derivation.mp (.mp (moveThird I.qctag I.ctag I.atag I.numeralTag index fuel m
  (LiteralNumeralPrefix.numeralCall I.numeralTag .zero) (.mul m .zero) cert (third I.rightTag out)) (Support.equalitySymmetry _ _ h3)) hc3
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) (Logic.trans _ _ _ h1 (Support.equalitySymmetry _ _ hn)))
  (.mp (.mp (.logical (.andIntro _ _)) (Logic.trans _ _ _ h2 (Support.equalitySymmetry _ _ hm))) hc4)⟩

theorem stepProperty {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (count m index fuel s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag count m index fuel s)
   (property I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag (.succ count) m index fuel
    (binaryCall I.mulStepTag m s)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := property I.qctag I.ctag I.atag I.leftTag I.rightTag I.numeralTag count m index fuel s
 let G := [H]
 let num := LiteralNumeralPrefix.numeralCall I.numeralTag count
 let val := Term.mul m count
 let cert := third I.rightTag s
 let sn := RawAdditionComputation.succRaw I.ctag num
 let sv := Term.add val m
 let nextCert := RawMultiplicationComputation.stepCertificate I.mpTag I.qtag I.reflexivityTag I.mulSuccTag I.iteratorTag
  I.congruenceIteratorTag I.numeralTag I.prefixTag I.ptag I.ctag I.atag I.rightTag m num val cert
 let out := binaryCall I.mulStepTag m s
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hfirst := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 have hsecond := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hcontents := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrest
 obtain ⟨hnv⟩ := RawRetainedAdditionIteration.InvariantSupport.numeralValid p old a x I.toComputation.toEvaluator count
 obtain ⟨hstep⟩ := RawMultiplicationComputation.StatementChecks.exactStep n p old a x I.toComputation ctx m num val cert index fuel
 have hc0 : Hilbert.Local T ctx G (contents I.qctag I.ctag I.atag I.numeralTag index fuel m sn sv nextCert) :=
  .mp (.mp (.base hstep) (.base hnv)) hcontents
 obtain ⟨hr⟩ := reconstructState p old a x I.toComputation.toEvaluator s
 have htail := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ cert _ cert hsecond (.base (.logical (.reflexive cert)))
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ _ _ _ hfirst htail
 have hcanonical := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hr)) hpair
 have hstepEq := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.mulStepTag m _ m _
  (.base (.logical (.reflexive m))) hcanonical
 obtain ⟨hctor⟩ := ConstructorProof.internalStep n p old a x I ctx m num val cert
 have hout := localTrans _ _ _ hstepEq (.base hctor)
 obtain ⟨⟨hd1⟩,⟨hd2⟩,⟨hd3⟩⟩ := decodeState p old a x I.toComputation.toEvaluator sn sv nextCert
 have h1 := localTrans _ _ _ (unaryLocal I.leftTag _ _ hout) (.base hd1)
 have hright := unaryLocal I.rightTag _ _ hout
 have h2 := localTrans _ _ _ (unaryLocal I.leftTag _ _ hright) (.base hd2)
 have h3 := localTrans _ _ _ (unaryLocal I.rightTag _ _ hright) (.base hd3)
 obtain ⟨hn⟩ := LiteralNumeralPrefix.EquationsProof.successor p I.numeralTag I.ctag I.hnumeral I.hc count
 have hm : Derivation T (.equal (.mul m (.succ count)) (.add (.mul m count) m)) := .arithmetic (.mulSucc m count)
 have hc1 := Hilbert.Local.mp (.mp (.base (moveFirst I.qctag I.ctag I.atag I.numeralTag index fuel m sn sv nextCert
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)))) (.base (Support.equalitySymmetry _ _ hn))) hc0
 have hc2 := Hilbert.Local.mp (.mp (.base (moveSecond I.qctag I.ctag I.atag I.numeralTag index fuel m
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)) sv nextCert (.mul m (.succ count)))) (.base (Support.equalitySymmetry _ _ hm))) hc1
 have hc3 := Hilbert.Local.mp (.mp (.base (moveThird I.qctag I.ctag I.atag I.numeralTag index fuel m
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ count)) (.mul m (.succ count)) nextCert (third I.rightTag out)))
  (.mp (.base (Logic.symmetryRule T _ _)) h3)) hc2
 have hfirstOut := localTrans _ _ _ h1 (.base (Support.equalitySymmetry _ _ hn))
 have hsecondOut := localTrans _ _ _ h2 (.base (Support.equalitySymmetry _ _ hm))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (.logical (.andIntro _ _))) hfirstOut)
   (.mp (.mp (.base (.logical (.andIntro _ _))) hsecondOut) hc3)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantProof.baseProperty
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationIteration.InvariantProof.stepProperty
