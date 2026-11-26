module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof

def retentionInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawArithmeticCoreRetention.Installation p
 (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawCumulativeArithmetic.arithmetic a) x := {
 ptag := I.ptag, ctag := I.ctag, ftag := I.ftag, ltag := I.ltag,
 oldTag := I.oldArithmeticTag, newTag := I.arithmeticTag, dtag := I.dtag, itag := I.itag, qctag := I.qctag,
 hp := I.hp, hc := I.hc, hf := I.hf, hl := I.hl, ho := I.holdArithmetic, hn := I.harithmetic,
 hd := I.hd, hi := I.hi, hqc := I.hqc }

noncomputable def localCore {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (G : List (Formula ctx)) (formula payload ann qline index fuel : Term ctx)
 (hq : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal qline (RawArithmeticCoreRetention.line I.ptag formula payload ann)))
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero)))
 (hl : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall I.oldArithmeticTag qline) (.succ .zero))) :
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero (.add formula formula)
   (HistoryLookup.consCall I.ctag qline .zero)) (.succ .zero)) := by
 apply Classical.choice
 let T := GorbowPRNumeralCalculation.Theory p
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.oldArithmeticTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hl
 obtain ⟨hc⟩ := RawArithmeticCoreRetention.StatementChecks.exactCoreRetention n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawCumulativeArithmetic.arithmetic a) x
  (retentionInstallation p old a x I) ctx formula payload ann index fuel
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (.base hc) hv) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.ctag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ HistoryLookup.consCall I.ctag qline .zero ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ
   RawArithmeticCoreRetention.certificate I.ptag I.ctag formula payload ann ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive _))
       | succ i => cases i using Fin.cases with
         | zero => exact .base (.logical (.reflexive _))
         | succ i => cases i using Fin.cases with
           | zero => exact .base hcert
           | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ hcg hcore⟩

theorem internalBase : Targets.InternalBase := by
 intro n p old a x I ctx t index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag t
 have ht : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawAddZero.StatementChecks.exactInternalLine n p I.zeroTag I.ptag I.ctag I.atag
  I.hzero I.hp I.hc I.ha ctx t
 obtain ⟨hv⟩ := RawAddZeroDispatcher.StatementChecks.exactFormulaValidity n p I.vtag I.ftag I.ptag I.ctag I.atag
  I.hv I.hf I.hp I.hc I.ha ctx t
 obtain ⟨hl⟩ := RawCumulativeArithmetic.StatementChecks.exactAddZero n p a I.zeroTag I.oldArithmeticTag I.ptag I.ctag I.atag I.vtag
  I.hzero I.holdArithmetic I.hp I.hc I.ha I.hv ctx t
 have h := localCore p old a x I [H] (RawAddZero.equalityValue I.ctag I.atag t) (Term.numeral 2)
  (HistoryLookup.consCall I.ctag t .zero) (RawAddZero.lineCall I.zeroTag t) index fuel hq
  (.mp (.base hv) ht) (.mp (.base hl) ht)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

theorem additionAxiom {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t u index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddSucc.equalityValue I.ctag I.atag t u) (RawAddSucc.equalityValue I.ctag I.atag t u))
     (RawAddSuccCertificate.certificate I.ctag I.addTag t u)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag t
 let K := RawReflexivityDispatcher.valid I.vtag u
 let G := [K,H]
 have ht : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hu : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawAddSucc.StatementChecks.exactInternalLine n p I.addTag I.ptag I.ctag I.atag I.hadd I.hp I.hc I.ha ctx t u
 obtain ⟨hv⟩ := RawAddSuccDispatcher.StatementChecks.exactFormulaValidity n p I.vtag I.ftag I.ptag I.ctag I.atag I.hv I.hf I.hp I.hc I.ha ctx t u
 obtain ⟨hl⟩ := RawAddSucc.StatementChecks.exactInternalArithmetic n p (RawAddZero.arithmeticLeaf a)
  I.addTag I.oldArithmeticTag I.ptag I.ctag I.atag I.vtag I.hadd I.holdArithmetic I.hp I.hc I.ha I.hv ctx t u
 have h := localCore p old a x I G (RawAddSucc.equalityValue I.ctag I.atag t u) (Term.numeral 3)
  (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))
  (RawAddSucc.lineCall I.addTag t u) index fuel hq
  (.mp (.mp (.base hv) ht) hu) (.mp (.mp (.base hl) ht) hu)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge h))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof.localCore
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof.internalBase
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof.additionAxiom
