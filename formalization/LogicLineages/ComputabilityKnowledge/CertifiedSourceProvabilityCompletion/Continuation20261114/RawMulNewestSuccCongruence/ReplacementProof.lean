module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.ReplacementProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
theorem replacementCore {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t u index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawSuccReplace.formulaValue I.consTag I.appendTag t u) (RawSuccReplace.formulaValue I.consTag I.appendTag t u))
     (RawSuccReplaceCertificate.certificate I.consTag I.replaceTag t u)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag t
 let K := RawReflexivityDispatcher.valid I.validatorTag u
 let G := [K,H]
 have ht : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hu : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawSuccReplace.StatementChecks.exactInternalLine n p I.replaceTag I.pairTag I.consTag I.appendTag
  I.hreplace I.hp I.hc I.ha ctx t u
 obtain ⟨hv⟩ := RawSuccReplaceDispatcher.StatementChecks.exactFormulaValidity n p I.validatorTag I.ftag I.pairTag I.consTag I.appendTag
  I.hv I.hf I.hp I.hc I.ha ctx t u
 obtain ⟨hl⟩ := RawSuccReplace.StatementChecks.exactInternalLogical n p (ReflexivitySource.logical old) I.replaceTag I.cumulativeTag I.pairTag I.consTag I.appendTag I.validatorTag
  I.hreplace I.hcumulative I.hp I.hc I.ha I.hv ctx t u
 have hcum := Hilbert.Local.mp (.mp (.base hl) ht) hu
 obtain ⟨hr⟩ := RawLogicalRetention.StatementChecks.exactRetention n p (RawCumulativeLogical.logical old)
  I.cumulativeTag I.rightReplaceTag I.hcumulative I.hrightReplace ctx (RawSuccReplace.lineCall I.replaceTag t u)
 have hright := Hilbert.Local.mp (.base hr) hcum
 obtain ⟨ha⟩ := RawAddRightRetention.StatementChecks.exactRetention n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old))
  I.rightReplaceTag I.addRightTag I.hrightReplace I.haddRight ctx (RawSuccReplace.lineCall I.replaceTag t u)
 have hadd := Hilbert.Local.mp (.base ha) hright
 obtain ⟨hal⟩ := RawAddLeftRetention.StatementChecks.exactRetention n p (RawAddLeftCongruence.previousLogical old)
  I.addRightTag I.addLeftTag I.haddRight I.haddLeft ctx (RawSuccReplace.lineCall I.replaceTag t u)
 have hleft := Hilbert.Local.mp (.base hal) hadd
 obtain ⟨hmr⟩ := RawMulRightRetention.StatementChecks.exactRetention n p (RawMulRightCongruence.previousLogical old)
  I.addLeftTag I.previousTag I.haddLeft I.hprevious ctx (RawSuccReplace.lineCall I.replaceTag t u)
 have hprevious := Hilbert.Local.mp (.base hmr) hleft
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.previousTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hprevious
 obtain ⟨hc⟩ := RawMulLeftRetention.StatementChecks.exactCoreRetention n p (RawMulLeftCongruence.previousLogical old) a x
  (RawMulLeftCongruence.ReflexivityProof.retentionInstallation p old a x I.toNewestEquality.toCongruences.toNewest) ctx (RawSuccReplace.formulaValue I.consTag I.appendTag t u) (Term.numeral 12)
  (HistoryLookup.consCall I.consTag (RawSuccReplace.templateValue I.consTag I.appendTag t)
   (HistoryLookup.consCall I.consTag t (HistoryLookup.consCall I.consTag u .zero))) index fuel
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (.base hc) (.mp (.mp (.base hv) ht) hu)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.consTag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (RawSuccReplace.formulaValue I.consTag I.appendTag t u) (RawSuccReplace.formulaValue I.consTag I.appendTag t u) ::ᵥ
   RawSuccReplaceCertificate.certificate I.consTag I.replaceTag t u ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (RawSuccReplace.formulaValue I.consTag I.appendTag t u) (RawSuccReplace.formulaValue I.consTag I.appendTag t u) ::ᵥ
   RawMulLeftRetention.certificate I.pairTag I.consTag (RawSuccReplace.formulaValue I.consTag I.appendTag t u) (Term.numeral 12)
    (HistoryLookup.consCall I.consTag (RawSuccReplace.templateValue I.consTag I.appendTag t)
   (HistoryLookup.consCall I.consTag t (HistoryLookup.consCall I.consTag u .zero))) ::ᵥ nil) (fun i => by
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
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hcore)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.ReplacementProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.ReplacementProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.ReplacementProof.replacementCore
