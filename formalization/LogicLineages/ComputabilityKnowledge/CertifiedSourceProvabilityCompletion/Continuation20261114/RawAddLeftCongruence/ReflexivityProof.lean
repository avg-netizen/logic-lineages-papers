module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.ReflexivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
def retentionInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawAddLeftRetention.Installation p (previousLogical old) a x := {
 ptag := I.pairTag, ctag := I.consTag, ftag := I.ftag, ltag := I.ltag,
 oldTag := I.previousTag, newTag := I.logicalTag, dtag := I.dtag, itag := I.itag, qctag := I.qctag,
 hp := I.hp, hc := I.hc, hf := I.hf, hl := I.hlineValidator, ho := I.hprevious, hn := I.hlogical,
 hd := I.hdispatcher, hi := I.hi, hqc := I.hqc }

theorem internalReflexivity : Targets.InternalReflexivity := by
 intro n p old a x I ctx t index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag t
 let G := [H]
 have ht : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawReflexivity.StatementChecks.exactInternalLine n p I.reflexivityTag I.pairTag I.consTag I.appendTag
  I.hreflexivity I.hp I.hc I.ha ctx t
 obtain ⟨hv⟩ := RawReflexivityDispatcher.StatementChecks.exactEqualityValidity n p I.validatorTag I.ftag I.pairTag I.consTag I.appendTag
  I.hv I.hf I.hp I.hc I.ha ctx t
 obtain ⟨hl⟩ := RawCumulativeLogical.StatementChecks.exactReflexivity n p old I.reflexivityTag I.cumulativeTag I.pairTag I.consTag I.appendTag I.validatorTag
  I.hreflexivity I.hcumulative I.hp I.hc I.ha I.hv ctx t
 obtain ⟨hretain⟩ := RawLogicalRetention.StatementChecks.exactRetention n p (RawCumulativeLogical.logical old)
  I.cumulativeTag I.rightReplaceTag I.hcumulative I.hrightReplace ctx (RawReflexivity.lineCall I.reflexivityTag t)
 have hright := Hilbert.Local.mp (.base hretain) (.mp (.base hl) ht)
 obtain ⟨hretainAdd⟩ := RawAddRightRetention.StatementChecks.exactRetention n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old))
  I.rightReplaceTag I.previousTag I.hrightReplace I.hprevious ctx (RawReflexivity.lineCall I.reflexivityTag t)
 have hprevious := Hilbert.Local.mp (.base hretainAdd) hright
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.previousTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hprevious
 obtain ⟨hc⟩ := RawAddLeftRetention.StatementChecks.exactCoreRetention n p (previousLogical old) a x
  (retentionInstallation p old a x I) ctx (eqRaw I.consTag I.appendTag t t) (Term.numeral 11)
  (HistoryLookup.consCall I.consTag t .zero) index fuel
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (.base hc) (.mp (.base hv) ht)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.consTag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (eqRaw I.consTag I.appendTag t t) (eqRaw I.consTag I.appendTag t t) ::ᵥ
   RawCumulativeLogical.certificate I.consTag I.reflexivityTag t ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (eqRaw I.consTag I.appendTag t t) (eqRaw I.consTag I.appendTag t t) ::ᵥ
   RawAddLeftRetention.certificate I.pairTag I.consTag (eqRaw I.consTag I.appendTag t t) (Term.numeral 11)
    (HistoryLookup.consCall I.consTag t .zero) ::ᵥ nil) (fun i => by
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
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcg hcore))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.ReflexivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.ReflexivityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCongruence.ReflexivityProof.internalReflexivity
