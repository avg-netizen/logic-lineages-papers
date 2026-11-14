module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.ReplacementProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof

theorem internalReplacement : Targets.InternalReplacement := by
 intro n p old a x I ctx t u v index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let Z := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [Z,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G Z := .hypothesis List.mem_cons_self
 obtain ⟨hlog⟩ := RawRightReplace.StatementChecks.exactInternalLogical n p (RawCumulativeLogical.logical old)
  I.equalityLineTag I.rightReplaceTag I.pairTag I.consTag I.appendTag I.validatorTag
  I.hequalityLine I.hrightReplace I.hp I.hc I.ha I.hv ctx t u v
 have hright := Hilbert.Local.mp (.mp (.mp (.base hlog) ht) hu) hv
 obtain ⟨hretain⟩ := RawAddRightRetention.StatementChecks.exactRetention n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old))
  I.rightReplaceTag I.previousTag I.hrightReplace I.hprevious ctx (RawRightReplace.lineCall I.equalityLineTag t u v)
 have haccepted := Hilbert.Local.mp (.base hretain) hright
 obtain ⟨hq⟩ := RawRightReplace.StatementChecks.exactInternalLine n p I.equalityLineTag I.pairTag I.consTag I.appendTag
  I.hequalityLine I.hp I.hc I.ha ctx t u v
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.previousTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) haccepted
 obtain ⟨hvalid⟩ := RawRightReplaceDispatcher.StatementChecks.exactFormulaValidity n p I.validatorTag I.ftag I.pairTag I.consTag I.appendTag
  I.hv I.hf I.hp I.hc I.ha ctx t u v
 let formula := RawRightReplace.formulaValue I.consTag I.appendTag t u v
 let args := HistoryLookup.consCall I.consTag (RawRightReplace.templateValue I.consTag v)
  (HistoryLookup.consCall I.consTag t (HistoryLookup.consCall I.consTag u .zero))
 obtain ⟨hc⟩ := RawAddLeftRetention.StatementChecks.exactCoreRetention n p (RawAddLeftCongruence.previousLogical old) a x
  (RawAddLeftCongruence.ReflexivityProof.retentionInstallation p old a x I.toCongruences.toNewest)
  ctx formula (Term.numeral 12) args index fuel
 have hcore := Hilbert.Local.mp (.mp (.base hc) (.mp (.mp (.mp (.base hvalid) ht) hu) hv)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.consTag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ RawRightReplaceCertificate.certificate I.consTag I.equalityLineTag t u v ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ RawAddLeftRetention.certificate I.pairTag I.consTag formula (Term.numeral 12) args ::ᵥ nil) (fun i => by
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
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hcore))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.ReplacementProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.ReplacementProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.ReplacementProof.internalReplacement
