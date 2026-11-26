module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.ReflexivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
def retentionInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawLogicalCoreRetention.Installation p (RawCumulativeLogical.logical old) a x := {
 ptag := I.ptag, ctag := I.ctag, ftag := I.ftag, ltag := I.ltag,
 oldTag := I.oldTag, newTag := I.btag, dtag := I.dtag, itag := I.itag, qctag := I.qctag,
 hp := I.hp, hc := I.hc, hf := I.hf, hl := I.hl, ho := I.hold, hn := I.hb,
 hd := I.hd, hi := I.hi, hqc := I.hqc }

theorem internalReflexivity : Targets.InternalReflexivity := by
 intro n p old a x I ctx t index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag t
 let G := [H]
 have ht : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawReflexivity.StatementChecks.exactInternalLine n p I.reflexivityTag I.ptag I.ctag I.atag
  I.hreflexivity I.hp I.hc I.ha ctx t
 obtain ⟨hv⟩ := RawReflexivityDispatcher.StatementChecks.exactEqualityValidity n p I.vtag I.ftag I.ptag I.ctag I.atag
  I.hv I.hf I.hp I.hc I.ha ctx t
 obtain ⟨hl⟩ := RawCumulativeLogical.StatementChecks.exactReflexivity n p old I.reflexivityTag I.oldTag I.ptag I.ctag I.atag I.vtag
  I.hreflexivity I.hold I.hp I.hc I.ha I.hv ctx t
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.oldTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) (.mp (.base hl) ht)
 obtain ⟨hc⟩ := RawLogicalCoreRetention.StatementChecks.exactCoreRetention n p (RawCumulativeLogical.logical old) a x
  (retentionInstallation p old a x I) ctx (eqRaw I.ctag I.atag t t) (Term.numeral 11)
  (HistoryLookup.consCall I.ctag t .zero) index fuel
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (.base hc) (.mp (.base hv) ht)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.ctag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (eqRaw I.ctag I.atag t t) (eqRaw I.ctag I.atag t t) ::ᵥ
   reflexivityCertificate I.ctag I.reflexivityTag t ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (eqRaw I.ctag I.atag t t) (eqRaw I.ctag I.atag t t) ::ᵥ
   RawLogicalCoreRetention.certificate I.ptag I.ctag (eqRaw I.ctag I.atag t t) (Term.numeral 11)
    (HistoryLookup.consCall I.ctag t .zero) ::ᵥ nil) (fun i => by
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

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.ReflexivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.ReflexivityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.ReflexivityProof.internalReflexivity
