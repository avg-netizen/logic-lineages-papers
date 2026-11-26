module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.ReplacementProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
theorem replacementCore {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (t u index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u))
     (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u)) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag t
 let K := RawReflexivityDispatcher.valid I.vtag u
 let G := [K,H]
 have ht : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hu : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 obtain ⟨hq⟩ := RawSuccReplace.StatementChecks.exactInternalLine n p I.replaceTag I.ptag I.ctag I.atag
  I.hreplace I.hp I.hc I.ha ctx t u
 obtain ⟨hv⟩ := RawSuccReplaceDispatcher.StatementChecks.exactFormulaValidity n p I.vtag I.ftag I.ptag I.ctag I.atag
  I.hv I.hf I.hp I.hc I.ha ctx t u
 obtain ⟨hl⟩ := RawSuccReplace.StatementChecks.exactInternalLogical n p (ReflexivitySource.logical old) I.replaceTag I.oldTag I.ptag I.ctag I.atag I.vtag
  I.hreplace I.hold I.hp I.hc I.ha I.hv ctx t u
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.oldTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) (.mp (.mp (.base hl) ht) hu)
 obtain ⟨hc⟩ := RawLogicalCoreRetention.StatementChecks.exactCoreRetention n p (RawCumulativeLogical.logical old) a x
  (RawEqualityComposition.ReflexivityProof.retentionInstallation p old a x I.toEquality) ctx (RawSuccReplace.formulaValue I.ctag I.atag t u) (Term.numeral 12)
  (HistoryLookup.consCall I.ctag (RawSuccReplace.templateValue I.ctag I.atag t)
   (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))) index fuel
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (.base hc) (.mp (.mp (.base hv) ht) hu)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.ctag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u) ::ᵥ
   RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u) ::ᵥ
   RawLogicalCoreRetention.certificate I.ptag I.ctag (RawSuccReplace.formulaValue I.ctag I.atag t u) (Term.numeral 12)
    (HistoryLookup.consCall I.ctag (RawSuccReplace.templateValue I.ctag I.atag t)
   (HistoryLookup.consCall I.ctag t (HistoryLookup.consCall I.ctag u .zero))) ::ᵥ nil) (fun i => by
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

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.ReplacementProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.ReplacementProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.ReplacementProof.replacementCore
