module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CodeTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem exactCertificate : Targets.InternalCertificate := by
 intro f lhs rhs k t rawOld ar baseX pF pR
 dsimp only
 intro I isExists lineTag singletonTag hline hsingle ctx a b index fuel
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let J : Installation p f lhs rhs rawOld (CumulativePropositionalSource.arithmetic ar)
  (SaturatedAxiomLeaf.saturated baseX) isExists :=
  { toInstallation := I.currentK, quantifierTag := lineTag, singletonTag := singletonTag,
    h_quantifierTag := hline, h_singletonTag := hsingle }
 let T := GorbowPRNumeralCalculation.Theory p
 let A := OriginalQuantifierLogicalExtension.guards isExists J.fval a b
 let G := [A]
 let C := OriginalQuantifierLogicalProducers.conclusionValue isExists J.ctag J.atag a b
 have hh : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hr⟩ := RunProof.internalRawSingletonRun p f lhs rhs rawOld _ _ isExists J a b index fuel
 obtain ⟨hc⟩ := CoreProof.internalCore p f lhs rhs rawOld _ _ isExists J a b index fuel
 obtain ⟨he⟩ := CodeTransport.singleton p f lhs rhs rawOld _ _ isExists J a b
 have hrun := localTrans _ _ _
  (CodeTransport.run T G J.iteratorTag J.ptag index fuel _ _ (.base he)) (.mp (.base hr) hh)
 have hraw := Hilbert.Local.mp (.base hc) hh
 obtain ⟨hcore⟩ := CurrentImplicationCertificate.RebaseProof.coreCode T G J.coreTag index fuel C
  (rawCertificate J.ctag J.quantifierTag a b) (certificate J.singletonTag a b)
  (.base (Support.equalitySymmetry _ _ he)) hraw
 obtain ⟨hinj⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p J.verifierTag J.coreTag (checker f lhs rhs rawOld (CumulativePropositionalSource.arithmetic ar)
   (SaturatedAxiomLeaf.saturated baseX)) J.h_verifierTag J.h_coreTag
  index fuel .zero (.add C C) (certificate J.singletonTag a b)
 have hfuel := Hilbert.Local.mp (.base hinj) hcore
 have hcf := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hcore) hfuel
 have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hrun) hcf
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Proof
