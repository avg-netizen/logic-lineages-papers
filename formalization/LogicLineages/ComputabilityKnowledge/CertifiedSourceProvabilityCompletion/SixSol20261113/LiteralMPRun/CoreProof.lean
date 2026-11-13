module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.ConstructedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryRunSplice LiteralRawMP

theorem internalCoreAcceptance : Targets.InternalCoreAcceptance := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag qtag hm hq ctx context phi psi imp ant tailI tailA index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
  let V := newLineValid tag ltag ptag v l a x context psi ant
  let G := [V,H]
  let code := certificate mtag context psi imp ant
  let history := joinedHistory atag ptag ctag context phi psi tailI tailA
  let it := qtag+LiteralCheckerAcceptance.iteratorOffset v l a x
  have hH : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
  have hV : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
  obtain ⟨hrun⟩ := ConstructedProof.internalConstructedRun v l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht mtag hm ctx context phi psi imp ant tailI tailA index fuel
  have hresult := Hilbert.Local.mp (.mp (.base hrun) hH) hV
  obtain ⟨hf,hiter⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p qtag v l a x hq
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it itag 4
    (SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)) hiter hi ctx
    (code ::ᵥ state ptag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  have hstate := localTrans _ _ _ (.base hcopy) hresult
  obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (qtag+1) ptag ctag hf hp hc
    (LiteralCheckerAcceptance.runCall it ptag index fuel code) context (.add psi psi) code psi history
  have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body ptag ctag
      (LiteralCheckerAcceptance.runCall it ptag index fuel code) context (.add psi psi) psi history) :=
    .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive (.add psi psi))))) hstate
  have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
  obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p qtag ptag v l a x hq hp ctx index fuel context (.add psi psi) code
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (localTrans _ _ _ (.base hnorm) hfinish)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.CoreProof
