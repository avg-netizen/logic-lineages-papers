module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityRecognizer
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem localBinding {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (vtag stag ptag ctag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (raw : Term ctx)
 (hscan : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag
   (LiteralNumeralPrefix.termTask ptag .zero) .zero) raw) (.succ .zero))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (leafCall vtag raw) (.succ .zero))) := by
 let args := raw ::ᵥ nil
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let tasks := HistoryLookup.consCall ctag task .zero
 have hz := constantValue p G args 0
 have ht : Computes p G (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0)) args task :=
  binary p G args HistoryCodec.pair _ _ .zero .zero task hz hz (copies p G _ ptag hp _)
 have hts : Computes p G termTasks args tasks :=
  binary p G args HistoryCodec.cons _ _ task .zero tasks ht hz (copies p G _ ctag hc _)
 have hscan' : Computes p G LiteralSyntaxScan.scanCode (tasks ::ᵥ raw ::ᵥ nil) (.succ .zero) := by
  intro tag htag
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag stag 2
   LiteralSyntaxScan.scanCode htag hs ctx (tasks ::ᵥ raw ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hscan⟩
 have hsc : Computes p G termScan args (.succ .zero) :=
  binary p G args LiteralSyntaxScan.scanCode _ _ tasks raw (.succ .zero)
   hts (projection p G args 0) hscan'
 exact binary p G args equalCode termScan (constant 1 1)
  (.succ .zero) (.succ .zero) (.succ .zero) hsc (constantValue p G args 1)
  (equalDiagonal p G (.succ .zero)) vtag hv

theorem internalSuccessorValidity : Targets.InternalSuccessorValidity := by
 intro n p vtag ptag ctag hv hp hc ctx raw
 obtain ⟨stag,hs⟩ := TermInternalProof.scanInstalled p vtag hv
 obtain ⟨hsound⟩ := RawReflexivityDispatcher.TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc raw
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hsucc⟩ := LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc .zero .zero raw
 have hscan := localTrans _ _ _ (.base hsucc) (.mp (.base hsound) hh)
 obtain ⟨hvout⟩ := localBinding p [H] vtag stag ptag ctag hv hs hp hc (RawSuccReplace.succValue ctag raw) hscan
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hvout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.ValidityProof.internalSuccessorValidity
