module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CodeTransport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem singleton {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1)
 (rawOld arithmetic : Program 1) (x : Program 3) (isExists : Bool)
 (I : Installation p f lhs rhs rawOld arithmetic x isExists) (a b : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (certificate I.singletonTag a b) (rawCertificate I.ctag I.quantifierTag a b))) :=
 (OriginalQuantifierLogicalProducers.StatementChecks.exactInternal n p isExists I.ptag I.ctag I.atag
  I.quantifierTag I.singletonTag ⟨I.h_ptag,I.h_ctag,I.h_atag⟩ I.h_quantifierTag I.h_singletonTag ctx a b).2

noncomputable def run {ctx : Nat} (T : Sentence → Prop) (G : List (Formula ctx)) (itag ptag : Nat)
 (index fuel old new : Term ctx) (h : Hilbert.Local T ctx G (.equal old new)) :
 Hilbert.Local T ctx G (.equal (LiteralCheckerAcceptance.runCall itag ptag index fuel old)
  (LiteralCheckerAcceptance.runCall itag ptag index fuel new)) := by
 have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) ptag
  (.succ .zero) old (.succ .zero) new (.base (.logical (.reflexive _))) h
 apply LiteralRawMP.DispatcherSupportProof.callCongruence (T := T) (G := G) itag
  (old ::ᵥ HistoryKernel.pairCall ptag (.succ .zero) old ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  (new ::ᵥ HistoryKernel.pairCall ptag (.succ .zero) new ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => cases i using Fin.cases with
  | zero => exact hs
  | succ i => cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive index))
   | succ i => cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive fuel))
    | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CodeTransport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CodeTransport
