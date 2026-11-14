module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.AppendBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.BoundProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryCancellation.TransitivityProof

theorem internalCandidateBound : Targets.InternalCandidateBound := by
 intro n p ptag ctag atag lengthTag dropTag hp hc ha hl hd ctx t u v
 let T := GorbowPRNumeralCalculation.Theory p
 have trans (a b c : Term ctx) (h : Derivation T (weakBound a b)) (k : Derivation T (weakBound b c)) :
  Derivation T (weakBound a c) := by
  apply Classical.choice
  obtain ⟨ht⟩ := weakTrans T a b c
  exact ⟨.mp (.mp ht h) k⟩
 have app (a b : Term ctx) : Derivation T (weakBound a (HistoryAppend.appendCall atag a b)) := by
  apply Classical.choice
  exact AppendBoundProof.lengthData n p lengthTag atag dropTag ctag hl ha hd hc ctx a b .zero
 have consLeft (a b : Term ctx) : Derivation T (weakBound a (HistoryLookup.consCall ctag a b)) := by
  apply Classical.choice
  obtain ⟨h⟩ := HistoryBounds.ConsProof.consFirstStrictBound n p ctag hc ctx a b
  obtain ⟨hw⟩ := HistoryCancellation.ShellProof.strictToWeak T a (HistoryLookup.consCall ctag a b)
  exact ⟨.mp hw h⟩
 have consRight (a b : Term ctx) : Derivation T (weakBound b (HistoryLookup.consCall ctag a b)) := by
  apply Classical.choice
  obtain ⟨h⟩ := HistoryBounds.ConsProof.consSecondStrictBound n p ctag hc ctx a b
  obtain ⟨hw⟩ := HistoryCancellation.ShellProof.strictToWeak T b (HistoryLookup.consCall ctag a b)
  exact ⟨.mp hw h⟩
 have pairLeft (a b : Term ctx) : Derivation T (weakBound a (HistoryKernel.pairCall ptag a b)) := by
  apply Classical.choice
  exact HistoryBounds.PairProof.pairFirstBound n p ptag hp ctx a b
 have pairRight (a b : Term ctx) : Derivation T (weakBound b (HistoryKernel.pairCall ptag a b)) := by
  apply Classical.choice
  exact HistoryBounds.PairProof.pairSecondBound n p ptag hp ctx a b
 let vt := binaryValue ctag atag 3 v t
 let var := HistoryLookup.consCall ctag (.zero : Term ctx) (HistoryLookup.consCall ctag .zero .zero)
 let vx := binaryValue ctag atag 3 v var
 let phi := templateValue ctag atag t v
 let ann := HistoryLookup.consCall ctag phi (HistoryLookup.consCall ctag t (HistoryLookup.consCall ctag u .zero))
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let ar := HistoryKernel.pairCall ptag ann refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 12) ar
 let rule := HistoryKernel.pairCall ptag (.zero : Term ctx) payload
 let conclusion := HistoryKernel.pairCall ptag (formulaValue ctag atag t u v) rule
 have hvt : Derivation T (weakBound v vt) := trans _ _ _ (app v t) (consRight (Term.numeral 3) _)
 have hphi : Derivation T (weakBound v phi) := trans _ _ _ (trans _ _ _ hvt (app vt vx)) (consRight .zero _)
 have hann : Derivation T (weakBound v ann) := trans _ _ _ hphi (consLeft phi _)
 have har := trans _ _ _ hann (pairLeft ann refs)
 have hpay := trans _ _ _ har (pairRight (Term.numeral 12) ar)
 have hrule := trans _ _ _ hpay (pairRight .zero payload)
 have hconcl := trans _ _ _ hrule (pairRight (formulaValue ctag atag t u v) rule)
 exact ⟨trans _ _ _ hconcl (pairRight .zero conclusion)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.BoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.BoundProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.BoundProof.internalCandidateBound
