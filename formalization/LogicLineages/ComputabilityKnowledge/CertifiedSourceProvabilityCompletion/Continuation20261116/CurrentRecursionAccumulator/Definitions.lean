module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality

/-- Join inputs are counter, actual prior accumulator, then fixed parameters. -/
def atCounter (m : Nat) : Fin (m+1) → Program (m+2) :=
 Fin.cases (.projection 0) (fun i => .projection i.succ.succ)
def atSuccessor (m : Nat) : Fin (m+1) → Program (m+2) :=
 Fin.cases (.composition .succ (fun _ => .projection 0)) (fun i => .projection i.succ.succ)
def join {m : Nat} (formula step : Program (m+1)) : Program (m+2) :=
 .composition LiteralRawMP.constructor
  (Fin.cases (HistoryRuleSuffix.constant (m+2) 0)
   (Fin.cases (.composition formula (atSuccessor m))
    (Fin.cases (.composition step (atCounter m)) (Fin.cases (.projection 1) Fin.elim0))))
def producer {m : Nat} (base : Program m) (formula step : Program (m+1)) : Program (m+1) :=
 .recursion base (join formula step)
/-- Actual node memberships only. This conditional installation does NOT assert
that arbitrary supplied producer programs occur in the accepted source root. -/
structure Installation {arity m : Nat} (p : Program arity) (base : Program m) (formula step : Program (m+1)) where
 producerTag : Nat
 baseTag : Nat
 formulaTag : Nat
 stepTag : Nat
 h_producer : (nodes p)[producerTag]? = some ⟨m+1,producer base formula step⟩
 h_base : (nodes p)[baseTag]? = some ⟨m,base⟩
 h_formula : (nodes p)[formulaTag]? = some ⟨m+1,formula⟩
 h_step : (nodes p)[stepTag]? = some ⟨m+1,step⟩
/-- Exact original numeric Nat.rec. Step is an ordinary implication code,
not a function supplied with an arbitrary accepted previous certificate. -/
def number (phi : Nat → Formula 0) (stepCode : Nat → Nat) (baseCode : Nat) : Nat → Nat :=
 Nat.rec baseCode (fun k previous => GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode (phi (k+1))) (stepCode k) previous)
/-- Same literal constructor for arbitrary raw formula/certificate numbers,
retaining original decode/default behavior rather than treating malformed codes
as syntax. Canonical prefix outputs recover number above. -/
def rawNumber (formulaCode stepCode : Nat → Nat) (baseCode : Nat) : Nat → Nat :=
 Nat.rec baseCode (fun k previous => GorbowNumericCertificate.certificateNumber
  (GorbowTheoryCertificateOperations.mpLines 0
   ((GorbowNumericCertificate.decodeFormula (formulaCode (k+1))).getD [])
   ((GorbowNumericCertificate.decodeCertificate (stepCode k)).getD [])
   ((GorbowNumericCertificate.decodeCertificate previous).getD [])))
def familyCall {ctx m : Nat} (tag : Nat) (counter : Term ctx) (params : List.Vector (Term ctx) m) : Term ctx :=
 call tag (counter ::ᵥ params)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator
