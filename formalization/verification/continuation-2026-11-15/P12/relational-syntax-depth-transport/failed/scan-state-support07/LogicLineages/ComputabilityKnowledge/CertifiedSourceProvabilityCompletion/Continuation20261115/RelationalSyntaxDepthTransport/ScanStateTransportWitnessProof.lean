module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportWitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralSyntaxScan.StateRecursionProof LiteralSyntaxScan.Fusion
open ScanStateTransportSupportProof ScanStateTransportTargets

def transferClaim {ctx : Nat} (itag len ptag q l r : Nat)
 (raw tasks tail next result : Term ctx) : Formula ctx :=
 .imp (.equal (scanState itag len ptag r raw (.succ tasks)) (scanState itag len ptag r tail (.succ next)))
  (witnesses itag len ptag q l r raw tasks result)
theorem substTransfer {m n : Nat} (s : Fin m → Term n) itag len ptag q l r
 (raw tasks tail next result : Term m) :
 substituteFormula s (transferClaim itag len ptag q l r raw tasks tail next result) =
 transferClaim itag len ptag q l r (substitute s raw) (substitute s tasks)
  (substitute s tail) (substitute s next) (substitute s result) := by
 simp only [transferClaim,substituteFormula,substScanState,substWitnesses,substitute]
/-- Move an existential final result across an ACTUAL scan-state equality.
The witness itself stays unchanged; its relation is preserved verbatim. -/
theorem transfer {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r
 (raw tasks tail next result : Term ctx) :
 Nonempty (Derivation T (.imp (witnesses itag len ptag q l r tail next result)
  (transferClaim itag len ptag q l r raw tasks tail next result))) := by
 let H := witnessBody itag len ptag q l r (liftTerm tail) (liftTerm next) (liftTerm result) (.var (0 : Fin (ctx+1)))
 let E := Formula.equal (scanState itag len ptag r (liftTerm raw) (.succ (liftTerm tasks)))
  (scanState itag len ptag r (liftTerm tail) (.succ (liftTerm next)))
 let G := [E,H]
 have hh : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
 have he : Hilbert.Local T (ctx+1) G E := .hypothesis (by simp [G])
 have hs := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hr := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 have hsucc := localTrans _ _ _ he hs
 have hw := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hsucc) hr
 have hout := Hilbert.Local.mp (.base (witnessIntro itag len ptag q l r
  (liftTerm raw) (liftTerm tasks) (liftTerm result) (.var (0 : Fin (ctx+1))))) hw
 have hb : Derivation T (.imp H (GorbowPACore.weaken (transferClaim itag len ptag q l r raw tasks tail next result))) := by
  rw [GorbowPACore.weaken,substTransfer]
  simpa only [G,E,transferClaim,liftTerm,renameTerm] using hout.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (transferClaim itag len ptag q l r raw tasks tail next result) ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportWitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportWitnessProof
