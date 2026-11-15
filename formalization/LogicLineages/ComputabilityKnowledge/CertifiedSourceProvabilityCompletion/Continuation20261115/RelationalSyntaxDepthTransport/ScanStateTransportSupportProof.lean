module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SubstitutionProof ScanStateTransportTargets
open LiteralSyntaxScan.Fusion

theorem substBody {m n : Nat} (s : Fin m → Term n) itag len ptag q l r
 (raw nt oldResult newResult : Term m) :
 substituteFormula s (witnessBody itag len ptag q l r raw nt oldResult newResult) =
 witnessBody itag len ptag q l r (substitute s raw) (substitute s nt)
  (substitute s oldResult) (substitute s newResult) := by
 simp only [witnessBody,substituteFormula,substScanState,substStack,substitute]
theorem bodyAt {ctx : Nat} itag len ptag q l r (raw nt oldResult newResult : Term ctx) :
 GorbowStandardInstances.instantiate (witnessBody itag len ptag q l r
  (liftTerm raw) (liftTerm nt) (liftTerm oldResult) (.var 0)) newResult =
 witnessBody itag len ptag q l r raw nt oldResult newResult := by
 simp only [GorbowStandardInstances.instantiate,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r
 (raw nt oldResult newResult : Term ctx) :
 Derivation T (.imp (witnessBody itag len ptag q l r raw nt oldResult newResult)
  (witnesses itag len ptag q l r raw nt oldResult)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T)
  (witnessBody itag len ptag q l r (liftTerm raw) (liftTerm nt) (liftTerm oldResult) (.var 0)) newResult
 rw [bodyAt] at h
 exact h
theorem substWitnesses {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (raw nt result : Term m) :
 substituteFormula s (witnesses itag len ptag q l r raw nt result) =
 witnesses itag len ptag q l r (substitute s raw) (substitute s nt) (substitute s result) := by
 simp only [witnesses,substituteFormula,substBody,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
def property {ctx : Nat} (itag len ptag q l r : Nat) (raw ot nt result : Term ctx) : Formula ctx :=
 .imp (stackRelation len q l r ot nt)
  (.imp (.equal (LiteralSyntaxScan.StateRecursionProof.scanState itag len ptag r raw (.succ ot)) (.succ result))
   (witnesses itag len ptag q l r raw nt result))
theorem substProperty {m n : Nat} (s : Fin m → Term n) itag len ptag q l r (raw ot nt result : Term m) :
 substituteFormula s (property itag len ptag q l r raw ot nt result) =
 property itag len ptag q l r (substitute s raw) (substitute s ot) (substitute s nt) (substitute s result) := by
 simp only [property,substituteFormula,substStack,substScanState,substWitnesses,substitute]
theorem weakenProperty {ctx : Nat} itag len ptag q l r (raw ot nt result : Term ctx) :
 GorbowPACore.weaken (property itag len ptag q l r raw ot nt result) =
 property itag len ptag q l r (liftTerm raw) (liftTerm ot) (liftTerm nt) (liftTerm result) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
/-- Empty original raw input returns the initial task-state exactly. -/
theorem nil {n ctx : Nat} (p : Program n) (itag len ptag q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ot nt result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property itag len ptag q l r .zero ot nt result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let R := stackRelation len q l r ot nt
 let S := Formula.equal (LiteralSyntaxScan.StateRecursionProof.scanState itag len ptag r .zero (.succ ot)) (.succ result)
 let G := [S,R]
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 obtain ⟨ho⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ ot)
 obtain ⟨hn⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ nt)
 have heq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hs) (.base ho)
 have he := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) heq
 have houtrel := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r ot result nt))
  (HistoryOrder.StepProof.localSym _ _ he)) hrel
 have hw := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base hn)) houtrel
 have hout := Hilbert.Local.mp (.base (witnessIntro itag len ptag q l r .zero nt result nt)) hw
 exact ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportSupportProof
