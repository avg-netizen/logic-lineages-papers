module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.WitnessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.FinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TransportProof
open GorbowSyntax GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralRawMP.DispatcherSupportProof
noncomputable def cons {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} ctag (a b tail : Term ctx)
 (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (HistoryLookup.consCall ctag a tail) (HistoryLookup.consCall ctag b tail)) := by
 apply callCongruence (T := T) (G := G) ctag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive tail))
   | succ i => exact Fin.elim0 i
noncomputable def step {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag
 (a b tok tok' : Term ctx) (h : Hilbert.Local T ctx G (.equal a b))
 (ht : Hilbert.Local T ctx G (.equal tok tok')) :
 Hilbert.Local T ctx G (.equal (LiteralSyntaxStep.stepCall tag (.succ a) tok)
  (LiteralSyntaxStep.stepCall tag (.succ b) tok')) := by
 have hs : Hilbert.Local T ctx G (.equal (.succ a) (.succ b)) := localUnary (.succ (.var 0)) _ _ h
 apply callCongruence (T := T) (G := G) tag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact hs
 | succ i => cases i using Fin.cases with
   | zero => exact ht
   | succ i => exact Fin.elim0 i
noncomputable def emit {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag
 (a b tok tok' raw : Term ctx) (h : Hilbert.Local T ctx G (.equal a b))
 (ht : Hilbert.Local T ctx G (.equal tok tok')) :
 Hilbert.Local T ctx G (.equal (UniformClosedSubstitutionEmit.emitCall tag (.succ a) tok raw)
  (UniformClosedSubstitutionEmit.emitCall tag (.succ b) tok' raw)) := by
 have hs : Hilbert.Local T ctx G (.equal (.succ a) (.succ b)) := localUnary (.succ (.var 0)) _ _ h
 apply callCongruence (T := T) (G := G) tag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact hs
 | succ i => cases i using Fin.cases with
   | zero => exact ht
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i
/-- Eliminate concrete canonical coordinates only by internal equality. The
actual scanner/output witness stays explicit; no CORE or relation cast. -/
theorem finishCanonical {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} stag len q l r
 (tasks canonicalTasks chunk canonicalChunk oldResult canonicalOldResult newResult : Term ctx)
 (ht : Hilbert.Local T ctx G (.equal tasks canonicalTasks))
 (hc : Hilbert.Local T ctx G (.equal chunk canonicalChunk))
 (ho : Hilbert.Local T ctx G (.equal oldResult canonicalOldResult))
 (hbody : Hilbert.Local T ctx G (resultBody stag len q l r canonicalTasks canonicalChunk canonicalOldResult newResult)) :
 Nonempty (Hilbert.Local T ctx G (results stag len q l r tasks chunk oldResult)) := by
 have hscan := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hbody
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hbody
 have hin := callCongruence (T := T) (G := G) stag
  (tasks ::ᵥ chunk ::ᵥ nil) (canonicalTasks ::ᵥ canonicalChunk ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact ht
   | succ i => cases i using Fin.cases with
     | zero => exact hc
     | succ i => exact Fin.elim0 i)
 have hout := localTrans _ _ _ hin hscan
 have hr := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r canonicalOldResult oldResult newResult))
  (HistoryOrder.StepProof.localSym _ _ ho)) hrel
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hout) hr
 exact ⟨.mp (.base (WitnessProof.introResult stag len q l r tasks chunk oldResult newResult)) hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TransportProof
