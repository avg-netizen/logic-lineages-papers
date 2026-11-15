module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.EnvironmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.MachineProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformFixedFormulaAgreement.Traversal RelationalSyntaxDepthTransport.ConstructorStepTargets
open LiteralRawMP.DispatcherSupportProof
/-- Runtime input term, rather than the older finite native token list. -/
def run {n ctx : Nat} {p : Program n} (I : Installation p) (tokens state out raw : Term ctx) : Term ctx :=
 UniformClosedSubstitutionRawFold.foldCall I.ftag tokens (HistoryKernel.pairCall I.ptag state out) raw
noncomputable def stateCongruence {T : Sentence → Prop} {ctx : Nat} (G : List (Formula ctx))
 (ftag : Nat) (tokens a b raw : Term ctx) (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (UniformClosedSubstitutionRawFold.foldCall ftag tokens a raw)
  (UniformClosedSubstitutionRawFold.foldCall ftag tokens b raw)) := by
 apply callCongruence (T := T) (G := G) ftag
 intro i
 cases i using Fin.cases with
 | zero => exact .base (.logical (.reflexive tokens))
 | succ i => cases i using Fin.cases with
   | zero => exact h
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i
/-- Concrete input-fusion application with the real intermediate packed state. -/
theorem compose {n ctx : Nat} (p : Program n) (I : Installation p) (G : List (Formula ctx))
 (xs ys a b c raw : Term ctx)
 (hleft : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall I.ftag xs a raw) b))
 (hright : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall I.ftag ys b raw) c)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall I.ftag (HistoryAppend.appendCall I.atag xs ys) a raw) c)) := by
 obtain ⟨hf⟩ := UniformRawFoldInputFusion.StatementChecks.exactInputFusion n p
  I.ftag I.etag I.stag I.ptag I.ctag I.atag I.ltag I.rtag I.hf I.he I.hs I.hp I.hc I.ha I.hl I.hr ctx xs ys a raw
 have hmid := stateCongruence G I.ftag ys _ b raw hleft
 exact ⟨localTrans _ _ _ (.base hf) (localTrans _ _ _ hmid hright)⟩
/-- Consume an original nonmarker constructor before an arbitrary runtime
suffix, with actual pending-task expansion exposed in the same list order. -/
theorem constructor {n ctx : Nat} (p : Program n) (I : Installation p)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound rest tokens out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (HistoryLookup.consCall I.ctag (Term.numeral (token ctor)) tokens)
    (input I.ptag I.ctag ctor bound rest) out raw)
   (run I tokens (.succ (UniformFixedFormulaAgreement.StackProof.prepend I.ctag (tasks I.ptag bound ctor) rest))
    (HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))) raw))) := by
 obtain ⟨hfirst⟩ := UniformFixedFormulaAgreement.ConstructorProof.consume p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.xtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hx ctor hmarker bound rest tokens out raw
 obtain ⟨hrows⟩ := UniformFixedFormulaAgreement.StackProof.appendPrefix p I.ctag I.atag I.hc I.ha (tasks I.ptag bound ctor) rest
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := []) hrows)
 have hsucc' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (.succ (output I.ptag I.ctag I.atag ctor bound rest))
   (.succ (UniformFixedFormulaAgreement.StackProof.prepend I.ctag (tasks I.ptag bound ctor) rest))) := by
  simpa only [RelationalSyntaxDepthTransport.ConstructorStepTargets.output,GorbowStandardInstances.instantiate,
   GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 let afterOut : Term ctx := HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))
 have hp := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag
  (.succ (output I.ptag I.ctag I.atag ctor bound rest)) afterOut
  (.succ (UniformFixedFormulaAgreement.StackProof.prepend I.ctag (tasks I.ptag bound ctor) rest)) afterOut
  hsucc' (.base (.logical (.reflexive afterOut)))
 have hm := UniformFixedFormulaAgreement.FoldProof.stateCongruence I.ftag tokens _ _ raw hp.finish
 exact ⟨Logic.trans _ _ _ hfirst hm⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.MachineProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.MachineProof
