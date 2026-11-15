module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.GuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.OutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.ConclusionProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The actual case13/predecessor conclusion equals the original dynamic
universal-instantiation formula, under the original recognizer guards. -/
theorem canonical {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (replacement : Term ctx)
 (hreplacement : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag replacement)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag
    (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e) replacement)
   (conclusion I.ctag I.atag e f raw replacement))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let B := FixedFormulaSubstitution.formulaValue I.ctag I.atag (replacement ::ᵥ raw) f
  (UniformRuntimeEnvironmentAgreement.specialize e)
 obtain ⟨hvalid⟩ := GuardProof.validFormula p old arithmetic x I e f G raw hinputs
 have hg : Hilbert.Local T ctx G (UniformClosedInstanceRecognizer.guards I.fval I.vtag A replacement) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hvalid) hreplacement
 obtain ⟨hgraph⟩ := UniformClosedRule13Validity.GraphProof.exactConclusionGraph arity p
  I.toDispatcherInstallation.toInstallation.toGraphInstallation ctx A replacement
 have hc := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hgraph) hg
 obtain ⟨houtput⟩ := OutputProof.substituted p old arithmetic x I e f G raw hinputs replacement
 let antecedent := HistoryLookup.consCall I.ctag (Term.numeral (n := ctx) 10) A
 let projected := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag A replacement
 have happ : Hilbert.Local T ctx G
  (.equal (HistoryAppend.appendCall I.atag antecedent projected)
   (HistoryAppend.appendCall I.atag antecedent B)) := by
  apply callCongruence (T := T) (G := G) I.atag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive antecedent))
  | succ i => cases i using Fin.cases with
    | zero => exact houtput
    | succ i => exact Fin.elim0 i
 have hshape : Hilbert.Local T ctx G
  (.equal (HistoryLookup.consCall I.ctag (Term.numeral 7) (HistoryAppend.appendCall I.atag antecedent projected))
   (HistoryLookup.consCall I.ctag (Term.numeral 7) (HistoryAppend.appendCall I.atag antecedent B))) := by
  apply callCongruence (T := T) (G := G) I.ctag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive _))
  | succ i => cases i using Fin.cases with
    | zero => exact happ
    | succ i => exact Fin.elim0 i
 exact ⟨localTrans _ _ _ hc hshape⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.ConclusionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.ConclusionProof
