module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentGuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentOutputProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LiteralRawMP.DispatcherSupportProof
/-- Actual replacement singleton for any original fixed matrix with arbitrary
closed runtime coordinates. Both instance outputs and compiled predecessor are paid. -/
theorem certificate {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (left right index fuel : Term ctx)
 (hl : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag left))
 (hr : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag right)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel
   (impValue I.ctag I.atag (equalValue I.ctag I.atag left right)
    (impValue I.ctag I.atag
     (FixedFormulaSubstitution.formulaValue I.ctag I.atag (left ::ᵥ raw) f (UniformRuntimeEnvironmentAgreement.specialize e))
     (FixedFormulaSubstitution.formulaValue I.ctag I.atag (right ::ᵥ raw) f (UniformRuntimeEnvironmentAgreement.specialize e))))
   (UniformClosedRule12Certificate.certificate I.ctag I.constructorTag
    (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e) left right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let B := FixedFormulaSubstitution.formulaValue I.ctag I.atag (left ::ᵥ raw) f (UniformRuntimeEnvironmentAgreement.specialize e)
 let C := FixedFormulaSubstitution.formulaValue I.ctag I.atag (right ::ᵥ raw) f (UniformRuntimeEnvironmentAgreement.specialize e)
 obtain ⟨hv⟩ := EnvironmentGuardProof.validFormula p old arithmetic x I e f G raw hinputs
 have hguards : Hilbert.Local T ctx G (UniformClosedRule12.guards I.fval I.vtag A left right) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.mp (.base (.logical (.andIntro _ _))) hv) hl)) hr
 obtain ⟨hgraph⟩ := UniformClosedRule12Validity.StatementChecks.exactConclusionGraph arity p
  I.toDispatcherInstallation.toInstallation.toGraphInstallation ctx A left right
 have hC := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hgraph) hguards
 obtain ⟨hleft⟩ := EnvironmentOutputProof.substituted p old arithmetic x I e f G raw hinputs left
 obtain ⟨hright⟩ := EnvironmentOutputProof.substituted p old arithmetic x I e f G raw hinputs right
 obtain ⟨hinner⟩ := LogicProof.binary I.ctag I.atag 7 _ _ B C hleft hright
 obtain ⟨houter⟩ := LogicProof.binary I.ctag I.atag 7 (equalValue I.ctag I.atag left right) _
  (equalValue I.ctag I.atag left right) (impValue I.ctag I.atag B C)
  (Hilbert.Local.base (T := T) (Gamma := G) (.logical (.reflexive _))) hinner
 have heq := localTrans _ _ _ hC houter
 obtain ⟨hseed⟩ := UniformClosedRule12Certificate.CoreProof.internalCore p old arithmetic x I A left right index fuel
 have hs := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hseed) hguards
 exact LogicProof.coreFormula I.coreTag index fuel _ _ _ heq hs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
