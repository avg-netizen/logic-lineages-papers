module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainCertificateProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem targetTyped (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (tau : Ty) (f g witness : OTerm α)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (ht : Nonempty (Derivation body Delta
      (typed (Outer.computability oldComp data window oldVertex oldResult) tau (numeral context) f)))
    (hp : Nonempty (Derivation body Delta
      (certificate (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
        false context f g witness))) :
    Nonempty (Derivation body Delta
      (typed (Outer.computability oldComp data window oldVertex oldResult) tau (numeral context) g)) :=
  GuardedSourceCertificateProof.certificateClosure
    (GammaGuardedSource.baseTyped (Outer.typed data window oldComp.typed) Outer.valid)
    (GammaGuardedSource.basePositive
      (Outer.positive (Outer.rawPositive data oldStep bottom measure) window oldSrc.positive) Outer.gamma)
    Outer.tag window (numeral context) (numeral (typeNumber tau)) f g witness
    (GuardedSourceCertificateProof.windowNumeral window context hw) ht hp

/-- Preserve the exact domain along the explicit supplied certificate.
Typedness comes from ORIGINAL certificate closure; the common runtime
Gamma comes from ORIGINAL guard and certificate graph factors. -/
theorem targetDomain (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty) (f g a witness gammaCode : OTerm α)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hd : Nonempty (Derivation body Delta
      (domain (Outer.computability oldComp data window oldVertex oldResult) context sigma tau f a)))
    (hp : Nonempty (Derivation body Delta
      (certificate (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
        false context f g witness))) :
    Nonempty (Derivation body Delta
      (domain (Outer.computability oldComp data window oldVertex oldResult) context sigma tau g a)) := by
  have hg := OuterGammaProof.targetGamma oldSrc oldComp data rawScalar oldStep bottom measure window
    context f g witness gammaCode hf hp
  have ha := OuterGammaProof.argumentGamma oldComp data window oldVertex oldResult f a gammaCode hf (andRight hd)
  have ht := targetTyped oldSrc oldComp data rawScalar oldStep bottom measure window oldVertex oldResult
    context (.arrow sigma tau) f g witness hw (andLeft (andLeft hd)) hp
  exact andIntro (andIntro ht (andRight (andLeft hd)))
    (OuterTypedProof.objectGuard oldComp data window oldVertex oldResult g a gammaCode hg ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainCertificateProof
