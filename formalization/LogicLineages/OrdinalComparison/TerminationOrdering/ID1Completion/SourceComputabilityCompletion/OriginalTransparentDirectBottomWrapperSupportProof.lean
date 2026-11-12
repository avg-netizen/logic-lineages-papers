module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTransparentDirectBottom OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both implication guards are paid by actual same-type bottom; only the
spine supplier is kept as a proof-side input to this assembly lemma. -/
theorem wrapperIntroduction (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
    (s t cert parameter typ : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hspine : Nonempty (Derivation body Delta
      (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) (suc z) s t cert parameter)))
    (hold : Nonempty (Derivation body Delta (graph4 oldStep (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (wrapper endpoint window oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htype := unaryValue InternalUnpair.left (.projection 0) typ s xs ht (projectionValue 0 xs)
  have hbottom := unaryValue BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htype
  have hsame := sameAccept (.projection 1) OriginalConstructorLeaf.expectedBottom t xs (projectionValue 1 xs) hbottom
  have hone := InternalLessThanSupportProof.oneConstantValue (body := body) (Gamma := Delta) xs
  have hneutral := OriginalTransparentVariableStepGuardProof.equalBranches
    (OriginalNeutralLeaf.trigger endpoint window) (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom) (suc z) xs hone hsame
  have hvariable := OriginalTransparentVariableStepGuardProof.equalBranches
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalConstructorLeaf.variableAt)
    (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom) (suc z) xs hone hsame
  have hnonbottom := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs hn
  have hs := conjunctionAccept oldStep
    (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hold hspine
  have hne := conjunctionAccept (OriginalSpineGuardLeaf.refined oldStep)
    (OriginalNeutralLeaf.leafGuard endpoint window) xs hs hneutral
  exact conjunctionAccept (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
    (InternalAcceptance.conjunction
      (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
      OriginalConstructorLeaf.variableGuard) xs hne (conjunctionAccept _ _ xs hnonbottom hvariable)

/-- Assembly only. The public concrete-source endpoint must DERIVE hspine
from the actual decoder and nonbottom; it does not expose this helper input. -/
theorem closedFromSpine (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (s t cert parameter typ : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Premises source s t cert parameter typ)))
    (hspine : Nonempty (Derivation body Delta
      (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window (refined source oldStep)) (suc z) s t cert parameter)) := by
  have hs := andLeft h
  have hn := andLeft (andRight h)
  have ht := andLeft (andRight (andRight h))
  have hb := andLeft (andRight (andRight (andRight h)))
  have hc := andRight (andRight (andRight (andRight h)))
  let leaf := refined source oldStep
  let inner := wrapper endpoint window leaf
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hleaf := OriginalTransparentDirectBottomInternalProof.introduction source oldStep s t cert typ parameter hs hn ht hb hc
  have hinner := wrapperIntroduction endpoint window leaf s t cert parameter typ hn ht hb hspine hleaf
  have hguard := OriginalTransparentVariableStepHereditaryProof.nilGuard inner s t cert parameter typ ht hb hc
  have hclosed := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hinner hguard
  exact wrapperIntroduction endpoint window (OriginalHereditaryLambda.refined inner)
    s t cert parameter typ hn ht hb hspine hclosed
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
