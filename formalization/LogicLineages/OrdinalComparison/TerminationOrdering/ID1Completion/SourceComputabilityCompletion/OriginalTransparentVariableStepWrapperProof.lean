module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every existing single-layer guard is derived at these exact raw inputs. -/
theorem wrapperIntroduction (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
    (s t cert parameter typ : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hold : Nonempty (Derivation body Delta (graph4 oldStep (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (wrapper endpoint window oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hs := OriginalTransparentVariableStepSpineProof.variableSpine s t cert parameter htag
  have hg := OriginalTransparentVariableStepGuardProof.guards endpoint window s t cert parameter typ htag ht hb
  have hspine := conjunctionAccept oldStep
    (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hold hs
  have hn := conjunctionAccept (OriginalSpineGuardLeaf.refined oldStep)
    (OriginalNeutralLeaf.leafGuard endpoint window) xs hspine (andLeft hg)
  exact conjunctionAccept (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
    (InternalAcceptance.conjunction
      (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
      OriginalConstructorLeaf.variableGuard) xs hn (andRight hg)

/-- Both wrapper layers and the intervening hereditary refinement are
constructed. The exact source/checker tuple and certificate remain unchanged. -/
theorem closedIntroduction (source : Program 2) (oldStep : Program 4)
    (endpoint : Program 6) (window : Program 1) (s t cert parameter typ : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source (suc z) s parameter)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta
      (graph1 OriginalTransparentVariableStep.certificateCode cert s))) :
    Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window (OriginalTransparentVariableStep.refined source oldStep))
        (suc z) s t cert parameter)) := by
  let leaf := OriginalTransparentVariableStep.refined source oldStep
  let inner := wrapper endpoint window leaf
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hv : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) s)) :=
    sameAccept OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1) z
      (Fin.cons s Fin.elim0) htag (constantZeroValue (Fin.cons s Fin.elim0))
  have hleaf := OriginalTransparentVariableStepInternalProof.introduction source oldStep
    s t cert typ parameter hs hv ht hb hc
  have hinner := wrapperIntroduction endpoint window leaf s t cert parameter typ htag ht hb hleaf
  have hguard := OriginalTransparentVariableStepHereditaryProof.nilGuard inner s t cert parameter typ ht hb hc
  have hclosed := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hinner hguard
  exact wrapperIntroduction endpoint window (OriginalHereditaryLambda.refined inner)
    s t cert parameter typ htag ht hb hclosed

theorem actualOriginalTransparentVariableClosedLeaf :
    OriginalTransparentVariableStepWrapperTargets.ActualOriginalTransparentVariableClosedLeaf := by
  intro source oldStep endpoint window body alpha Delta s t cert parameter typ
  let A := graph2 source (suc z) s parameter ⊓
    (graph1 OriginalLambdaConstructor.tag z s ⊓
      (graph1 InternalUnpair.left typ s ⊓
        (graph1 BottomRepresentative.bottomCode t typ ⊓
          graph1 OriginalTransparentVariableStep.certificateCode cert s)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := closedIntroduction source oldStep endpoint window s t cert parameter typ
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperProof
