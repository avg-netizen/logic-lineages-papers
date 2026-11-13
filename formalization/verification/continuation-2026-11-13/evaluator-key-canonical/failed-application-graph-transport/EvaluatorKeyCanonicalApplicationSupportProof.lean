module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open OriginalLambdaTraversalInternal
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem admitted (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (left right leftOut rightOut parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter))) :
    Nonempty (Derivation body Delta
      (AdmittedPair (baseRepresentative p H G W) H G (member p H G W) W left right parameter)) := by
  have hl := EvaluatorKeyDomainClosureSupportProof.factors p H G W left parameter (andLeft hp)
  have hr := EvaluatorKeyDomainClosureSupportProof.factors p H G W right parameter (andLeft (andRight hp))
  exact andIntro (andRight hl) (andIntro (andRight hr) (andLeft (andRight (andRight hp))))

theorem children (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (left right leftOut rightOut parameter ld lc lf la rd rc rf ra : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
    (hl : Nonempty (Derivation body Delta (ApplicationFields left ld lc lf la)))
    (hr : Nonempty (Derivation body Delta (ApplicationFields right rd rc rf ra))) :
    Nonempty (Derivation body Delta
      ((Domain p H G W lf parameter ⊓ (Domain p H G W rf parameter ⊓ Same p H G W lf rf parameter)) ⊓
       (Domain p H G W la parameter ⊓ (Domain p H G W ra parameter ⊓ Same p H G W la ra parameter)))) := by
  have had := admitted p H G W P left right leftOut rightOut parameter hp
  have dl := EvaluatorKeyApplicationDomainProof.actualApplicationDomain p H G W body alpha Delta
    left parameter ld lc lf la (andLeft hp) hl
  have dr := EvaluatorKeyApplicationDomainProof.actualApplicationDomain p H G W body alpha Delta
    right parameter rd rc rf ra (andLeft (andRight hp)) hr
  have sl := EvaluatorChildrenSourceProof.sourceApplication H G (member p H G W) W body alpha Delta
    left parameter ld lc lf la (andLeft had) hl
  have sr := EvaluatorChildrenSourceProof.sourceApplication H G (member p H G W) W body alpha Delta
    right parameter rd rc rf ra (andLeft (andRight had)) hr
  have ql := EvaluatorChildrenSelectorProof.selectorApplication body alpha Delta left parameter ld lc lf la hl
  have qr := EvaluatorChildrenSelectorProof.selectorApplication body alpha Delta right parameter rd rc rf ra hr
  have hc := EvaluatorChildrenAssemblyProof.application (baseRepresentative p H G W) H G (member p H G W) W
    left right parameter lf la rf ra had (andLeft sl) (andRight sl) (andLeft sr) (andRight sr)
    (andLeft ql) (andLeft (andRight ql)) (andRight (andRight ql))
    (andLeft qr) (andLeft (andRight qr)) (andRight (andRight qr))
  exact andIntro
    (andIntro (andLeft dl) (andIntro (andLeft dr) (andRight (andRight (andLeft hc)))))
    (andIntro (andRight dl) (andIntro (andRight dr) (andRight (andRight (andRight hc)))))

theorem rebuilt (ld lc lf la rd rc rf ra out otherOut : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (equal ld rd)))
    (hc : Nonempty (Derivation body Delta (equal lc rc)))
    (hf : Nonempty (Derivation body Delta (equal lf rf)))
    (ha : Nonempty (Derivation body Delta (equal la ra)))
    (hl : Nonempty (Derivation body Delta (graph4 application out ld lc lf la)))
    (hr : Nonempty (Derivation body Delta (graph4 application otherOut rd rc rf ra))) :
    Nonempty (Derivation body Delta (equal out otherOut)) := by
  have hh : Nonempty (Derivation body Delta (graph4 application out rd rc rf ra)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 4 Delta _ out
      (Fin.cons ld (Fin.cons lc (Fin.cons lf (Fin.cons la Fin.elim0))))
      (Fin.cons rd (Fin.cons rc (Fin.cons rf (Fin.cons ra Fin.elim0)))) _ hl
    intro i
    exact Fin.cases hd (Fin.cases hc (Fin.cases hf (Fin.cases ha (fun k => Fin.elim0 k)))) i
  simpa only [equalEqn] using valueUnique application out otherOut
    (Fin.cons rd (Fin.cons rc (Fin.cons rf (Fin.cons ra Fin.elim0)))) hh hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationSupportProof
