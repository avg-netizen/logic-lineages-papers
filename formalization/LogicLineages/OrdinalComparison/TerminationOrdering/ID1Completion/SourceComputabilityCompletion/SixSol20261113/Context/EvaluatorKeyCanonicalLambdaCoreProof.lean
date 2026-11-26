module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalInternal
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter domain codomain child otherChild childParameter childPayload childOut otherOut : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (hl : Nonempty (Derivation body Delta (LambdaFields left domain codomain child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (LambdaFields right domain codomain otherChild parameter childParameter)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
 (hcl : Nonempty (Derivation body Delta (graph2 (C p H G W P) childOut child childParameter)))
 (hcr : Nonempty (Derivation body Delta (graph2 (C p H G W P) otherOut otherChild childParameter))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 have dl := andLeft hp
 have dr := andLeft (andRight hp)
 have same := andLeft (andRight (andRight hp))
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W left right parameter dl dr same
 have dcl := EvaluatorKeyDomainClosureProof.actualLambdaDomain p H G W body alpha Delta left parameter domain codomain child childParameter dl hl
 have dcr := EvaluatorKeyDomainClosureProof.actualLambdaDomain p H G W body alpha Delta right parameter domain codomain otherChild childParameter dr hr
 have cad := EvaluatorChildrenProof.actualLambda (baseRepresentative p H G W) H G (member p H G W) W body alpha Delta
   left right domain codomain child otherChild parameter childParameter had hl hr
 have hc := EvaluatorKeyCanonicalBindingProof.belowPayloadApply p H G W P q childPayload child otherChild childOut otherOut childParameter
   hb hlt hraw (andIntro dcl (andIntro dcr (andIntro (andRight (andRight cad)) (andIntro hcl hcr))))
 let leaf := OriginalLambdaTraversalSelection.leaf (refined p H G W P).base (refined p H G W P).window
 obtain ⟨lawl⟩ := OriginalLambdaTraversalInternalLambdaProof.actualOriginalLambdaTraversalInternalLambda
   body leaf alpha Delta left domain codomain child childOut leftOut parameter childParameter
 obtain ⟨lawr⟩ := OriginalLambdaTraversalInternalLambdaProof.actualOriginalLambdaTraversalInternalLambda
   body leaf alpha Delta right domain codomain otherChild otherOut rightOut parameter childParameter
 obtain ⟨argl⟩ := andIntro hl hcl
 obtain ⟨argr⟩ := andIntro hr hcr
 obtain ⟨vl⟩ := andLeft (andRight (andRight (andRight hp)))
 obtain ⟨vr⟩ := andRight (andRight (andRight (andRight hp)))
 have gl : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor leftOut domain codomain childOut)) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination lawl argl)) vl⟩
 have gr : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor rightOut domain codomain otherOut)) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination lawr argr)) vr⟩
 exact EvaluatorKeyCanonicalLambdaSupportProof.rebuilt domain codomain childOut otherOut leftOut rightOut hc gl gr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaCoreProof
