module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open Continuation20261116.OriginalConcreteHeadSignature
open Continuation20261115.OriginalHeadDecoderValidity.SupportProof
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open BuiltinSupportProof
theorem basicEquation : Targets.BasicEquation := by
  intro n arity body alpha Delta tag raw packed out hp hk
  have hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)) := by
    apply Continuation20261115.OriginalHeadDecoderValidity.BackwardProof.basicAccept n raw (numeral tag.val) z hp
    apply InternalApplicationStepPeelSupportProof.andIntro
    · fin_cases tag
      · exact ⟨InternalQuotientComparisonProof.orLeft (refl z)⟩
      · exact ⟨InternalQuotientComparisonProof.orRight (refl (suc z))⟩
    · exact ⟨refl z⟩
  fin_cases tag
  · exact finish n arity 0 raw z z packed out hp (constantValue 0 ![z]) hg hk
  · have hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.branchResult 1) (suc z) z)) :=
      arrowValue (constant 1 0) (constant 1 0) z z z z (constantValue 0 ![z]) (constantValue 0 ![z])
        InternalApplicationValidityStackAppendTransitionProof.pairZero
    exact finish n arity 1 raw z (suc z) packed out hp hv hg hk

theorem caseEquation : Targets.CaseEquation := by
  intro n arity body alpha Delta raw tau aa ab ac packed out hp haa hab hac hk
  have ht : Nonempty (Derivation body Delta (graph1 (.projection 0) tau tau)) := projectionValue 0 ![tau]
  have hz : Nonempty (Derivation body Delta (graph1 (constant 1 0) z tau)) := constantValue 0 ![tau]
  have h1 := arrowValue (.projection 0) (.projection 0) tau tau tau aa ht ht haa
  have h2 := arrowValue (.projection 0) (OriginalHeadResult.arrow (.projection 0) (.projection 0)) tau tau (suc aa) ab ht h1 hab
  have h3 := arrowValue (constant 1 0) (OriginalHeadResult.arrow (.projection 0) (OriginalHeadResult.arrow (.projection 0) (.projection 0))) tau z (suc ab) ac hz h2 hac
  have hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)) :=
    (tagFactor n 2 raw (numeral 2) tau (numeral 1) hp ⟨refl (numeral 2)⟩).mpr (constantValue 1 ![raw])
  exact finish n arity 2 raw tau (suc ac) packed out hp h3 hg hk

theorem recursorEquation : Targets.RecursorEquation := by
  intro n arity body alpha Delta raw tau aa ab ac ad packed out hp haa hab hac had hk
  have ht : Nonempty (Derivation body Delta (graph1 (.projection 0) tau tau)) := projectionValue 0 ![tau]
  have hz : Nonempty (Derivation body Delta (graph1 (constant 1 0) z tau)) := constantValue 0 ![tau]
  let A := OriginalHeadResult.arrow (.projection 0) (.projection 0)
  let B := OriginalHeadResult.arrow (constant 1 0) A
  have h1 := arrowValue (.projection 0) (.projection 0) tau tau tau aa ht ht haa
  have h2 := arrowValue (constant 1 0) A tau z (suc aa) ab hz h1 hab
  have h3 := arrowValue B A tau (suc ab) (suc aa) ac h2 h1 hac
  have h4 := arrowValue (constant 1 0) (OriginalHeadResult.arrow B A) tau z (suc ac) ad hz h3 had
  have hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)) :=
    (tagFactor n 3 raw (numeral 3) tau (numeral 1) hp ⟨refl (numeral 3)⟩).mpr (constantValue 1 ![raw])
  exact finish n arity 3 raw tau (suc ad) packed out hp h4 hg hk

theorem builtinSignatures : Targets.InternalBuiltinSignatures := ⟨basicEquation,caseEquation,recursorEquation⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinProof
