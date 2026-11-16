module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.AnswerCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.HeadRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalQuotientComparisonProof (orLeft)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem headNil (out : OTerm alpha)
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out z))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  obtain ⟨he⟩ := valueUnique InternalListCodec.headCode out z (Fin.cons z Fin.elim0) hh
    SixSol20261113.Context.ReverseForwardRowsProof.headZero
  exact ⟨orLeft he⟩

theorem nilMapHead (n : Nat) (param values out : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values z param)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out values))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  have he := valueUnique (Equation.answerMap n) values z ![z,param] hm (AnswersProof.nilMap n param)
  exact headNil out (headTransport InternalListCodec.headCode out values z Fin.elim0 he hh)

theorem consHeadIn (n : Nat) (key param deps parentRank list child tail values out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hmem : Nonempty (Derivation body Delta (graph2 contains (suc z) deps child)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list child tail)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values list param)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out values))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply AnswerCasesProof.consCases n list child tail param values _ hc hm
  intro beta j Theta rest hj hr hs
  rw [booleanRename]
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hmem j Theta hj
  have hhj := renameInto hh j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hpj hdj hmj
  rw [graph1Rename] at hhj
  apply programCases (extract n) (Fin.cons (child.relabel j) (Fin.cons (param.relabel j) Fin.elim0)) _
  intro gamma k Xi value hk hv
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hv
  have ihk := renameInto ihj k Xi hk
  rw [belowRankRename] at ihk
  have hpk := renameInto hpj k Xi hk
  have hdk := renameInto hdj k Xi hk
  have hmk := renameInto hmj k Xi hk
  have hhk := renameInto hhj k Xi hk
  have hsk := renameInto hs k Xi hk
  simp only [graph2Rename,sucRelabel,zRelabel] at hpk hdk hmk
  rw [graph1Rename] at hhk
  rw [graph3Rename] at hsk
  have hcons := AnswerCasesProof.stepCons n ((child.relabel j).relabel k) (rest.relabel k)
    ((param.relabel j).relabel k) ((values.relabel j).relabel k) value hsk hv
  have hhead := InternalRawListRecursionSupportProof.consHead ((values.relabel j).relabel k) value (rest.relabel k) hcons
  have he := valueUnique InternalListCodec.headCode ((out.relabel j).relabel k) value
    (Fin.cons ((values.relabel j).relabel k) Fin.elim0) hhk hhead
  have hb := MemberProof.memberValue n ((key.relabel j).relabel k) ((param.relabel j).relabel k)
    ((deps.relabel j).relabel k) ((child.relabel j).relabel k) ((parentRank.relabel j).relabel k) value ihk hpk hdk hmk hv
  exact Continuation20261115.OriginalDecodedBooleanRange.PayloadProof.transport _ value he hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.HeadRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.HeadRangeProof
