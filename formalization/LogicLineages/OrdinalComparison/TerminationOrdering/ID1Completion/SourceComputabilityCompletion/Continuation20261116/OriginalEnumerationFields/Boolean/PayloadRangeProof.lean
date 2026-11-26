module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SelectorRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PayloadRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalTagArithmeticSupportProof (cancelSuc)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def secondQuery : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => InternalListCodec.tailCode)
def queries : Fin 3 → Program 1 := ![InternalListCodec.headCode,InternalListCodec.tailCode,secondQuery]

theorem atPayload (n : Nat) (key param deps parentRank values out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (hpay : Nonempty (Derivation body Delta (graph3 (LayerInternalProof.payload n) out key values param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply queryCases queries (Fin.cons values Fin.elim0) _
  intro beta j ys Theta hj hg
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hg
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have hpayj := renameInto hpay j Theta hj
  rw [graph2Rename] at hpj hdj hmj
  rw [graph3Rename] at hpayj
  have hs := unaryRecover InternalListCodec.headCode InternalListCodec.tailCode (ys 2) (ys 1)
    (Fin.cons (values.relabel j) Fin.elim0) (hg 2) (hg 1)
  have hr := SelectorRangeProof.atValues n (key.relabel j) (param.relabel j) (deps.relabel j) (parentRank.relabel j)
    (values.relabel j) (ys 0) (ys 1) (ys 2) ihj hpj hdj hmj (hg 0) (hg 1) hs
  exact PointBindingProof.applyAt (LayerInternalProof.payload n)
    ![key.relabel j,values.relabel j,param.relabel j] (out.relabel j) hr hpayj

theorem atLayer (n : Nat) (key param deps parentRank values out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (hl : Nonempty (Derivation body Delta (graph3 (layer n) (suc out) key values param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases (LayerInternalProof.payload n) (Fin.cons key (Fin.cons values (Fin.cons param Fin.elim0))) _
  intro beta j Theta value hj hv
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hv
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have hlj := renameInto hl j Theta hj
  rw [graph2Rename] at hpj hdj hmj
  simp only [graph3Rename,sucRelabel] at hlj
  have hb := atPayload n (key.relabel j) (param.relabel j) (deps.relabel j) (parentRank.relabel j) (values.relabel j) value ihj hpj hdj hmj hv
  have hs := LayerInternalProof.atPayload n (key.relabel j) (values.relabel j) (param.relabel j) value hv
  obtain ⟨he⟩ := valueUnique (layer n) (suc (out.relabel j)) (suc value)
    ![key.relabel j,values.relabel j,param.relabel j] hlj hs
  exact Continuation20261115.OriginalDecodedBooleanRange.PayloadProof.transport (out.relabel j) value ⟨cancelSuc he⟩ hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PayloadRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PayloadRangeProof
