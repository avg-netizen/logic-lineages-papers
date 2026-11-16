module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.BindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.MemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atRank (n : Nat) (key param deps child parentRank childRank value : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) deps child)))
    (hr : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value child param))) :
    Nonempty (Derivation body Delta (BooleanValue value)) :=
  atRankApply n childRank child param value
    (belowRankAt n parentRank childRank ih (RankDescentProof.descent key param deps child parentRank childRank hp hd hm hr))
    (andIntro hr hv)

theorem memberValue (n : Nat) (key param deps child parentRank value : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) deps child)))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value child param))) :
    Nonempty (Derivation body Delta (BooleanValue value)) := by
  apply programCases rank (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta childRank hj hr
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hr
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hpj hdj hmj hvj
  exact atRank n (key.relabel j) (param.relabel j) (deps.relabel j) (child.relabel j)
    (parentRank.relabel j) childRank (value.relabel j) ihj hpj hdj hmj hr hvj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.MemberProof
