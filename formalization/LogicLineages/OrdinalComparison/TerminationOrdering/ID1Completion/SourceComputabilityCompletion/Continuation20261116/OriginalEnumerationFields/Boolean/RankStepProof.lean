module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PayloadRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.RankStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (queryCases andLeft andRight)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof BindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries (n : Nat) : Fin 2 → Program 2 := ![dependency,Equation.answers n]

theorem atExtract (n : Nat) (key param parentRank out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (he : Nonempty (Derivation body Delta (graph2 (extract n) out key param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply queryCases (queries n) (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j ys Theta hj hg
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hg
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hpj hej
  have hd : Nonempty (Derivation body Theta (graph2 dependency (ys 0) (key.relabel j) (param.relabel j))) := hg 0
  have ha : Nonempty (Derivation body Theta (graph2 (Equation.answers n) (ys 1) (key.relabel j) (param.relabel j))) := hg 1
  have hm := binaryRecover (Equation.answerMap n) dependency (.projection 1) (ys 1) (ys 0) (param.relabel j)
    ![key.relabel j,param.relabel j] ha hd (projectionValue 1 ![key.relabel j,param.relabel j])
  have hl := (Equation.Proof.exchangeEquation n body beta Theta (key.relabel j) (param.relabel j) (ys 1) (out.relabel j) ha).mp hej
  exact PayloadRangeProof.atLayer n (key.relabel j) (param.relabel j) (ys 0) (parentRank.relabel j)
    (ys 1) (out.relabel j) ihj hpj hd hm hl

theorem step (n : Nat) (r : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n r))) :
    Nonempty (Derivation body Delta (AtRank n r)) := by
  apply atRankIntro n r
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let key : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let row := graph2 rank (r.relabel Sum.inl) key param ⊓ graph2 (extract n) out key param
  let Theta := row :: Delta.map (fun q => q.relabel Sum.inl)
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 3) Theta hj
  rw [belowRankRename] at ihj
  have hf : Nonempty (Derivation body Theta row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (atExtract n key param (r.relabel Sum.inl) out ihj (andLeft hf) (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.RankStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.RankStepProof
