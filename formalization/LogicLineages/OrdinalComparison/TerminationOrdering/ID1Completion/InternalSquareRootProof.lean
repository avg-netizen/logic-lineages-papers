module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalSquareRoot InternalSquareRootArithmetic
open InternalSquareRootSyntaxProof InternalSquareRootStepProof
open InternalSquareRootArithmeticSupportProof InternalSquareRootArithmeticProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof InternalRecursionClosureProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaTotalityProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The retained and crossing branches extend an actual recursive graph
witness and its arithmetic interval together. -/
theorem certifiedStep (n : OTerm α) (h : Nonempty (Derivation body Gamma (certified n))) :
    Nonempty (Derivation body Gamma (certified (suc n))) := by
  apply certifiedCases Gamma n _ h
  intro β j Delta old _ ⟨hg⟩ ⟨hi⟩
  rw [certifiedRename,sucRelabel]
  let k := n.relabel j
  let p := ltF (suc k) (square (suc old))
  have yes : Nonempty (Derivation body (p :: Delta) (certified (suc k))) := by
    apply certifiedIntroduction (suc k) old
    · exact rootNext k old old ⟨addHyp hg p⟩
        (stepRetain k old ⟨Derivation.hypothesis List.mem_cons_self⟩)
    · exact intervalRetain old k ⟨addHyp hi p⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have no : Nonempty (Derivation body (p.not :: Delta) (certified (suc k))) := by
    apply certifiedIntroduction (suc k) (suc old)
    · exact rootNext k old (suc old) ⟨addHyp hg p.not⟩
        (stepAdvance k old ⟨Derivation.hypothesis List.mem_cons_self⟩)
    · exact intervalAdvance old k ⟨addHyp hi p.not⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨yes⟩ := yes
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

/-- Original PA induction on the actual input term. Existential witnesses
are object-language terms, never standard values used for reflection. -/
theorem certifiedValue (n : OTerm α) : Nonempty (Derivation body Gamma (certified n)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := certified x
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,x,certifiedInstantiate,varBind]
    exact Classical.choice (certifiedIntroduction z z rootZero ⟨intervalZero⟩)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,x,successorInstance,nextEmbedding,certifiedSubst,varNext]
    exact Classical.choice (certifiedStep x ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have h := Derivation.universalElimination (emb n) (natInduction theta hb hs)
  simpa only [theta,x,certifiedInstantiate,varBind] using (Nonempty.intro h)

/-- Original graph functionality identifies every graph output with the
interval-certified output constructed by induction. -/
theorem intervalOfRootGraph (out n : OTerm α)
    (h : Nonempty (Derivation body Gamma (rootGraph out n))) :
    Nonempty (Derivation body Gamma (interval out n)) := by
  apply certifiedCases Gamma n _ (certifiedValue n)
  intro β j Delta value hj hg ⟨hi⟩
  rw [intervalRename]
  have hp := InternalOriginalOrderProof.renameInto h j Delta hj
  rw [rootGraphRename] at hp
  obtain ⟨he⟩ := valueUnique root value (out.relabel j) (Fin.cons (n.relabel j) Fin.elim0) hg hp
  exact ⟨intervalOutputTransport (n.relabel j) he hi⟩

/-- Arithmetic interval uniqueness and original equality transport give
the converse for every arbitrary symbolic output term. -/
theorem rootGraphOfInterval (out n : OTerm α)
    (h : Nonempty (Derivation body Gamma (interval out n))) :
    Nonempty (Derivation body Gamma (rootGraph out n)) := by
  apply certifiedCases Gamma n _ (certifiedValue n)
  intro β j Delta value hj hg hi
  rw [rootGraphRename]
  have hp := InternalOriginalOrderProof.renameInto h j Delta hj
  rw [intervalRename] at hp
  have he := intervalUnique value (out.relabel j) (n.relabel j) hi hp
  exact outputTransport root value (out.relabel j) (Fin.cons (n.relabel j) Fin.elim0) he hg

theorem actualOriginalSquareRootGraph : InternalSquareRootTargets.ActualOriginalSquareRootGraph := by
  intro body α out n
  obtain ⟨hf⟩ := intervalOfRootGraph (body := body) (Gamma := [rootGraph out n]) out n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rootGraphOfInterval (body := body) (Gamma := [interval out n]) out n
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalSquareRootTotalFunctional : InternalSquareRootTargets.ActualOriginalSquareRootTotalFunctional :=
  fun body => actualOriginalPrograms body 1 root

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootProof
