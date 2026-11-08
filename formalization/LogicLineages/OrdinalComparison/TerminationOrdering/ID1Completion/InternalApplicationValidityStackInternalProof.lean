module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalApplicationValidityStackInternalSupportProof

theorem pushForward (node leaf : Program 1)
    (d e fp ap tail state out : OTerm α)
    (hstate : Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap tail)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hout : Nonempty (Derivation body Gamma (graph1 (transition node leaf) out state))) :
    Nonempty (Derivation body Gamma (InternalApplicationStepPeel.graph5 expandedFrame out d e fp ap tail)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail Fin.elim0))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename,graph5Rename]
  have hstate' := renameInto hstate j Delta hj
  have hnode' := renameInto hnode j Delta hj
  have hout' := renameInto hout j Delta hj
  simp only [graph5Rename] at hstate'
  simp only [graph1Rename,sucRelabel,zRelabel] at hnode'
  simp only [graph1Rename,graph5Rename] at hout'
  simp only [consTermRename,emptyRename] at hq
  have ht := transitionFromQueries node leaf (d.relabel j) (e.relabel j) (fp.relabel j)
    (ap.relabel j) (tail.relabel j) (state.relabel j) ys hstate' hnode' hq
  have he : Nonempty (Derivation body Delta
      (InternalApplicationStepPeel.graph5 expandedFrame (ys 10) (d.relabel j) (e.relabel j)
        (fp.relabel j) (ap.relabel j) (tail.relabel j))) := hq 10
  have heq := valueUnique (transition node leaf) (ys 10) (out.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ht hout'
  exact outputTransport expandedFrame (ys 10) (out.relabel j) _ heq he

theorem pushBackward (node leaf : Program 1)
    (d e fp ap tail state out : OTerm α)
    (hstate : Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap tail)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hout : Nonempty (Derivation body Gamma (InternalApplicationStepPeel.graph5 expandedFrame out d e fp ap tail))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) out state)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail Fin.elim0))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename,graph5Rename]
  have hstate' := renameInto hstate j Delta hj
  have hnode' := renameInto hnode j Delta hj
  have hout' := renameInto hout j Delta hj
  simp only [graph5Rename] at hstate'
  simp only [graph1Rename,sucRelabel,zRelabel] at hnode'
  simp only [graph1Rename,graph5Rename] at hout'
  simp only [consTermRename,emptyRename] at hq
  have ht := transitionFromQueries node leaf (d.relabel j) (e.relabel j) (fp.relabel j)
    (ap.relabel j) (tail.relabel j) (state.relabel j) ys hstate' hnode' hq
  have he : Nonempty (Derivation body Delta
      (InternalApplicationStepPeel.graph5 expandedFrame (ys 10) (d.relabel j) (e.relabel j)
        (fp.relabel j) (ap.relabel j) (tail.relabel j))) := hq 10
  have heq := valueUnique expandedFrame (ys 10) (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fp.relabel j)
      (Fin.cons (ap.relabel j) (Fin.cons (tail.relabel j) Fin.elim0))))) he hout'
  exact outputTransport (transition node leaf) (ys 10) (out.relabel j) _ heq ht

theorem actualOriginalApplicationStackPush :
    InternalApplicationValidityStackTargets.ActualOriginalApplicationStackPush := by
  intro body node leaf α d e fp ap tail state out
  let c := InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap tail ⊓
    graph1 node (suc z) e
  let g := graph1 (transition node leaf) out state
  let r := InternalApplicationStepPeel.graph5 expandedFrame out d e fp ap tail
  have hc₁ : Nonempty (Derivation body [g,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := pushForward node leaf d e fp ap tail state out
    (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := pushBackward node leaf d e fp ap tail state out
    (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalRecursiveSourceTarget :
    InternalApplicationValidityStackTargets.ActualOriginalRecursiveSourceTarget := by
  intro body old member α value
  let target := validator (InternalLessThan.constantOne 1) old.targetValid
  let universeValidator := validator member old.sourceValid
  let p := graph1 (InternalAcceptance.conjunction target universeValidator) (suc z) value
  obtain ⟨h⟩ := conjunctionRecover (body := body) (Gamma := [p]) target universeValidator
    (Fin.cons value Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft h)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalProof
