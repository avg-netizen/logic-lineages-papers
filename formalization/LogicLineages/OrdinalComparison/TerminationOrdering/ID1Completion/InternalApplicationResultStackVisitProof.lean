module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalApplicationResultStackVisitSupportProof

theorem visitForward (guard leaf : Program 1) (combine : Program 4)
    (d e fp ap value tail results state out : OTerm α)
    (hvalue : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hstate : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) value)))
    (hout : Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state))) :
    Nonempty (Derivation body Gamma (graph6 expandedState out d e fp ap tail results)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail (Fin.cons results Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename,graph6Rename]
  have hvalue' := renameInto hvalue j Delta hj
  have hstate' := renameInto hstate j Delta hj
  have hguard' := renameInto hguard j Delta hj
  have hout' := renameInto hout j Delta hj
  simp only [graph4Rename] at hvalue'
  simp only [graph3Rename] at hstate'
  simp only [graph1Rename,sucRelabel,zRelabel] at hguard'
  simp only [graph1Rename,graph6Rename] at hout'
  simp only [consTermRename,emptyRename] at hq
  have ht := transitionFromQueries guard leaf combine (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (value.relabel j) (tail.relabel j) (results.relabel j)
    (state.relabel j) ys hvalue' hstate' hguard' hq
  have he : Nonempty (Derivation body Delta (graph6 expandedState (ys 18)
      (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
      (tail.relabel j) (results.relabel j))) := hq 18
  have heq := valueUnique (transition guard leaf combine) (ys 18) (out.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ht hout'
  exact outputTransport expandedState (ys 18) (out.relabel j) _ heq he

theorem visitBackward (guard leaf : Program 1) (combine : Program 4)
    (d e fp ap value tail results state out : OTerm α)
    (hvalue : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hstate : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) value)))
    (hout : Nonempty (Derivation body Gamma (graph6 expandedState out d e fp ap tail results))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail (Fin.cons results Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename,graph6Rename]
  have hvalue' := renameInto hvalue j Delta hj
  have hstate' := renameInto hstate j Delta hj
  have hguard' := renameInto hguard j Delta hj
  have hout' := renameInto hout j Delta hj
  simp only [graph4Rename] at hvalue'
  simp only [graph3Rename] at hstate'
  simp only [graph1Rename,sucRelabel,zRelabel] at hguard'
  simp only [graph1Rename,graph6Rename] at hout'
  simp only [consTermRename,emptyRename] at hq
  have ht := transitionFromQueries guard leaf combine (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (value.relabel j) (tail.relabel j) (results.relabel j)
    (state.relabel j) ys hvalue' hstate' hguard' hq
  have he : Nonempty (Derivation body Delta (graph6 expandedState (ys 18)
      (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
      (tail.relabel j) (results.relabel j))) := hq 18
  have heq := valueUnique expandedState (ys 18) (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fp.relabel j)
      (Fin.cons (ap.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (results.relabel j) Fin.elim0)))))) he hout'
  exact outputTransport (transition guard leaf combine) (ys 18) (out.relabel j) _ heq ht

theorem actualOriginalResultStackVisit :
    InternalApplicationResultStackTargets.ActualOriginalResultStackVisit := by
  intro body guard leaf combine α d e fp ap value tail results state out
  let c := graph4 packedApplication value d e fp ap ⊓
    (graph3 visitState state value tail results ⊓ graph1 guard (suc z) value)
  let g := graph1 (transition guard leaf combine) out state
  let r := graph6 expandedState out d e fp ap tail results
  have hc₁ : Nonempty (Derivation body [g,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := visitForward guard leaf combine d e fp ap value tail results state out
    (andLeft hc₁) (andLeft (andRight hc₁)) (andRight (andRight hc₁))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := visitBackward guard leaf combine d e fp ap value tail results state out
    (andLeft hc₂) (andLeft (andRight hc₂)) (andRight (andRight hc₂))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
