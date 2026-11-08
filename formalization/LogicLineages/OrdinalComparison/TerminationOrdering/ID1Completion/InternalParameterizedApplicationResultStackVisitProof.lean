module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalParameterizedApplicationResultStack InternalParameterizedApplicationResultStackVisitSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackVisitSupportProof (graph6Rename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem visitForward (guard leaf : Program 2) (combine : Program 5)
    (d e fp ap value tail results state out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) value parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter))) :
    Nonempty (Derivation body Gamma (graph6 expandedState out d e fp ap tail results)) := by
  apply programCases expanded (Fin.cons state Fin.elim0) _
  intro β j Delta candidate hj he
  rw [graph6Rename]
  simp only [consTermRename,emptyRename] at he
  have hp' := renameInto hp j Delta hj
  have hs' := renameInto hs j Delta hj
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph4Rename] at hp'
  simp only [graph3Rename] at hs'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  simp only [graph2Rename] at ho'
  have both := visitAt guard leaf combine (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (value.relabel j) (tail.relabel j) (results.relabel j) (state.relabel j) candidate
    (parameter.relabel j) hp' hs' hg' he
  have eq := valueUnique (transitionP guard leaf combine) candidate (out.relabel j)
    (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andLeft both) ho'
  exact outputTransport expandedState candidate (out.relabel j) _ eq (andRight both)

theorem visitBackward (guard leaf : Program 2) (combine : Program 5)
    (d e fp ap value tail results state out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) value parameter)))
    (ho : Nonempty (Derivation body Gamma (graph6 expandedState out d e fp ap tail results))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  apply programCases expanded (Fin.cons state Fin.elim0) _
  intro β j Delta candidate hj he
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at he
  have hp' := renameInto hp j Delta hj
  have hs' := renameInto hs j Delta hj
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph4Rename] at hp'
  simp only [graph3Rename] at hs'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  simp only [graph6Rename] at ho'
  have both := visitAt guard leaf combine (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (value.relabel j) (tail.relabel j) (results.relabel j) (state.relabel j) candidate
    (parameter.relabel j) hp' hs' hg' he
  have eq := valueUnique expandedState candidate (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fp.relabel j)
      (Fin.cons (ap.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (results.relabel j) Fin.elim0))))))
    (andRight both) ho'
  exact outputTransport (transitionP guard leaf combine) candidate (out.relabel j) _ eq (andLeft both)

theorem actualOriginalParameterizedApplicationResultStackVisit :
    InternalParameterizedApplicationResultStackTargets.ActualOriginalParameterizedApplicationResultStackVisit := by
  intro body guard leaf combine α Gamma d e fp ap value tail results state out parameter
  let c := graph4 packedApplication value d e fp ap ⊓
    (graph3 visitState state value tail results ⊓ graph2 guard (suc z) value parameter)
  let g := graph2 (transitionP guard leaf combine) out state parameter
  let r := graph6 expandedState out d e fp ap tail results
  have hc₁ : Nonempty (Derivation body (g :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := visitForward guard leaf combine d e fp ap value tail results state out parameter
    (andLeft hc₁) (andLeft (andRight hc₁)) (andRight (andRight hc₁))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := visitBackward guard leaf combine d e fp ap value tail results state out parameter
    (andLeft hc₂) (andLeft (andRight hc₂)) (andRight (andRight hc₂))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitProof
