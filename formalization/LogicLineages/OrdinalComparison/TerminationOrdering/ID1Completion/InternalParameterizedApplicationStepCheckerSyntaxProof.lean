module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationStepChecker
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalParameterizedApplicationResultStack (appendParameter)
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem appendParameterThree {α : Type} (a b c parameter : α) :
    appendParameter (Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0))) parameter =
      Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons parameter Fin.elim0))) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        rfl

theorem appendParameterFive {α : Type} (a b c d e parameter : α) :
    appendParameter (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e Fin.elim0))))) parameter =
      Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e (Fin.cons parameter Fin.elim0))))) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · refine Fin.cases ?_ (fun k => ?_) k
          · rfl
          · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
            rfl

@[simp] theorem endpointGraphRename {β : Type} (P : Program 6)
    (out d e s t a parameter : OTerm α) (j : α → β) :
    (endpointGraph P out d e s t a parameter).relabel j =
      endpointGraph P (out.relabel j) (d.relabel j) (e.relabel j)
        (s.relabel j) (t.relabel j) (a.relabel j) (parameter.relabel j) := by
  change (programGraph P out (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t
    (Fin.cons a (Fin.cons parameter Fin.elim0))))))).relabel j =
      programGraph P (out.relabel j) (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
        (Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
          (Fin.cons (a.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))))))
  simp only [programRename,consTermRename,emptyRename]

@[simp] theorem transitionGraphRename {β : Type} (P : Program 6)
    (out state parameter : OTerm α) (j : α → β) :
    (transitionGraph P out state parameter).relabel j =
      transitionGraph P (out.relabel j) (state.relabel j) (parameter.relabel j) :=
  graph2Rename _ _ _ _ _

@[simp] theorem normalizerGraphRename {β : Type} (P : Program 6)
    (out state parameter : OTerm α) (j : α → β) :
    (normalizerGraph P out state parameter).relabel j =
      normalizerGraph P (out.relabel j) (state.relabel j) (parameter.relabel j) :=
  graph2Rename _ _ _ _ _

@[simp] theorem checkerGraphRename {β : Type} (E : Program 6) (C : Program 4)
    (out s t k parameter : OTerm α) (j : α → β) :
    (checkerGraph E C out s t k parameter).relabel j =
      checkerGraph E C (out.relabel j) (s.relabel j) (t.relabel j)
        (k.relabel j) (parameter.relabel j) := graph4Rename _ _ _ _ _ _ _

@[simp] theorem liftedCheckerPremisesRename {β : Type} (E : Program 6)
    (d e arrow s t a k s' t' k' parameter : OTerm α) (j : α → β) :
    (liftedCheckerPremises E d e arrow s t a k s' t' k' parameter).relabel j =
      liftedCheckerPremises E (d.relabel j) (e.relabel j) (arrow.relabel j)
        (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
        (s'.relabel j) (t'.relabel j) (k'.relabel j) (parameter.relabel j) := by
  simp only [liftedCheckerPremises,conjunctionRename,
    graph1Rename,graph2Rename,graph4Rename,endpointGraphRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem guardedIffAt {A p q : Formula α}
    (hf : Nonempty (Derivation body (p :: A :: Gamma) q))
    (hb : Nonempty (Derivation body (q :: A :: Gamma) p)) :
    Nonempty (Derivation body Gamma (A.imp (p.iff q))) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
