module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedActivationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedApplicationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open ApplicationGuarded ApplicationGuardedActivationProof InternalApplicationSyntaxProof InternalApplicationProof
open GuardedSourceSyntaxProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem existsApplicationGraph {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) :
    existsApplication comp context sigma tau f a = InternalApplication.applicationExists comp.application
      ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a] := by
  unfold existsApplication InternalApplication.applicationExists
  rw [literalApplicationGraph]
  congr 1
  congr 1
  funext i
  exact Fin.cases (numeralRename context Sum.inl).symm
    (Fin.cases (numeralRename (typeNumber sigma) Sum.inl).symm
      (Fin.cases (numeralRename (typeNumber tau) Sum.inl).symm
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

theorem actualOriginalTotality : ApplicationGuardedTargets.ActualOriginalTotality := by
  intro body old window arrow result context sigma tau hw ha α f a
  let comp := InternalApplication.computability old window arrow result
  let P := domain comp context sigma tau f a
  have hc := activationClosure (body := body) (Gamma := [P]) old window arrow context sigma tau hw ha f a
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := activeTotality (ApplicationDomain.activation window old.typed old.guard arrow)
    result old.application ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a] hc
  change Derivation body [P] (InternalApplication.applicationExists comp.application _) at d
  rw [← existsApplicationGraph comp context sigma tau f a] at d
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalFunctionality : ApplicationGuardedTargets.ActualOriginalFunctionality := by
  intro body old window arrow result context sigma tau hw ha α f a out other
  let comp := InternalApplication.computability old window arrow result
  let P := domain comp context sigma tau f a
  let Q := InternalApplication.literalApplication comp.application context sigma tau f a out ⊓
    InternalApplication.literalApplication comp.application context sigma tau f a other
  have hc := activationClosure (body := body) (Gamma := [Q,P]) old window arrow context sigma tau hw ha f a
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have ho : Nonempty (Derivation body [Q,P]
      (InternalApplication.literalApplication comp.application context sigma tau f a out)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have ht : Nonempty (Derivation body [Q,P]
      (InternalApplication.literalApplication comp.application context sigma tau f a other)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  rw [literalApplicationGraph] at ho ht
  obtain ⟨d⟩ := activeFunctionality (ApplicationDomain.activation window old.typed old.guard arrow)
    result old.application ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a]
    out other hc ho ht
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedApplicationProof
