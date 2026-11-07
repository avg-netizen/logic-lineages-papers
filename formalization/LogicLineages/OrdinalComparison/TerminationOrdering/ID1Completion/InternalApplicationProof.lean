module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplication InternalApplicationSyntaxProof InternalApplicationGraphProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationExistsIntro (p : Program 6) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph p (suc z) (inputs xs out)))) :
    Nonempty (Derivation body Gamma (applicationExists p xs)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rw [applicationOutputInstantiate]
  exact h

theorem activeTotality (active result : Program 5) (old : Program 6) (xs : Fin 5 → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph active (suc z) xs))) :
    Nonempty (Derivation body Gamma (applicationExists (application active result old) xs)) := by
  apply programCases result xs _
  intro β j Delta out hj ho
  rw [applicationExistsRename]
  have hc' := renameInto hc j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at hc'
  exact applicationExistsIntro _ _ out (activeAccept active result old _ out hc' ho)

theorem actualOriginalActiveTotality : InternalApplicationTargets.ActualOriginalActiveTotality := by
  intro body active result old α xs
  obtain ⟨d⟩ := activeTotality (body := body)
    (Gamma := [programGraph active (suc z) xs]) active result old xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem activeFunctionality (active result : Program 5) (old : Program 6)
    (xs : Fin 5 → OTerm α) (out other : OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph active (suc z) xs)))
    (ho : Nonempty (Derivation body Gamma
      (programGraph (application active result old) (suc z) (inputs xs out))))
    (ht : Nonempty (Derivation body Gamma
      (programGraph (application active result old) (suc z) (inputs xs other)))) :
    Nonempty (Derivation body Gamma (equal out other)) := by
  rw [equalEqn]
  exact valueUnique result out other xs (activeRecover active result old xs out hc ho)
    (activeRecover active result old xs other hc ht)

theorem actualOriginalActiveFunctionality : InternalApplicationTargets.ActualOriginalActiveFunctionality := by
  intro body active result old α xs out other
  let c := programGraph active (suc z) xs
  let p := application active result old
  let g := programGraph p (suc z) (inputs xs out) ⊓ programGraph p (suc z) (inputs xs other)
  obtain ⟨d⟩ := activeFunctionality (body := body) (Gamma := [g,c]) active result old xs out other
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationProof
