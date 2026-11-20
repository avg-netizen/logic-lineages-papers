module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (chosenState iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveOutputTargets

attribute [local irreducible] programGraph iterateState

abbrev picks : Fin 5 → Program 4 :=
  ![.projection 3,.projection 0,.projection 1,.projection 2,.projection 3]
abbrev selectedArgs {α : Type} (c ty current cert : OTerm α) : Fin 5 → OTerm α :=
  ![cert,c,ty,current,cert]

private theorem inputs {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (c ty current cert : OTerm α) (i : Fin 5) :
    Nonempty (Derivation body Γ
      (programGraph (picks i) (selectedArgs c ty current cert i) (args4 c ty current cert))) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i
  · exact projectionValue (3 : Fin 4) (args4 c ty current cert)
  · exact projectionValue (0 : Fin 4) (args4 c ty current cert)
  · exact projectionValue (1 : Fin 4) (args4 c ty current cert)
  · exact projectionValue (2 : Fin 4) (args4 c ty current cert)
  · exact projectionValue (3 : Fin 4) (args4 c ty current cert)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem stateOfLoop (raw : Program 5) (least : Program 3) (out c ty current cert : OTerm α)
    (h : Nonempty (Derivation body Γ (loopGraph raw least out cert c ty current cert))) :
    Nonempty (Derivation body Γ (programGraph (chosenState raw least) out (args4 c ty current cert))) := by
  unfold chosenState
  exact compositionValue (iterateState raw least) picks out (args4 c ty current cert)
    (selectedArgs c ty current cert) h (inputs c ty current cert)

theorem loopOfState (raw : Program 5) (least : Program 3) (out c ty current cert : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (chosenState raw least) out (args4 c ty current cert)))) :
    Nonempty (Derivation body Γ (loopGraph raw least out cert c ty current cert)) := by
  unfold chosenState at h
  exact compositionRecover (iterateState raw least) picks out (args4 c ty current cert)
    (selectedArgs c ty current cert) h (inputs c ty current cert)

theorem chosen : OpenChosenState := by
  intro body raw least α out c ty current cert
  let a := programGraph (chosenState raw least) out (args4 c ty current cert)
  let b := loopGraph raw least out cert c ty current cert
  obtain ⟨f⟩ := loopOfState (body := body) (Γ := [a]) raw least out c ty current cert
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := stateOfLoop (body := body) (Γ := [b]) raw least out c ty current cert
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
