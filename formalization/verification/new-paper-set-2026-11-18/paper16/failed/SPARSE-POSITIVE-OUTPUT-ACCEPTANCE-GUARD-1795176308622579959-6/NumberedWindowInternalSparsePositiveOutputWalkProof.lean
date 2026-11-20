module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputWalkProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveFold (chosenWalk finish)
open NumberedWindowInternalSparsePositiveOutputTargets

attribute [local irreducible] programGraph finish

abbrev succAt (i : Fin 5) : Program 5 :=
  .composition .succ (fun _ : Fin 1 => .projection i)
abbrev picks : Fin 4 → Program 5 :=
  ![.projection 0,.projection 1,succAt 2,.projection 3]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem succAtValue (i : Fin 5) (xs : Fin 5 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph (succAt i) (suc (xs i)) xs)) :=
  compositionValue .succ (fun _ : Fin 1 => .projection i) (suc (xs i)) xs
    (fun _ : Fin 1 => xs i) (successorValue (fun _ : Fin 1 => xs i))
    (fun _ => projectionValue i xs)

private theorem inputs (c ty source cert target : OTerm α) (i : Fin 4) :
    Nonempty (Derivation body Γ
      (programGraph (picks i) (args4 c ty (suc source) cert i) (args5 c ty source cert target))) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun u => Fin.elim0 u) d) b) a) i
  · exact projectionValue (0 : Fin 5) (args5 c ty source cert target)
  · exact projectionValue (1 : Fin 5) (args5 c ty source cert target)
  · exact succAtValue (2 : Fin 5) (args5 c ty source cert target)
  · exact projectionValue (3 : Fin 5) (args5 c ty source cert target)

theorem walkOfFinish (raw : Program 5) (least : Program 3) (out c ty source cert target : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (finish raw least) out (args4 c ty (suc source) cert)))) :
    Nonempty (Derivation body Γ (programGraph (chosenWalk raw least) out
      (args5 c ty source cert target))) := by
  unfold chosenWalk
  exact compositionValue (finish raw least) picks out (args5 c ty source cert target)
    (args4 c ty (suc source) cert) h (inputs c ty source cert target)

theorem finishOfWalk (raw : Program 5) (least : Program 3) (out c ty source cert target : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (chosenWalk raw least) out
      (args5 c ty source cert target)))) :
    Nonempty (Derivation body Γ (programGraph (finish raw least) out (args4 c ty (suc source) cert))) := by
  unfold chosenWalk at h
  exact compositionRecover (finish raw least) picks out (args5 c ty source cert target)
    (args4 c ty (suc source) cert) h (inputs c ty source cert target)

theorem walk : OpenChosenWalk := by
  intro body raw least α out c ty source cert target
  let a := programGraph (chosenWalk raw least) out (args5 c ty source cert target)
  let b := programGraph (finish raw least) out (args4 c ty (suc source) cert)
  obtain ⟨f⟩ := finishOfWalk (body := body) (Γ := [a]) raw least out c ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := walkOfFinish (body := body) (Γ := [b]) raw least out c ty source cert target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputWalkProof
