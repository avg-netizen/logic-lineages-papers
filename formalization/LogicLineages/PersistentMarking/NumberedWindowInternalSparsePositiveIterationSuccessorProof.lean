module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport valueUnique outputTransport)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph stepGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6 callRename selectedRename)
open NumberedWindowInternalSparsePositiveIterationTargets

abbrev loopArgs {α : Type} (fuel c ty start cert : OTerm α) : Fin 5 → OTerm α :=
  ![fuel,c,ty,start,cert]

theorem loopArgsRename {α β : Type} (fuel c ty start cert : OTerm α) (j : α → β) :
    (fun i => (loopArgs fuel c ty start cert i).relabel j) =
      loopArgs (fuel.relabel j) (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i <;> rfl

theorem loopRename {α β : Type} (raw : Program 5) (least : Program 3)
    (out fuel c ty start cert : OTerm α) (j : α → β) :
    (loopGraph raw least out fuel c ty start cert).relabel j =
      loopGraph raw least (out.relabel j) (fuel.relabel j) (c.relabel j) (ty.relabel j)
        (start.relabel j) (cert.relabel j) := by
  unfold loopGraph
  change (programGraph (iterateState raw least) out (loopArgs fuel c ty start cert)).relabel j = _
  rw [programRename,loopArgsRename] <;> rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveLoop {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (raw : Program 5) (least : Program 3)
    (out fuel c ty start cert : OTerm α)
    (known : Nonempty (Derivation body Γ (loopGraph raw least out fuel c ty start cert))) :
    Nonempty (Derivation body Δ (loopGraph raw least (out.relabel j) (fuel.relabel j)
      (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j))) := by
  have next := renameInto known j Δ hJ
  rw [loopRename] at next
  exact next

theorem moveFuel (raw : Program 5) (least : Program 3)
    (out a b c ty start cert : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn a b)))
    (known : Nonempty (Derivation body Γ (loopGraph raw least out a c ty start cert))) :
    Nonempty (Derivation body Γ (loopGraph raw least out b c ty start cert)) :=
  headTransport (iterateState raw least) out a b ![c,ty,start,cert] eq known

theorem loopIntro (raw : Program 5) (least : Program 3)
    (out prior fuel c ty start cert : OTerm α)
    (known : Nonempty (Derivation body Γ (loopGraph raw least prior fuel c ty start cert)))
    (step : Nonempty (Derivation body Γ (stepGraph raw least out fuel prior c ty start cert))) :
    Nonempty (Derivation body Γ (loopGraph raw least out (suc fuel) c ty start cert)) :=
  recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula initial)
    (OrdinaryArithmetic.graphFormula (iterateStep raw least)) out fuel prior ![c,ty,start,cert] known step

theorem loopRead (raw : Program 5) (least : Program 3)
    (out prior fuel c ty start cert : OTerm α)
    (known : Nonempty (Derivation body Γ (loopGraph raw least prior fuel c ty start cert)))
    (next : Nonempty (Derivation body Γ (loopGraph raw least out (suc fuel) c ty start cert))) :
    Nonempty (Derivation body Γ (stepGraph raw least out fuel prior c ty start cert)) := by
  apply programCases (iterateStep raw least) (call6 fuel prior c ty start cert) _
  intro β j Δ result hJ proposal
  change Nonempty (Derivation body Δ
    ((programGraph (iterateStep raw least) out (call6 fuel prior c ty start cert)).relabel j))
  rw [selectedRename]
  rw [callRename] at proposal
  let fuel' := fuel.relabel j
  let c' := c.relabel j
  let t' := ty.relabel j
  let init' := start.relabel j
  let cert' := cert.relabel j
  let prior' := prior.relabel j
  have prev := moveLoop j Δ hJ raw least prior fuel c ty start cert known
  have actual := moveLoop j Δ hJ raw least out (suc fuel) c ty start cert next
  rw [sucRelabel] at actual
  have composed := loopIntro raw least result prior' fuel' c' t' init' cert' prev proposal
  have eq := valueUnique (iterateState raw least) result (out.relabel j)
    (loopArgs (suc fuel') c' t' init' cert') composed actual
  exact outputTransport (iterateStep raw least) result (out.relabel j)
    (call6 fuel' prior' c' t' init' cert') eq proposal

theorem successor : OpenRecursorSuccessor := by
  intro body raw least α out prior fuel c ty start cert
  let known := loopGraph raw least prior fuel c ty start cert
  let a := stepGraph raw least out fuel prior c ty start cert
  let b := loopGraph raw least out (suc fuel) c ty start cert
  have ha : Derivation body [a,known] known :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hb : Derivation body [b,known] known :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨forward⟩ := loopIntro raw least out prior fuel c ty start cert
    ⟨ha⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := loopRead raw least out prior fuel c ty start cert
    ⟨hb⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
