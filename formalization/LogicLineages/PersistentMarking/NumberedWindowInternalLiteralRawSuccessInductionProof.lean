module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessInductionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue recursionZeroValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalSparseRawTick (rootCall stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralRawSuccessorCasesProof (exact_OpenLiteralRawSuccessorSuccessCases)
open NumberedWindowInternalLiteralRawSuccessMotiveProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- On an arbitrary accepted open run, either the successful scratch
was already the initial scratch, or it was produced at an actual
root tick at some predecessor state of the SAME run. The scratch,
its actual row selectors, and the root call are provided in the same
permitted object context. No arithmetic truth reflection is used. -/
theorem exact_OpenLiteralRawSuccessElimination (p other : Program 3)
    (fuel start k f : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (iterateState p other) (stateTerm (suc k) f) ![fuel,start]))
    (initial : ∀ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ Δ) →
      D B Δ (eqn start (stateTerm (suc k) f)) → D B Δ goal)
    (rooted : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (u prev frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev ![u,start.relabel j]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (rootCall p) (suc (k.relabel j)) tape) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  let out := stateTerm (suc k) f
  let J : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let k' := k.relabel J
  let f' := f.relabel J
  let start' := start.relabel J
  let goal' := goal.relabel J
  let out' := stateTerm (suc k') f'
  let θ := successMotive p other v start' out' goal'
  have outRename : out.relabel J = out' := by
    simp only [out,out',k',f',NumberedWindowInternalSparseRawTickShapeSyntaxProof.stateRename,
      ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel]
  have inst (a : OTerm α) : instantiate θ (emb a) = successMotive p other a start out goal := by
    simpa only [θ,J,v,start',goal',← outRename] using successMotiveInstantiate p other start out a goal
  have next : successorInstance θ = successMotive p other (suc v) start' out' goal' := by
    simpa only [θ,J,v,start',goal',← outRename] using successMotiveNext p other start out goal
  have first : D B Γ (successMotive p other z start out goal) := by
    let h := programGraph (iterateState p other) out ![z,start]
    let Ω := h :: Γ
    have h0 : D B Ω (programGraph (iterateState p other) start ![z,start]) :=
      recursionZeroValue (.projection 0) (step p other) start ![start]
        (projectionValue 0 ![start])
    have got : D B Ω h := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have eq := valueUnique (iterateState p other) start out ![z,start] h0 got
    obtain ⟨answered⟩ := initial Ω (fun φ mem => List.mem_cons_of_mem _ mem) eq
    exact ⟨Derivation.implicationIntroduction answered⟩
  have each : D B (θ :: Γ.map weaken) (successMotive p other (suc v) start' out' goal') := by
    let h := programGraph (iterateState p other) out' ![suc v,start']
    let Ω := h :: θ :: Γ.map weaken
    have before : D B Ω (successMotive p other v start' out' goal') :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have entry (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel J ∈ Ω :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,mem,rfl⟩))
    have acc : D B Ω h := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have answered : D B Ω goal' := by
      apply exact_OpenLiteralRawSuccessorSuccessCases p other v start' k' f' goal' acc
      · intro β l Δ keep early
        have ih := renameInto before l Δ keep
        rw [successMotiveRename] at ih
        have exactIH : D B Δ ((programGraph (iterateState p other)
          (stateTerm (suc (k'.relabel l)) (f'.relabel l)) ![v.relabel l,start'.relabel l]).imp
          (goal'.relabel l)) := by
          simpa only [successMotive,out',NumberedWindowInternalSparseRawTickShapeSyntaxProof.stateRename,
            ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel] using ih
        obtain ⟨imp⟩ := exactIH
        obtain ⟨run⟩ := early
        exact ⟨Derivation.implicationElimination imp run⟩
      · intro β l Δ prev frame tape keep run live left cert right hit
        let m := l ∘ J
        have retain (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel m ∈ Δ := by
          simpa only [m,formulaRelabelComposition] using keep _ (entry φ mem)
        have reply := rooted β m Δ (v.relabel l) prev frame tape retain
          (by simpa only [m,start',Term.relabel_relabel] using run)
          live left cert right (by simpa only [m,k',Term.relabel_relabel] using hit)
        simpa only [m,goal',formulaRelabelComposition] using reply
    obtain ⟨derived⟩ := answered
    exact ⟨Derivation.implicationIntroduction derived⟩
  obtain ⟨first⟩ := first
  obtain ⟨each⟩ := each
  have result := Derivation.universalElimination (emb fuel)
    (natInduction θ (by rw [inst]; exact first) (by rw [next]; exact each))
  rw [inst] at result
  obtain ⟨check⟩ := held
  exact ⟨Derivation.implicationElimination result check⟩

#print axioms exact_OpenLiteralRawSuccessElimination
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessInductionProof
