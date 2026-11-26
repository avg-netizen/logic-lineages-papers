module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue successorValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalQuotientComparisonProof (orLeft)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (initialState iterateState ownState)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename goodIntro)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph emitGraph)
open NumberedWindowInternalSparseRawRunShapeInductionProof (loopShape)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Forward graph of the actual initial scratch on ANY ternary tape,
built from the literal projections, zero constant, cons and successor. -/
theorem initialGraph (xs : Fin 3 → OTerm α) :
    Nonempty (Derivation body Γ (programGraph initialState
      (stateTerm z (frameValueTerm (xs 0) (xs 1) (xs 2))) xs)) := by
  let payload : OTerm α := rawCons (xs 0) (rawCons (xs 1) (rawCons (xs 2) z))
  let packed : Program 3 :=
    consOf (.projection 0) (consOf (.projection 1) (consOf (.projection 2) (constantZero 3)))
  let tail2 : Program 3 := consOf (.projection 2) (constantZero 3)
  let tail1 : Program 3 := consOf (.projection 1) tail2
  have c2 : Nonempty (Derivation body Γ (programGraph tail2 (rawCons (xs 2) z) xs)) :=
    consOfGraph (.projection 2) (constantZero 3) (xs 2) z xs
      (projectionValue 2 xs) (constantZeroValue xs)
  have c1 : Nonempty (Derivation body Γ
      (programGraph tail1 (rawCons (xs 1) (rawCons (xs 2) z)) xs)) :=
    consOfGraph (.projection 1) tail2 (xs 1) (rawCons (xs 2) z) xs (projectionValue 1 xs) c2
  have c0 : Nonempty (Derivation body Γ (programGraph packed payload xs)) :=
    consOfGraph (.projection 0) tail1 (xs 0) (rawCons (xs 1) (rawCons (xs 2) z)) xs
      (projectionValue 0 xs) c1
  have frame : Nonempty (Derivation body Γ (programGraph
      (.composition .succ (fun _ : Fin 1 => packed)) (suc payload) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => packed) (suc payload) xs ![payload]
      (successorValue ![payload])
    intro i
    obtain rfl := Fin.eq_zero i
    exact c0
  exact emitGraph (constantZero 3) (.composition .succ (fun _ : Fin 1 => packed)) z
    (suc payload) xs (constantZeroValue xs) frame

/-- The actual own-witness state: the composition is eliminated, the
initial component is identified by functionality with the forward
initial graph (flag literally zero), and the loop shape applies at the
component fuel eigenvariable. -/
theorem ownShape (p other : Program 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (ownState p other) out xs))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  apply programCompositionCases (iterateState p other) ![.projection 1,initialState]
    out xs (goodState out) h
  intro β j ys Δ _ hf hg
  rw [goodRename]
  let xs' : Fin 3 → OTerm β := fun a => (xs a).relabel j
  let start : OTerm β := stateTerm z (frameValueTerm (xs' 0) (xs' 1) (xs' 2))
  have hi : Nonempty (Derivation body Δ (programGraph initialState (ys 1) xs')) := hg 1
  have he := valueUnique initialState (ys 1) start xs' hi (initialGraph xs')
  have good : Nonempty (Derivation body Δ (goodState (ys 1))) :=
    goodIntro (ys 1) z (frameValueTerm (xs' 0) (xs' 1) (xs' 2)) he ⟨orLeft (refl z)⟩
  have eta : ys = ![ys 0,ys 1] := by
    funext i
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun e => Fin.elim0 e) k) i
  rw [eta] at hf
  exact loopShape p other (ys 0) (ys 1) (out.relabel j) good hf

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeOwnProof
