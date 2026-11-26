module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename goodIntro)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Forward cons construction, re-established here at arbitrary arity
because the #689 helper is private to its own live proof. -/
theorem consOfGraph {n : Nat} (p q : Program n) (h t : OTerm α) (xs : Fin n → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph p h xs)))
    (right : Nonempty (Derivation body Γ (programGraph q t xs))) :
    Nonempty (Derivation body Γ (programGraph (consOf p q) (rawCons h t) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0)) (rawCons h t) xs ![h,t]
    (consGraph h t)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

/-- Forward graph of the actual two-field emitter at known components. -/
theorem emitGraph {n : Nat} (p q : Program n) (a b : OTerm α) (xs : Fin n → OTerm α)
    (flag : Nonempty (Derivation body Γ (programGraph p a xs)))
    (frame : Nonempty (Derivation body Γ (programGraph q b xs))) :
    Nonempty (Derivation body Γ (programGraph (emitState p q) (stateTerm a b) xs)) := by
  have rest := consOfGraph q (constantZero n) b z xs frame (constantZeroValue xs)
  exact consOfGraph p (consOf q (constantZero n)) a (rawCons b z) xs flag rest

/-- Any supplied output of an emitter whose FLAG program is the literal
zero constant has the shape. Original totality supplies the unknown frame
component as an object eigenvariable; functionality of the same emitter
on the same tape identifies the supplied output. -/
theorem zeroFlagShape {n : Nat} (q : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (emitState (constantZero n) q) out xs))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  apply programCases q xs _
  intro β j Δ v hj hv
  rw [goodRename]
  have h' := renameInto h j Δ hj
  rw [programRename] at h'
  have built := emitGraph (constantZero n) q z v (fun i => (xs i).relabel j)
    (constantZeroValue _) hv
  have he := valueUnique (emitState (constantZero n) q) (out.relabel j) (stateTerm z v)
    (fun i => (xs i).relabel j) h' built
  exact goodIntro (out.relabel j) z v he ⟨orLeft (refl z)⟩

/-- Same, when the FRAME program is the literal zero constant. -/
theorem zeroFrameShape {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (emitState p (constantZero n)) out xs))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  apply programCases p xs _
  intro β j Δ v hj hv
  rw [goodRename]
  have h' := renameInto h j Δ hj
  rw [programRename] at h'
  have built := emitGraph p (constantZero n) v z (fun i => (xs i).relabel j)
    hv (constantZeroValue _)
  have he := valueUnique (emitState p (constantZero n)) (out.relabel j) (stateTerm v z)
    (fun i => (xs i).relabel j) h' built
  exact goodIntro (out.relabel j) v z he ⟨orRight (refl z)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
