module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericTargets
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalLessThan (constantOne)
open InternalRawListRecursion (lookup)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentLeaf fragmentGuard)

def HasAuxPayload (raw : Nat) : Prop :=
  ∃ dom cod fn arg, unpackNode raw = some (6,[dom,cod,fn,arg])

def HasLambdaPayload (raw : Nat) : Prop :=
  ∃ dom q, unpackNode raw = some (2,[dom,q])

/-- Exactly the physical auxiliary recursion fragment. Non-aux leaves
must be positive and must reject the literal lambda header, but we do
not require every such terminal to be a well-formed term or typed. -/
inductive SourceFragment : Nat → Prop
  | terminal (prior : Nat) :
      ¬ HasAuxPayload (prior+1) → ¬ HasLambdaPayload (prior+1) → SourceFragment (prior+1)
  | fork (raw dom cod fn arg : Nat) :
      unpackNode raw = some (6,[dom,cod,fn,arg]) →
      SourceFragment fn → SourceFragment arg → SourceFragment raw

abbrev sourceLookup (i old child : Nat) : Nat :=
  evaluate lookup ((i-child) ::ᵥ old ::ᵥ nil)

abbrev fragmentRow (i old : Nat) : Nat :=
  evaluate (auxSyntaxUpdate fragmentLeaf (constantOne 1)) (args i old)

def ExactCoverAuxFragmentNumericRow : Prop :=
  ∀ (i old : Nat),
    (∀ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) →
      (fragmentRow i old = 1 ↔ sourceLookup i old fn = 1 ∧ sourceLookup i old arg = 1)) ∧
    (¬ HasAuxPayload (i+1) → (fragmentRow i old = 1 ↔ ¬ HasLambdaPayload (i+1))) ∧
    (fragmentRow i old = 0 ∨ fragmentRow i old = 1)

def ExactCoverAuxFragmentNumericSource : Prop :=
  run fragmentGuard 0 = 0 ∧
  (∀ raw, run fragmentGuard raw = 0 ∨ run fragmentGuard raw = 1) ∧
  (∀ raw, run fragmentGuard raw = 1 ↔ SourceFragment raw)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericTargets
