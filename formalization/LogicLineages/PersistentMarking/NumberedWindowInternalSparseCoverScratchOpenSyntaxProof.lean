module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratchOpenTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem callbackArguments (s : Settings) (seed : OTerm α) (i : Fin 3) :
    Nonempty (Derivation body Γ (programGraph
      ((![literal 1 (Encodable.encode s.window.2),
        literal 1 (Encodable.encode s.types), .projection 0] : Fin 3 → Program 1) i)
      (callbackTape s seed i) ![seed])) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact literalGraph (Encodable.encode s.window.2) ![seed]
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact literalGraph (Encodable.encode s.types) ![seed]
    · obtain rfl := Fin.eq_zero i
      exact projectionValue 0 ![seed]

theorem optionFromCallback (C : Program 3) (s : Settings) (value seed : OTerm α)
    (callback : Nonempty (Derivation body Γ (callbackAt C s value seed))) :
    Nonempty (Derivation body Γ (unary (coverOption C s) value seed)) :=
  compositionValue C
    ![literal 1 (Encodable.encode s.window.2), literal 1 (Encodable.encode s.types), .projection 0]
    value ![seed] (callbackTape s seed) callback (callbackArguments s seed)

theorem callbackFromOption (C : Program 3) (s : Settings) (value seed : OTerm α)
    (covered : Nonempty (Derivation body Γ (unary (coverOption C s) value seed))) :
    Nonempty (Derivation body Γ (callbackAt C s value seed)) :=
  compositionRecover C
    ![literal 1 (Encodable.encode s.window.2), literal 1 (Encodable.encode s.types), .projection 0]
    value ![seed] (callbackTape s seed) covered (callbackArguments s seed)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
