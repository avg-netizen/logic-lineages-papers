module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFixedGrammarGuardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem memberCalls (code : Nat) (ty : OTerm α) (i : Fin 2) :
    Nonempty (Derivation body Γ
      (programGraph ((![literal 1 code,.projection 0] : Fin 2 → Program 1) i)
        ((![numeral code,ty] : Fin 2 → OTerm α) i) ![ty])) :=
  Fin.cases (literalGraph code ![ty])
    (Fin.cases (projectionValue 0 ![ty]) (fun j => Fin.elim0 j)) i

theorem reports : ExactOpenRefitGuardReports := by
  intro S K T body α Γ ty source reports
  let code := Encodable.encode (fixed S K).types
  let parts : Fin 2 → Program 1 := ![literal 1 code,.projection 0]
  let G := grammarTypeAt S K
  have forward : Nonempty (Derivation body (source :: Γ) reports) := by
    have start : Nonempty (Derivation body (source :: Γ) source) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨both⟩ := conjunctionRecover T G ![ty] start
    obtain ⟨member⟩ := compositionRecover scratchMember parts (suc z) ![ty]
      ![numeral code,ty] ⟨Derivation.conjunctionRight both⟩ (memberCalls code ty)
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft both) member⟩
  have backward : Nonempty (Derivation body (reports :: Γ) source) := by
    have start : Derivation body (reports :: Γ) reports := Derivation.hypothesis List.mem_cons_self
    have member : Nonempty (Derivation body (reports :: Γ) (unary G (suc z) ty)) :=
      compositionValue scratchMember parts (suc z) ![ty] ![numeral code,ty]
        ⟨Derivation.conjunctionRight start⟩ (memberCalls code ty)
    exact conjunctionAccept T G ![ty] ⟨Derivation.conjunctionLeft start⟩ member
  obtain ⟨f⟩ := forward
  obtain ⟨b⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction b)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardOpenProof
