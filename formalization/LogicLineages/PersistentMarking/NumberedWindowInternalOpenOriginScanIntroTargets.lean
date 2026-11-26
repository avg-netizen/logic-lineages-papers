module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept scan)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParser (parser)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

def ExactOpenOriginScanConsIntro : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code head tail removed : OrdinaryArithmetic.Term α),
    D B Γ (programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))) →
    D B Γ (rowAccept r head removed) → D B Γ (loopAccept r tail removed) →
    D B Γ (loopAccept r code removed)

def ExactOpenOriginRawScanIntro : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw rows removed : OrdinaryArithmetic.Term α),
    D B Γ (unary parser (suc rows) raw) → D B Γ (loopAccept r rows removed) →
    D B Γ (programGraph (scan r) oneTerm ![raw,removed])

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroTargets
