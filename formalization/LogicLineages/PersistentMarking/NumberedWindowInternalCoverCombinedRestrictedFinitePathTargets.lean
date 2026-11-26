module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets (thinProvided)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets (suppliedPath)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)

/-- A nonempty splice of actual object proof rows, not an object path
codec. In a step, the first row's raw destination is literally the
tail's raw source. Every row uses the same selected programs and Γ. -/
inductive HeldHops (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx cod : OTerm α) : OTerm α → OTerm α → Prop
  | last {src dst : OTerm α} (wr : OTerm α) :
      Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst)) →
      HeldHops C X W s raw body α Γ ctx cod src dst
  | more {src mid dst : OTerm α} (wr : OTerm α) :
      Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr mid)) →
      HeldHops C X W s raw body α Γ ctx cod mid dst →
      HeldHops C X W s raw body α Γ ctx cod src dst

/-- Same-argument, literal function-side witness restriction for the
actual selected P. Endpoints here are function keys, not parent keys. -/
inductive HeldFixedArgHops (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg : OTerm α) : OTerm α → OTerm α → Prop
  | last {fn next : OTerm α} (child : OTerm α) :
      Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod
        (auxiliaryTerm dom cod fn arg) (functionWitnessTerm child) (auxiliaryTerm dom cod next arg))) →
      HeldFixedArgHops C X W s raw body α Γ ctx dom cod arg fn next
  | more {fn middle next : OTerm α} (child : OTerm α) :
      Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod
        (auxiliaryTerm dom cod fn arg) (functionWitnessTerm child) (auxiliaryTerm dom cod middle arg))) →
      HeldFixedArgHops C X W s raw body α Γ ctx dom cod arg middle next →
      HeldFixedArgHops C X W s raw body α Γ ctx dom cod arg fn next

def ExactOpenCoverThinFinitePath : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx cod src dst : OTerm α),
    HeldHops C X W s raw body α Γ ctx cod src dst →
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst))

def ExactOpenCoverCombinedRestrictedFinitePath : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (root other : Program 3) (X : Program 2)
    (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let raw := typedRaw5 root other W P.V
    HeldFixedArgHops P.cover X W s raw body α Γ ctx dom cod arg fn next →
    Nonempty (Derivation body Γ (suppliedPath P.cover X W s raw ctx cod
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod next arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathTargets
