module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase namedGrammarWindow)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck SlotReports)

/-- On [original lexical context, original raw key], test the bound slot
at original field 1, requiring the live cell's type to be original field 0. -/
def lexicalGuard : Program 2 :=
  .composition slotCheck ![onRaw (field 1),.projection 0,onRaw (field 0)]

def lexicalBoundBase (B : Program 2) : Program 2 :=
  branch (onRaw (header 1 2)) B (branch (normalize lexicalGuard) (constantZero 2) B)

abbrev lexicalNamedWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  namedGrammarWindow s (lexicalBoundBase B) T

def ExactCoverLexicalBoundBase : Prop :=
  ∀ (s : Settings) (B : Program 2), IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (lexicalBoundBase B)

def ExactCoverLexicalNamedWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (lexicalNamedWindow s B T)

def ExactOpenCoverLexicalBoundBaseSlot : Prop :=
  ∀ (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ
      (programGraph (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) (suc result)
        ![ctx,namedTerm 1 ty i])) →
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty]))

def ExactOpenCoverLexicalBoundWindowSlot : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (lexicalNamedWindow s B T) ctx result (namedTerm 1 ty i))) →
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty]))

def ExactOpenCoverLexicalBoundWindowReports : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty i result : OTerm α) (Q : Formula α),
    Nonempty (Derivation body Γ (windowGraph (lexicalNamedWindow s B T) ctx result (namedTerm 1 ty i))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (rest : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      SlotReports body Δ (i.relabel j) (ctx.relabel j) (ty.relabel j) rest →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets
