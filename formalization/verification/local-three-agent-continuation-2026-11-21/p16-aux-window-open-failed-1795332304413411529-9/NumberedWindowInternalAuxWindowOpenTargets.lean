module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)

abbrev intrinsicGraph {α : Type} (F : Program 2) (out ctx raw : OTerm α) :=
  programGraph F out ![ctx,raw]

abbrev windowGraph {α : Type} (W : Program 3) (ctx ty raw : OTerm α) :=
  programGraph W (suc z) ![ctx,ty,raw]

abbrev contextTable {α : Type} (R : Program 4) (out key ctx : OTerm α) :=
  programGraph (scratchTable (constantZero 2) R) out ![key,ctx,z]

abbrev contextRow {α : Type} (R : Program 4) (out key ctx : OTerm α) :=
  programGraph (scratchRow (constantZero 2) R) out ![key,ctx,z]

abbrev contextStep {α : Type} (R : Program 4) (out key tab ctx : OTerm α) :=
  programGraph R out ![key,tab,ctx,z]

def ExactOpenIntrinsicQuery : Prop :=
  ∀ (F : Program 2) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty raw : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (intrinsicQuery F) ctx ty raw)) ↔
    Nonempty (Derivation body Γ (intrinsicGraph F (suc ty) ctx raw))

def ExactOpenContextMemoSuccessor : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out key old ctx : OTerm α),
    Nonempty (Derivation body Γ (contextTable R old key ctx)) →
    Nonempty (Derivation body Γ (contextStep R out key old ctx)) →
    Nonempty (Derivation body Γ (contextRow R out (suc key) ctx))

/-- Both children are accepted by the same actual selected packed query,
in the same open context. The two literal original type guards are explicit. -/
def ExactOpenAuxWindow : Prop :=
  ∀ (base : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
      (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    let W := intrinsicQuery (selectedIntrinsic (windowUpdate base T))
    let premises := (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
      (windowGraph W ctx (rawCons dom cod) fn ⊓ windowGraph W ctx dom arg)
    Nonempty (Derivation body Γ (premises.imp (windowGraph W ctx cod (auxiliaryTerm dom cod fn arg))))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
