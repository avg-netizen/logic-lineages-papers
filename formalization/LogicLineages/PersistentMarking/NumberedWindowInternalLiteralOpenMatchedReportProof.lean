module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)

open ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel sucSubst zRelabel zSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Subst unarySubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename windowSubst)

def reported (L : Program 3) {α : Type} (ctx ty seed value : OTerm α) : Formula α :=
  programGraph L (suc value) ![ctx,ty,seed]

open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (numeralSubst programSubst)

structure MatchContext where
  types : Program 1
  cv : Program 1
  tv : Program 1
  finite : List Nat
  window : Program 3

def typedFormation (K : MatchContext) {α : Type} (ctx dom cod arg : OTerm α) : Formula α :=
  (unary K.types (suc z) dom ⊓ unary K.types (suc z) cod) ⊓
    (windowAt K.window ctx dom arg ⊓
      (unary K.cv (suc z) ctx ⊓ (unary K.tv (suc z) cod ⊓ literalMembership K.finite cod)))

theorem membershipRename {α β : Type} (codes : List Nat) (x : OTerm α) (j : α → β) :
    (literalMembership codes x).relabel j = literalMembership codes (x.relabel j) := by
  simp only [literalMembership,graphRename,numeralRename]

theorem membershipSubst {α β : Type} (codes : List Nat) (x : OTerm α) (ts : α → OTerm β) :
    (literalMembership codes x).subst (fun a => emb (ts a)) = literalMembership codes (x.subst ts) := by
  unfold literalMembership memberGraph
  rw [programSubst,sucSubst,zSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact numeralSubst _ _
  · obtain rfl := Fin.eq_zero j
    rfl

theorem reportedRename {α β : Type} (L : Program 3) (ctx ty q v : OTerm α) (j : α → β) :
    (reported L ctx ty q v).relabel j = reported L (ctx.relabel j) (ty.relabel j) (q.relabel j) (v.relabel j) := by
  simp only [reported,programRename,sucRelabel,tripleInputsRename]

theorem reportedSubst {α β : Type} (L : Program 3) (ctx ty q v : OTerm α) (ts : α → OTerm β) :
    (reported L ctx ty q v).subst (fun a => emb (ts a)) = reported L (ctx.subst ts) (ty.subst ts) (q.subst ts) (v.subst ts) := by
  simp only [reported,graph3Subst,sucSubst]

theorem typedFormationRename {α β : Type} (K : MatchContext) (ctx dom cod arg : OTerm α) (j : α → β) :
    (typedFormation K ctx dom cod arg).relabel j =
      typedFormation K (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) := by
  simp only [typedFormation,conjunctionRename,unaryRename,windowRename,sucRelabel,zRelabel,membershipRename]

theorem typedFormationSubst {α β : Type} (K : MatchContext) (ctx dom cod arg : OTerm α) (ts : α → OTerm β) :
    (typedFormation K ctx dom cod arg).subst (fun a => emb (ts a)) =
      typedFormation K (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) := by
  simp only [typedFormation,conjunctionSubst,unarySubst,windowSubst,sucSubst,zSubst,membershipSubst]

#print axioms reportedRename
#print axioms reportedSubst
#print axioms typedFormationRename
#print axioms typedFormationSubst

def pulled {α : Type} (L : Program 3) (raw : Program 5)
    (ctx cod parent target : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let earlier : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (reported L (ctx.relabel j) (cod.relabel j) (parent.relabel j) earlier ⊓
    supplied raw (L) (ctx.relabel j) (cod.relabel j) earlier (target.relabel j))

/-- The actual checked hop can start and finish at representatives different
from its two raw terms. A later application result determines the destination
class. Both an earlier result and its positive reduction witness are produced. -/
def MatchedCallsAt (K : MatchContext) (L : Program 3) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next q child r value : OTerm α),
    let least := L
    let input := typedFormation K ctx dom cod arg ⊓ (actualCalls raw least ctx (rawCons dom cod) fn next q child r ⊓
      reported L ctx cod (auxiliaryTerm dom cod next arg) value)
    Nonempty (Derivation body Γ (input.imp (pulled L raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
