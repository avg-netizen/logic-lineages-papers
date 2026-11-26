module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitRejectOpenProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawRunRootTapeProof (rejectLeft)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (singletonSyntax singletonAtomicDispatch)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonShiftHitMachineProof
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
open NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
  (exact_OpenReplacementTape exact_OpenShiftHitFallback)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- On the replacement tape `[a,d,a]` a rejected replacement makes the
actual two-slot syntax guard return zero: its first conjunct already
fails, so the second is not consulted. -/
theorem exact_OpenShiftHitSyntaxReject (V : Program 1) (a d : OTerm α)
    (bad : D B Γ (unary V z a)) :
    D B Γ (programGraph (singletonSyntax V) z ![a,d,a]) :=
  rejectLeft (onRaw V 0) (onRaw V 2) ![a,d,a] (onTape V 0 z ![a,d,a] bad)

/-- Inverse of the replacement-tape read: the three projections are
functional, so a graph of the composite is a graph of the inner program
on `[a,d,a]`. -/
theorem exact_OpenReplacementTapeRecover (P : Program 3) (a d out : OTerm α)
    (held : D B Γ (programGraph
      (.composition P (![.projection 0,.projection 1,.projection 0] : Fin 3 → Program 2) : Program 2)
      out ![a,d])) :
    D B Γ (programGraph P out ![a,d,a]) := by
  apply compositionRecover P (![.projection 0,.projection 1,.projection 0] : Fin 3 → Program 2)
    out ![a,d] ![a,d,a] held
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue (0 : Fin 2) ![a,d]
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact projectionValue (1 : Fin 2) ![a,d]
    · obtain rfl := Fin.eq_zero l
      exact projectionValue (0 : Fin 2) ![a,d]

/-- Inverse of the fallback slot. -/
theorem exact_OpenShiftHitFallbackRecover (H : Program 2) (a d q out : OTerm α)
    (held : D B Γ (programGraph (shiftHitFallback H) out ![a,d,q])) :
    D B Γ (programGraph H out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,q]
  apply compositionRecover H (![.projection 0,.projection 1] : Fin 2 → Program 3) out xs ![a,d] held
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue (0 : Fin 3) xs
  · obtain rfl := Fin.eq_zero j
    exact projectionValue (1 : Fin 3) xs

/-- The bound front on a rejected replacement is its fallback. -/
theorem exact_OpenShiftHitBoundReject (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (bad : D B Γ (unary V z a))
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitBound V H) out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  have rejected : D B Γ (programGraph (singletonSyntax V) z xs) :=
    exact_OpenShiftHitSyntaxReject V a d bad
  have passed : D B Γ (programGraph (shiftHitFallback H) out xs) :=
    exact_OpenShiftHitFallback H a d a out h
  have dispatched : D B Γ (programGraph (shiftHitDispatch V H) out xs) :=
    zeroBranchIntro (singletonSyntax V) (shiftHitFallback H)
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out xs rejected passed
  exact exact_OpenReplacementTape (shiftHitDispatch V H) a d out dispatched

theorem exact_OpenShiftHitBoundRejectRecover (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (bad : D B Γ (unary V z a))
    (held : D B Γ (programGraph (shiftHitBound V H) out ![a,d])) :
    D B Γ (programGraph H out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  have rejected : D B Γ (programGraph (singletonSyntax V) z xs) :=
    exact_OpenShiftHitSyntaxReject V a d bad
  have dispatched : D B Γ (programGraph (shiftHitDispatch V H) out xs) :=
    exact_OpenReplacementTapeRecover (shiftHitDispatch V H) a d out held
  have passed : D B Γ (programGraph (shiftHitFallback H) out xs) :=
    zeroBranchElim (singletonSyntax V) (shiftHitFallback H)
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out xs
      rejected dispatched
  exact exact_OpenShiftHitFallbackRecover H a d a out passed

/-- The atom front on a rejected replacement is its fallback. -/
theorem exact_OpenShiftHitAtomsReject (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (bad : D B Γ (unary V z a))
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitAtoms V H) out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  have rejected : D B Γ (programGraph (singletonSyntax V) z xs) :=
    exact_OpenShiftHitSyntaxReject V a d bad
  have passed : D B Γ (programGraph (shiftHitFallback H) out xs) :=
    exact_OpenShiftHitFallback H a d a out h
  have dispatched : D B Γ (programGraph (shiftAtomDispatch V H) out xs) :=
    zeroBranchIntro (singletonSyntax V) (shiftHitFallback H)
      (singletonAtomicDispatch (shiftHitFallback H)) out xs rejected passed
  exact exact_OpenReplacementTape (shiftAtomDispatch V H) a d out dispatched

theorem exact_OpenShiftHitAtomsRejectRecover (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (bad : D B Γ (unary V z a))
    (held : D B Γ (programGraph (shiftHitAtoms V H) out ![a,d])) :
    D B Γ (programGraph H out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  have rejected : D B Γ (programGraph (singletonSyntax V) z xs) :=
    exact_OpenShiftHitSyntaxReject V a d bad
  have dispatched : D B Γ (programGraph (shiftAtomDispatch V H) out xs) :=
    exact_OpenReplacementTapeRecover (shiftAtomDispatch V H) a d out held
  have passed : D B Γ (programGraph (shiftHitFallback H) out xs) :=
    zeroBranchElim (singletonSyntax V) (shiftHitFallback H)
      (singletonAtomicDispatch (shiftHitFallback H)) out xs rejected dispatched
  exact exact_OpenShiftHitFallbackRecover H a d a out passed

/-- Reject boundary of the installed front. When the actual syntax graph
rejects a symbolic replacement, the same `shiftHitLiterals V H` returns
exactly the supplied output of `H`: both guards, both dispatches and all
five tape projections are derived in the object calculus. -/
theorem exact_OpenShiftHitLiteralsReject (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (bad : D B Γ (unary V z a))
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitLiterals V H) out ![a,d]) :=
  exact_OpenShiftHitBoundReject V (shiftHitAtoms V H) a d out bad
    (exact_OpenShiftHitAtomsReject V H a d out bad h)

/-- Inversion by the branch and composition eliminators: on a rejected
replacement every output of the installed front is an output of `H`. No
graph of `H` is assumed. -/
theorem exact_OpenShiftHitLiteralsRejectRecover (V : Program 1) (H : Program 2)
    (a d out : OTerm α) (bad : D B Γ (unary V z a))
    (held : D B Γ (programGraph (shiftHitLiterals V H) out ![a,d])) :
    D B Γ (programGraph H out ![a,d]) :=
  exact_OpenShiftHitAtomsRejectRecover V H a d out bad
    (exact_OpenShiftHitBoundRejectRecover V (shiftHitAtoms V H) a d out bad held)

/-- Functional form: with a specified `H` output, any output of the
installed front on a rejected replacement equals it. -/
theorem exact_OpenShiftHitLiteralsRejectUnique (V : Program 1) (H : Program 2)
    (a d out r : OTerm α) (bad : D B Γ (unary V z a))
    (h : D B Γ (programGraph H out ![a,d]))
    (held : D B Γ (programGraph (shiftHitLiterals V H) r ![a,d])) :
    D B Γ (eqn r out) :=
  valueUnique (shiftHitLiterals V H) r out ![a,d] held
    (exact_OpenShiftHitLiteralsReject V H a d out bad h)

#print axioms exact_OpenShiftHitSyntaxReject
#print axioms exact_OpenReplacementTapeRecover
#print axioms exact_OpenShiftHitFallbackRecover
#print axioms exact_OpenShiftHitBoundReject
#print axioms exact_OpenShiftHitBoundRejectRecover
#print axioms exact_OpenShiftHitAtomsReject
#print axioms exact_OpenShiftHitAtomsRejectRecover
#print axioms exact_OpenShiftHitLiteralsReject
#print axioms exact_OpenShiftHitLiteralsRejectRecover
#print axioms exact_OpenShiftHitLiteralsRejectUnique
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitRejectOpenProof
