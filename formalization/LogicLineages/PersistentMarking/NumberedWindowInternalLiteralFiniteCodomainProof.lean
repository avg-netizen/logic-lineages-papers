module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeBitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowProbeCode (code)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalLiteralTypeBitProof (exact_LiteralTypeBitArrow)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes D)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypeMembershipProof
  (exact_FiniteProgramImageTransfer exact_FiniteActualTypeGuard exact_FiniteProgramGuardTransfer)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem validProbeCode (p : ProbeTy) : typeBit (code p) = true := by
  induction p with
  | ground => rfl
  | arrow d c hd hc =>
    change typeBit (arrow (code d) (code c)) = true
    rw [exact_LiteralTypeBitArrow,hd,hc]
    rfl

theorem validFiniteCodes (P : List ProbeTy) (t : Nat) (mem : t ∈ finiteCodes P) : typeBit t = true := by
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp mem
  exact validProbeCode p

private theorem tailOfCodes (P : List ProbeTy) (closed : ChildClosed P) (t : Nat)
    (mem : t ∈ finiteCodes P) : evaluate cellTail (t ::ᵥ nil) ∈ finiteCodes P := by
  obtain ⟨p,inP,rfl⟩ := List.mem_map.mp mem
  cases p with
  | ground =>
    change evaluate cellTail (0 ::ᵥ nil) ∈ finiteCodes P
    have nilTail : evaluate cellTail (0 ::ᵥ nil) = 0 := rfl
    rw [nilTail]
    exact List.mem_map.mpr ⟨.ground,inP,rfl⟩
  | arrow d c =>
    have equation : run cellTail (code (.arrow d c)) = code c :=
      (headTailOfCell (cellAt (code d) (code c))).2
    change run cellTail (code (.arrow d c)) ∈ finiteCodes P
    rw [equation]
    exact List.mem_map.mpr ⟨c,closed d c inP,rfl⟩

/-- At an actual arrow in the selected finite type list, read the same
physical tail selector. Finite numerical image proofs determine all
literal cases individually, so the open codomain is admitted without
interpreting an arbitrary proof of a numeral graph. -/
theorem exact_OpenLiteralFiniteCodomain (P : List ProbeTy) (closed : ChildClosed P)
    (dom cod : OTerm α)
    (arrowIn : D B Γ (literalMembership (finiteCodes P) (rawCons dom cod))) :
    D B Γ (literalMembership (finiteCodes P) cod) := by
  obtain ⟨row⟩ := canonicalCell (body := B) (Γ := Γ) dom cod
  exact exact_FiniteProgramImageTransfer cellTail (finiteCodes P) (finiteCodes P)
    (tailOfCodes P closed) B α Γ (rawCons dom cod) cod arrowIn
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight row)⟩

theorem exact_OpenLiteralFiniteTypeTests (s : Settings) (P : List ProbeTy) (tv T : Program 1)
    (actual : ActualTypeGuard tv) (cal : TypeGuardCalibrated s T)
    (included : ∀ t ∈ finiteCodes P, t ∈ s.window.1) (t : OTerm α)
    (mem : D B Γ (literalMembership (finiteCodes P) t)) :
    D B Γ (unary tv (suc z) t) ∧ D B Γ (unary T (suc z) t) := by
  refine ⟨exact_FiniteActualTypeGuard tv (finiteCodes P) actual (validFiniteCodes P) B α Γ t mem,?_⟩
  apply exact_FiniteProgramGuardTransfer T (finiteCodes P) _ B α Γ t mem
  intro k hk
  change run T k = 1
  rw [cal k]
  simp [typeGuard,validFiniteCodes P k hk,included k hk]

#print axioms exact_OpenLiteralFiniteCodomain
#print axioms exact_OpenLiteralFiniteTypeTests
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
