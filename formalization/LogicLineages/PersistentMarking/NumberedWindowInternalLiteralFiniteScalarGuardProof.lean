module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowTypedProbe (typed)
open NumberedWindowProbeCode (code)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy TypeSupport)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (literalFields)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof (viewDecoded)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (φ : Formula α) :=
  Nonempty (Derivation B Γ φ)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Use precisely the original finite list. If ground occurs, the
literal tail at that code is ground again; otherwise no extra type
needs to be inserted or admitted. -/
def finiteCodes (P : List ProbeTy) : List Nat := P.map code

def storedTypeIn (codes : List Nat) : Program 1 := .composition scratchMember
  (Fin.cons (literal 1 (Encodable.encode codes)) (Fin.cons rawResult Fin.elim0))

def finiteScalar (i : Program 1) (codes : List Nat) : Program 1 :=
  conjunction i (storedTypeIn codes)

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons a bs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem actualTypeListed (s : Settings) (P : List ProbeTy) (q : Nat)
    (support : TypeSupport s P) (accepted : scalar s q = true) :
    run rawResult q ∈ finiteCodes P := by
  cases h : addressView q with
  | none => simp [scalar,h] at accepted
  | some r =>
    obtain ⟨g,t,k⟩ := r
    have ht : typed s t q = true := by simp [typed,accepted,h]
    obtain ⟨τ,listed,same⟩ := support t q ht
    obtain ⟨decoded,_,value,_⟩ := viewDecoded h
    have chosen : run rawResult q = t := by
      rw [decoded.nameEq,(literalFields decoded.ctx decoded.ty decoded.classCode).2.1,value]
    rw [chosen,same]
    exact List.mem_map.mpr ⟨τ,listed,rfl⟩

/-- The actual finite type report is redundant numerically for the
original scalar but is a real guard in the new program. Every raw
input, including malformed addresses, retains its original result. -/
theorem exact_LiteralFiniteScalarCalibration (s : Settings) (i : Program 1) (P : List ProbeTy)
    (support : TypeSupport s P) (cal : ActualScalarCalibration s i) :
    ActualScalarCalibration s (finiteScalar i (finiteCodes P)) := by
  intro q
  rw [finiteScalar,conjunctionEvaluation,cal q]
  by_cases good : scalar s q = true
  · have listed := actualTypeListed s P q support good
    have guard : evaluate (storedTypeIn (finiteCodes P)) (q ::ᵥ nil) = 1 := by
      rw [storedTypeIn,compositeTwo,literalEvaluation,exact_AllInputScratchMembership,
        listCode,numbersRoundTrip]
      change ((finiteCodes P).any fun v => v == run rawResult q).toNat = 1
      have h : (finiteCodes P).any (fun v => v == run rawResult q) = true :=
        List.any_eq_true.mpr ⟨run rawResult q,listed,by simp⟩
      rw [h]
      rfl
    simp [good,guard]
  · cases h : scalar s q with
    | false => simp [h]
    | true => exact (good h).elim

private theorem typeReport (codes : List Nat) (q ty : OTerm α)
    (field : D B Γ (unary rawResult ty q))
    (held : D B Γ (unary (storedTypeIn codes) (suc z) q)) :
    D B Γ (literalMembership codes ty) := by
  let p := literal 1 (Encodable.encode codes)
  let k : OTerm α := numeral (Encodable.encode codes)
  exact compositionRecover scratchMember (Fin.cons p (Fin.cons rawResult Fin.elim0))
    (suc z) ![q] ![k,ty] held (fun n =>
      Fin.cases (literalGraph (Encodable.encode codes) ![q]) (Fin.cases field (fun r => Fin.elim0 r)) n)

/-- Recover the old scalar and the literal finite type membership on
the actual reported type in the same open body. -/
theorem exact_OpenLiteralFiniteScalar (i : Program 1) (codes : List Nat) (q ty : OTerm α)
    (field : D B Γ (unary rawResult ty q))
    (h : D B Γ (unary (finiteScalar i codes) (suc z) q)) :
    D B Γ (unary i (suc z) q) ∧ D B Γ (literalMembership codes ty) := by
  obtain ⟨both⟩ := conjunctionRecover i (storedTypeIn codes) ![q] h
  exact ⟨⟨Derivation.conjunctionLeft both⟩,typeReport codes q ty field ⟨Derivation.conjunctionRight both⟩⟩

theorem exact_MakeLiteralFiniteScalar (i : Program 1) (codes : List Nat) (q ty : OTerm α)
    (field : D B Γ (unary rawResult ty q))
    (scalar : D B Γ (unary i (suc z) q)) (member : D B Γ (literalMembership codes ty)) :
    D B Γ (unary (finiteScalar i codes) (suc z) q) := by
  have guard : D B Γ (unary (storedTypeIn codes) (suc z) q) :=
    compositionValue scratchMember
      (Fin.cons (literal 1 (Encodable.encode codes)) (Fin.cons rawResult Fin.elim0))
      (suc z) ![q] ![numeral (Encodable.encode codes),ty] member
      (fun n => Fin.cases (literalGraph (Encodable.encode codes) ![q])
        (Fin.cases field (fun r => Fin.elim0 r)) n)
  exact conjunctionAccept i (storedTypeIn codes) ![q] scalar guard

#print axioms exact_LiteralFiniteScalarCalibration
#print axioms exact_OpenLiteralFiniteScalar
#print axioms exact_MakeLiteralFiniteScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
