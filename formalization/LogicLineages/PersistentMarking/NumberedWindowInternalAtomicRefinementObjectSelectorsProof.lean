module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementObjectTargets
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph unaryInput)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal compareNumbers bothOne)
open NumberedWindowInternalFreshProbeParsedEmitter (addressTag addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood field)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem inverseEq (x y : OTerm α) (e : Nonempty (Derivation body Γ (equal x y))) :
    Nonempty (Derivation body Γ (equal y x)) := by
  rw [equalEqn] at e ⊢
  obtain ⟨h⟩ := e
  exact ⟨symm h⟩

theorem literalAddress (c t k : OTerm α) :
    Nonempty (Derivation body Γ (unary addressGood (suc z) (addressTerm c t k))) ∧
    Nonempty (Derivation body Γ (unary rawContext c (addressTerm c t k))) ∧
    Nonempty (Derivation body Γ (unary rawResult t (addressTerm c t k))) ∧
    Nonempty (Derivation body Γ (unary rawLeast k (addressTerm c t k))) := by
  let n := addressTerm c t k
  have code : Nonempty (Derivation body Γ (unary addressTag (numeral 3) n)) :=
    literalGraph 3 ![n]
  have selected := packedNode addressTag (numeral 3) [c,t,k] code
  exact ⟨selected.1,selected.2.1,selected.2.2.1,selected.2.2.2.1⟩

theorem literalAtom (tag : Nat) (c t : OTerm α) (tail : List (OTerm α)) :
    let payload := rawCons (numeral tag) (packedBody (t::tail))
    let x := addressTerm c t payload
    Nonempty (Derivation body Γ (unary (atomSource tag (t::tail).length) (suc z) x)) ∧
    Nonempty (Derivation body Γ (sourceFields x c t)) := by
  dsimp only
  let payload := rawCons (numeral tag) (packedBody (t::tail))
  let x := addressTerm c t payload
  let n := (t::tail).length
  let code := literal 1 tag
  let inner := nodeGood code n
  let check := applyUnary inner rawLeast
  obtain ⟨shell,hc,ht,hk⟩ := literalAddress (body := body) (Γ := Γ) c t payload
  have literalTag : Nonempty (Derivation body Γ (unary code (numeral tag) payload)) :=
    literalGraph tag ![payload]
  have seen := packedNode code (numeral tag) (t::tail) literalTag
  have termGood : Nonempty (Derivation body Γ (unary check (suc z) x)) :=
    makeUnary inner rawLeast (suc z) x payload seen.1 hk
  have rawTy : Nonempty (Derivation body Γ (unary (field 0) t payload)) := seen.2.1
  have sameStored : Nonempty (Derivation body Γ (unary storedType t x)) :=
    makeUnary (field 0) rawLeast t x payload rawTy hk
  have ok : Nonempty (Derivation body Γ (unary storedTypeFits (suc z) x)) := by
    unfold storedTypeFits
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest
      (Fin.cons rawResult (Fin.cons storedType Fin.elim0)) (suc z) ![x] ![t,t] (equalitySelf t)
    intro i
    exact Fin.cases ht (Fin.cases sameStored (fun k => Fin.elim0 k)) i
  have checked : Nonempty (Derivation body Γ (unary (atomSource tag n) (suc z) x)) := by
    unfold atomSource
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept addressGood (ID1Completion.InternalAcceptance.conjunction check storedTypeFits)
      ![x] shell (conjunctionAccept check storedTypeFits ![x] termGood ok)
  obtain ⟨a⟩ := hc
  obtain ⟨b⟩ := ht
  exact ⟨checked,⟨Derivation.conjunctionIntroduction a b⟩⟩

section
attribute [local irreducible] programGraph

theorem toFree (x c t n : OTerm α)
    (e : Nonempty (Derivation body Γ (equal x (packedFreeTerm c t n)))) :
    Nonempty (Derivation body Γ
      (programGraph freeSource (numeral 1) ![x] ⊓ sourceFields x c t)) := by
  let atom := packedFreeTerm c t n
  have back := inverseEq x atom e
  have known := literalAtom (body := body) (Γ := Γ) 0 c t [n]
  have branch : Nonempty (Derivation body Γ (programGraph freeSource (suc z) ![atom])) := known.1
  have fields : Nonempty (Derivation body Γ (sourceFields atom c t)) := known.2
  obtain ⟨hg⟩ := unaryInput freeSource (suc z) atom x back branch
  obtain ⟨fs⟩ := fields
  obtain ⟨hc⟩ := unaryInput rawContext c atom x back ⟨Derivation.conjunctionLeft fs⟩
  obtain ⟨ht⟩ := unaryInput rawResult t atom x back ⟨Derivation.conjunctionRight fs⟩
  exact ⟨Derivation.conjunctionIntroduction hg (Derivation.conjunctionIntroduction hc ht)⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
