module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericShapeProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (packNode unpackNode pack unpack)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowAtomicRawStepFieldProof (nodePacked codeOfNode)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood addressTag)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)

theorem shape (q : Nat) : run addressGood q = 1 ↔ ∃ c t k, q = packedAddress c t k := by
  have value : run addressTag q = 3 := literalEvaluation 1 3 (q ::ᵥ nil)
  change run (nodeGood addressTag 3) q = 1 ↔ _
  rw [nodeArity addressTag 3 q 3 value]
  constructor
  · rintro ⟨fs,decoded,len⟩
    rcases fs with _ | ⟨c,_ | ⟨t,_ | ⟨k,_ | ⟨d,rest⟩⟩⟩⟩ <;> simp at len
    exact ⟨c,t,k,codeOfNode decoded⟩
  · rintro ⟨c,t,k,rfl⟩
    exact ⟨[c,t,k],nodePacked 3 [c,t,k],rfl⟩

theorem unpackContext {n : Nat} {Γ : List Nat} (h : contextView n = some Γ) :
    unpack n = some Γ := by
  unfold contextView at h
  cases hu : unpack n with
  | none => simp [hu] at h
  | some xs =>
    have parsed : (∀ x ∈ xs, typeBit x = true) ∧ xs = Γ := by
      simpa [hu] using h
    exact congrArg some parsed.2

theorem sameContext {c d : Nat} {Γ Δ : List Nat}
    (left : contextView c = some Γ) (right : contextView d = some Δ) :
    c = d ↔ Γ = Δ := by
  constructor
  · intro h
    exact Option.some.inj (left.symm.trans (by rw [h]; exact right))
  · intro h
    rw [packOfUnpack c (unpackContext left), packOfUnpack d (unpackContext right),h]

/-- The complete original `addressView` reports literal original raw
fields plus independently verified original context/result validity. -/
structure Decoded (q : Nat) where
  ctx : Nat
  ty : Nat
  classCode : Nat
  stack : List Nat
  nameEq : q = packedAddress ctx ty classCode
  contextOk : contextView ctx = some stack
  typeOk : typeBit ty = true

theorem decodedView {n : Nat} (d : Decoded n) :
    addressView n = some (d.stack,d.ty,d.classCode) := by
  calc
    addressView n = addressView (packedAddress d.ctx d.ty d.classCode) :=
      congrArg addressView d.nameEq
    _ = some (d.stack,d.ty,d.classCode) := by
      rw [addressView,packedAddress,nodePacked]
      simp [d.contextOk,d.typeOk]

theorem viewDecoded {n t k : Nat} {Γ : List Nat} (h : addressView n = some (Γ,t,k)) :
    ∃ d : Decoded n, d.stack = Γ ∧ d.ty = t ∧ d.classCode = k := by
  have good : ∃ c u b, unpackNode n = some (3,[c,u,b]) := by
    cases ns : unpackNode n with
    | none => simp [addressView,ns] at h
    | some tag =>
      rcases tag with ⟨x,fs⟩
      by_cases eq : x = 3
      · subst x
        rcases fs with _ | ⟨c,_ | ⟨u,_ | ⟨b,_ | ⟨d,rest⟩⟩⟩⟩ <;>
          try simp [addressView, ns] at h
        exact ⟨c,u,b,rfl⟩
      · have none : addressView n = none := by
          unfold addressView
          rw [ns]
          cases x with
          | zero => rfl
          | succ x =>
            cases x with
            | zero => rfl
            | succ x =>
              cases x with
              | zero => rfl
              | succ x =>
                cases x with
                | zero => exact (eq rfl).elim
                | succ x => rfl
        simp [none] at h
  obtain ⟨c,u,b,ns⟩ := good
  have code : n = packedAddress c u b := codeOfNode ns
  cases hc : contextView c with
  | none => simp [addressView,ns,hc] at h
  | some stack =>
    by_cases ht : typeBit u = true
    · have d : Decoded n := ⟨c,u,b,stack,code,hc,ht⟩
      have he := Option.some.inj ((decodedView d).symm.trans h)
      exact ⟨d,congrArg Prod.fst he,congrArg (fun v => v.2.1) he,
        congrArg (fun v => v.2.2) he⟩
    · simp [addressView,ns,hc,ht] at h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericShapeProof
