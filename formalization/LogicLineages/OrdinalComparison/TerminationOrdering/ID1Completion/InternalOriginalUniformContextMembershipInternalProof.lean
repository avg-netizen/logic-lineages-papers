module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformContextMembership InternalOriginalUniformContextMembershipTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalTypedCarrierSupportProof (atValue)
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Pair inversion supplies the actual left selector used by the literal
normalized AST. Neither the Gamma code nor the context is decoded internally. -/
theorem sliceRecover (member : Program 2)
    (out typ parameter context gammaCode : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hm : Nonempty (Derivation body Gamma
      (graph2 (normalizedMember member) out typ parameter))) :
    Nonempty (Derivation body Gamma (graph2 (contextMember member) out typ context)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons typ (Fin.cons parameter Fin.elim0)
  have hl := atValue InternalUnpair.left 1 context xs (pairLeft parameter context gammaCode hp)
  exact binaryRecover (contextMember member) (.projection 0) (leftOf (.projection 1))
    out typ context xs hm (projectionValue 0 xs) hl

/-- The reverse graph implication uses the same original pairing graph and
the same two finite projections. Output values are unrestricted. -/
theorem sliceAccept (member : Program 2)
    (out typ parameter context gammaCode : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hm : Nonempty (Derivation body Gamma
      (graph2 (contextMember member) out typ context))) :
    Nonempty (Derivation body Gamma (graph2 (normalizedMember member) out typ parameter)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons typ (Fin.cons parameter Fin.elim0)
  have hl := atValue InternalUnpair.left 1 context xs (pairLeft parameter context gammaCode hp)
  exact binaryValue (contextMember member) (.projection 0) (leftOf (.projection 1))
    out typ context xs hm (projectionValue 0 xs) hl

theorem actualOriginalUniformMembershipSlice : ActualOriginalUniformMembershipSlice := by
  intro member body α Delta out typ parameter context gammaCode
  let P := graph2 InternalPairing.pairing parameter context gammaCode
  let N := graph2 (normalizedMember member) out typ parameter
  let C := graph2 (contextMember member) out typ context
  obtain ⟨hf⟩ := sliceRecover (body := body) (Gamma := N :: P :: Delta)
    member out typ parameter context gammaCode
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := sliceAccept (body := body) (Gamma := C :: P :: Delta)
    member out typ parameter context gammaCode
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
      (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
