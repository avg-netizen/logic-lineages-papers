module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentation
open Source NumberedRewriteReduction NumberedMultisetCertificate

/-- A product presentation of the original certificate, retaining every occurrence
and every literal removed-index/mark-label witness in its original order. -/
def certificateEquiv (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    MultisetCertificate n arity Gamma ≃
      List (Packed (Fin n) arity Gamma) × List (Packed (Fin n) arity Gamma) ×
        List (Packed (Fin n) arity Gamma) × List MarkWitness where
  toFun c := (c.kept,c.removed,c.inserted,c.witnesses)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨kept,removed,inserted,witnesses⟩; rfl

instance certificatePrimcodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primcodable (MultisetCertificate n arity Gamma) :=
  Primcodable.ofEquiv _ (certificateEquiv n arity Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentation
