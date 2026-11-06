module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotient
open Source NumberedUniformPackedDecoding NumberedQuotientPathCertificates

abbrev Parameters (n : Nat) := (ContextUniformPrimary.Window n × List Ty) × (Fin n → Fin n → Bool)

/-- The ORIGINAL three-number edge certificate, decoded with the joint
ambient context and the exactly calibrated raw canonical representative. -/
def rawEdgeTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y certificate : Nat) : Bool :=
  let source := (Nat.unpair certificate).1
  let target := (Nat.unpair (Nat.unpair certificate).2).1
  let step := (Nat.unpair (Nat.unpair certificate).2).2
  match rawUniverseDecode n arity symbols S Gamma source,rawPackedDecode n arity Gamma target with
  | some q,some r => NumberedNumericStep.numericStepTest n arity symbols S Gamma table source target step &&
      decide (ContextUniformPrimary.representative arity symbols S Gamma q=x ∧
        ContextUniformPrimary.representative arity symbols S Gamma r=y)
  | _,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotient
