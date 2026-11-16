module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInputs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GraphInterface LiteralRawMP.ConstructorSupportProof CurrentRecursionBaseProgram.GraphPrimitives
variable {n ctx : Nat} (p : Program n) (v : List.Vector (Term ctx) 7) (ntag : Nat)
 (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
include hn
theorem quoted (i : Fin 7) : Computes p (quotedNumeral i) v (numeral ntag (v.get i)) :=
 unary p v LiteralNumeralPrefix.numeralCode ntag hn _ _ (projection p v i)

theorem inner (i : Fin 4) : Computes p (innerArguments i) v ((innerInputs ntag v).get i) := by
 cases i using Fin.cases with
 | zero => exact quoted p v ntag hn 2
 | succ i => cases i using Fin.cases with
  | zero => exact quoted p v ntag hn 1
  | succ i => cases i using Fin.cases with
   | zero => exact projection p v 4
   | succ i => cases i using Fin.cases with
    | zero => exact quoted p v ntag hn 0
    | succ i => exact Fin.elim0 i

theorem outer (i : Fin 3) : Computes p (outerArguments i) v ((outerInputs ntag v).get i) := by
 cases i using Fin.cases with
 | zero => exact quoted p v ntag hn 1
 | succ i => cases i using Fin.cases with
  | zero => exact projection p v 4
  | succ i => cases i using Fin.cases with
   | zero => exact quoted p v ntag hn 0
   | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInputs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInputs
