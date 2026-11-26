module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInputs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

theorem quoted (i : Fin 7) (v : List.Vector Nat 7) :
 evaluate (quotedNumeral i) v = Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (n := 0) (v.get i))) := by
 change evaluate LiteralNumeralPrefix.numeralCode (v.get i ::ᵥ nil) = _
 exact LiteralNumeralPrefix.StatementChecks.exactNative (v.get i)

def innerTerms (v : List.Vector Nat 7) (u : Term 0) : Fin 4 → Term 0 :=
 Fin.cases (Term.numeral (v.get 2)) (Fin.cases (Term.numeral (v.get 1)) (Fin.cases u (Fin.cases (Term.numeral (v.get 0)) Fin.elim0)))
def outerTerms (v : List.Vector Nat 7) (u : Term 0) : Fin 3 → Term 0 :=
 Fin.cases (Term.numeral (v.get 1)) (Fin.cases u (Fin.cases (Term.numeral (v.get 0)) Fin.elim0))

theorem inner (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 (List.Vector.ofFn (fun i => evaluate (innerArguments i) v)) = FixedFormulaSubstitution.rawInputs (innerTerms v u) := by
 ext i
 simp only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs]
 cases i using Fin.cases with
 | zero => exact quoted 2 v
 | succ i => cases i using Fin.cases with
  | zero => exact quoted 1 v
  | succ i => cases i using Fin.cases with
   | zero => exact hu
   | succ i => cases i using Fin.cases with
    | zero => exact quoted 0 v
    | succ i => exact Fin.elim0 i

theorem outer (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 (List.Vector.ofFn (fun i => evaluate (outerArguments i) v)) = FixedFormulaSubstitution.rawInputs (outerTerms v u) := by
 ext i
 simp only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs]
 cases i using Fin.cases with
 | zero => exact quoted 1 v
 | succ i => cases i using Fin.cases with
  | zero => exact hu
  | succ i => cases i using Fin.cases with
   | zero => exact quoted 0 v
   | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInputs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInputs
