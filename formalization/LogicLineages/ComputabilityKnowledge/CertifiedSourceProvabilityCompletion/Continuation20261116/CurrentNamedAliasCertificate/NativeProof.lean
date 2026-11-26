module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.NativeProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowFormulaSubstitution CurrentRecursionBaseProgram.NativePrimitives
open CurrentRecursionBaseProgram HistoryRuleSuffix.NativeProof

theorem rawEval (v : List.Vector Nat 2) (i : Fin 2) :
 evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (n := 0) (v.get i))) := by
 change evaluate LiteralNumeralPrefix.numeralCode (v.get i ::ᵥ nil) = _
 exact LiteralNumeralPrefix.StatementChecks.exactNative (v.get i)

theorem seedEval (v : List.Vector Nat 2) :
 evaluate CurrentNamedAliasCertificate.seedProgram v = PrescribedSourceAxiomSpecialization.seed matrix := by
 apply SeedNativeProof.axiomEval
 exact constantEval _ _ v

theorem tailEval (v : List.Vector Nat 2) :
 evaluate tailProgram v = PrescribedRuntimeSpecialization.produce (.all matrix)
  (fun _ => Term.numeral (v.get 1)) (PrescribedSourceAxiomSpecialization.seed matrix) := by
 have hraw : ∀ i : Fin 1, evaluate (raw 1) v = Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (n := 0) (v.get 1))) := fun _ => rawEval v 1
 have hq := quoteEval (.all matrix) (fun _ => raw 1) v (fun _ => Term.numeral (v.get 1)) hraw
 have hh := headQuoteEval (.all matrix) Fin.elim0 v Fin.elim0 (fun i => Fin.elim0 i)
 change evaluate (mp _ _ _) v = _
 rw [mpEval _ _ _ v _ hq,allInstanceEval _ _ v _ _ hh (rawEval v 1),seedEval]
 rfl

theorem exactNative : Targets.Native := by
 intro r s
 let v : List.Vector Nat 2 := r ::ᵥ s ::ᵥ nil
 let sigma : Fin 2 → Term 0 := Fin.cases (Term.numeral r) (Fin.cases (Term.numeral s) Fin.elim0)
 have hr : ∀ i, evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma i)) := by
  intro i
  cases i using Fin.cases with
  | zero => exact rawEval v 0
  | succ i => cases i using Fin.cases with
   | zero => exact rawEval v 1
   | succ i => exact Fin.elim0 i
 have hq := quoteEval matrix raw v sigma hr
 have hh := headQuoteEval matrix (fun _ => raw 1) v (fun _ => Term.numeral s) (fun _ => rawEval v 1)
 change evaluate (mp _ _ _) v = _
 rw [mpEval _ _ _ v _ hq,allInstanceEval _ _ v _ _ hh (rawEval v 0),tailEval]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.NativeProof
