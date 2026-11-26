module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GuardSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GraphInterface
variable {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (ntag : Nat) (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (G : List (Formula ctx))

include hn
theorem numeralValid (count : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (numeral ntag count))) :=
 PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current ntag hn G count

theorem inner (v : List.Vector (Term ctx) 7)
 (hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag (v.get 4))) :
 ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((innerInputs ntag v).get i))) := by
 intro i
 cases i using Fin.cases with
 | zero => exact numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 2)
 | succ i => cases i using Fin.cases with
  | zero => exact numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 1)
  | succ i => cases i using Fin.cases with
   | zero => exact ⟨hu⟩
   | succ i => cases i using Fin.cases with
    | zero => exact numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 0)
    | succ i => exact Fin.elim0 i

theorem outer (v : List.Vector (Term ctx) 7)
 (hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag (v.get 4))) :
 ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((outerInputs ntag v).get i))) := by
 intro i
 cases i using Fin.cases with
 | zero => exact numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 1)
 | succ i => cases i using Fin.cases with
  | zero => exact ⟨hu⟩
  | succ i => cases i using Fin.cases with
   | zero => exact numeralValid p f lhs rhs t old ar x I ntag hn G (v.get 0)
   | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GuardSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GuardSupport
