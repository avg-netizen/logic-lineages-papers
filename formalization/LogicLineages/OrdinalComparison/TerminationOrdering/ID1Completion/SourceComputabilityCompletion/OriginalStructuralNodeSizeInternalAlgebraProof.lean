module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (sameAccept)
open OriginalHereditaryValidityInternalBranchProof (sameRejectAt)
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof (arityValueAt)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Proof-side algebra subexpression, not a replacement of the frozen machine.
Under actual unary/binary arity it is exactly its successor/sum return. -/
def rebuild : Program 3 := InternalAcceptance.branch
  (sameOf (arityOf (.projection 0)) (constant 3 1))
  (succOf (addOf (.projection 1) (.projection 2))) (succOf (.projection 1))

theorem unaryRecover (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) raw)))
    (hp : Nonempty (Derivation body Delta (graph3 rebuild out raw first second))) :
    Nonempty (Derivation body Delta (graph1 (.succ) out first)) := by
  let xs : Fin 3 → OTerm alpha := ![raw,first,second]
  have harity := arityValueAt (.projection 0) (suc z) raw xs (projectionValue 0 xs) ha
  have hs := sameAccept (arityOf (.projection 0)) (constant 3 1) (suc z) xs harity
    (InternalLessThanSupportProof.oneConstantValue xs)
  have hr := successorBranchElim _ _ _ out z xs hs hp
  exact InternalApplicationCertificateConstructorsSupportProof.unaryRecover .succ (.projection 1) out first xs hr (projectionValue 1 xs)
theorem binaryBranch (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hp : Nonempty (Derivation body Delta (graph3 rebuild out raw first second))) :
    Nonempty (Derivation body Delta
      (graph3 (succOf (addOf (.projection 1) (.projection 2))) out raw first second)) := by
  let vs : Fin 3 → OTerm alpha := ![raw,first,second]
  have harity := arityValueAt (.projection 0) (suc (suc z)) raw vs (projectionValue 0 vs) ha
  exact branchNumeralElim 2 1 (arityOf (.projection 0)) _ _ out vs harity hp

/-- Composition of the actual successor-of-sum graph, kept independent of
large machine branch ASTs. -/
theorem sumAt {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (raw first second out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph3 (succOf (addOf (.projection 1) (.projection 2))) out raw first second)))
    (hf : Nonempty (Derivation body Delta (programGraph p first xs)))
    (hs : Nonempty (Derivation body Delta (programGraph q second xs))) :
    Nonempty (Derivation body Delta (programGraph (succOf (addOf p q)) out xs)) := by
  apply programCases InternalArithmeticPrograms.addition (Fin.cons first (Fin.cons second Fin.elim0)) _
  intro beta j Theta total hj ht
  simp only [consTermRename,emptyRename] at ht
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [programRename,consTermRename,emptyRename] at hp' hf' hs'
  let vs : Fin 3 → OTerm beta := ![raw.relabel j,first.relabel j,second.relabel j]
  have hsum := binaryValue InternalArithmeticPrograms.addition (.projection 1) (.projection 2)
    total (first.relabel j) (second.relabel j) vs ht (projectionValue 1 vs) (projectionValue 2 vs)
  have hsucc := InternalApplicationCertificateConstructorsSupportProof.unaryRecover .succ
    (addOf (.projection 1) (.projection 2)) (out.relabel j) total vs hp' hsum
  exact unaryValue .succ (addOf p q) (out.relabel j) total (fun i => (xs i).relabel j) hsucc
    (binaryValue InternalArithmeticPrograms.addition p q total (first.relabel j) (second.relabel j)
      (fun i => (xs i).relabel j) ht hf' hs')

theorem binaryAt {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hp : Nonempty (Derivation body Delta (graph3 rebuild out raw first second)))
    (hf : Nonempty (Derivation body Delta (programGraph p first xs)))
    (hs : Nonempty (Derivation body Delta (programGraph q second xs))) :
    Nonempty (Derivation body Delta (programGraph (succOf (addOf p q)) out xs)) :=
  sumAt p q xs raw first second out (binaryBranch raw first second out ha hp) hf hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
