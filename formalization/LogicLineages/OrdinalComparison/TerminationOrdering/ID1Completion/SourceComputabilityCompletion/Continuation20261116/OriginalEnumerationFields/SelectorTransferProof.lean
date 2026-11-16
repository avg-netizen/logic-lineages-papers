module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.QueryTemplateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open QueryTemplateProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def arityTemplate : Template :=
  branch (same (left .input) (constant 1))
    (branch (same (left .input) (constant 4))
      (branch (same (left .input) (constant 2))
        (branch (same (left .input) (constant 5))
          (branch (same (left .input) (constant 7)) (constant 0) (constant 2))
          (constant 2)) (constant 2)) (constant 1)) (constant 1)
def firstTemplate : Template :=
  branch (same (left .input) (constant 1))
    (branch (same (left .input) (constant 4))
      (branch (same (left .input) (constant 5))
        (left (right (right .input))) (left (right (right (right (right .input))))))
      (right (right .input))) (right (right .input))
def secondTemplate : Template :=
  branch (same (left .input) (constant 5))
    (right (right (right .input))) (right (right (right (right (right (right .input))))))

theorem arityAST {k : Nat} (p : Program k) : instantiate p arityTemplate = OriginalRawSyntaxTransport.arityOf p := by
  simp only [arityTemplate,instantiateBranch,instantiateSame,instantiateLeft,instantiateConstant,instantiate]
  rfl

theorem firstAST {k : Nat} (p : Program k) : instantiate p firstTemplate = OriginalRawSyntaxTransport.firstOf p := by
  simp only [firstTemplate,instantiateBranch,instantiateSame,instantiateLeft,instantiateRight,instantiateConstant,instantiate]
  rfl

theorem secondAST {k : Nat} (p : Program k) : instantiate p secondTemplate = OriginalRawSyntaxTransport.secondOf p := by
  simp only [secondTemplate,instantiateBranch,instantiateSame,instantiateLeft,instantiateRight,instantiateConstant,instantiate]
  rfl

theorem arityAt {k : Nat} (p : Program k) (xs : Fin k → OTerm alpha) (raw out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ho : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) out raw))) :
    Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.arityOf p) out xs)) := by
  rw [← arityAST] at ho ⊢
  exact forward arityTemplate (.projection 0) p body alpha Delta (Fin.cons raw Fin.elim0) xs raw out
    (projectionValue 0 (Fin.cons raw Fin.elim0)) hp ho

theorem firstRecover {k : Nat} (p : Program k) (xs : Fin k → OTerm alpha) (raw out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.firstOf p) out xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) out raw)) := by
  rw [← firstAST] at ho ⊢
  exact forward firstTemplate p (.projection 0) body alpha Delta xs (Fin.cons raw Fin.elim0) raw out hp
    (projectionValue 0 (Fin.cons raw Fin.elim0)) ho

theorem secondRecover {k : Nat} (p : Program k) (xs : Fin k → OTerm alpha) (raw out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.secondOf p) out xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) out raw)) := by
  rw [← secondAST] at ho ⊢
  exact forward secondTemplate p (.projection 0) body alpha Delta xs (Fin.cons raw Fin.elim0) raw out hp
    (projectionValue 0 (Fin.cons raw Fin.elim0)) ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorTransferProof
