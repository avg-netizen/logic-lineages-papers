module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def headOf {k : Nat} (raw : Program k) : Program k :=
  InternalAcceptance.branch (sameOf (leftOf raw) (constant k 5))
    (leftOf (rightOf raw)) (leftOf (rightOf (rightOf raw)))

theorem headSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p : Program n} {q : Program m} (hp : Substitutes gs p q) :
    Substitutes gs (headOf p) (headOf q) := by
  have hl := unarySubstitution InternalUnpair.left hp
  have h1 := unarySubstitution InternalUnpair.right hp
  have h2 := unarySubstitution InternalUnpair.right h1
  exact branchSubstitution (sameSubstitution hl (constantSubstitution gs 5))
    (unarySubstitution InternalUnpair.left h1) (unarySubstitution InternalUnpair.left h2)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem headValueAt {k : Nat} (p : Program k) (head raw : OTerm alpha) (xs : Fin k → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (hh : Nonempty (Derivation body Delta (graph1 (headOf (.projection 0)) head raw))) :
    Nonempty (Derivation body Delta (programGraph (headOf p) head xs)) := by
  apply (substitutionGraph (headSubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
    (Fin.cons raw Fin.elim0) xs head (fun i => ?_)).mp hh
  obtain rfl := Fin.eq_zero i
  exact hp

theorem firstAt (table raw first : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))) :
    Nonempty (Derivation body Delta (graph2 OriginalCodeDecoderStep.firstField first table raw)) :=
  firstValueAt (.projection 1) first raw (Fin.cons table (Fin.cons raw Fin.elim0))
    (projectionValue 1 (Fin.cons table (Fin.cons raw Fin.elim0))) hf

theorem secondAt (table raw second : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta (graph2 OriginalCodeDecoderStep.secondField second table raw)) :=
  secondValueAt (.projection 1) second raw (Fin.cons table (Fin.cons raw Fin.elim0))
    (projectionValue 1 (Fin.cons table (Fin.cons raw Fin.elim0))) hs

theorem headAt (table raw head : OTerm alpha)
    (hh : Nonempty (Derivation body Delta (graph1 (headOf (.projection 0)) head raw))) :
    Nonempty (Derivation body Delta (graph2 OriginalCodeDecoderStep.headField head table raw)) :=
  headValueAt (.projection 1) head raw (Fin.cons table (Fin.cons raw Fin.elim0))
    (projectionValue 1 (Fin.cons table (Fin.cons raw Fin.elim0))) hh

theorem fieldCases (raw : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (tag payload first second head : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (raw.relabel j) tag payload)) →
      Nonempty (Derivation body Theta (graph1 (firstOf (.projection 0)) first (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (secondOf (.projection 0)) second (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (headOf (.projection 0)) head (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let qs : Fin 5 → Program 1 := ![InternalUnpair.left,InternalUnpair.right,
    firstOf (.projection 0),secondOf (.projection 0),headOf (.projection 0)]
  apply queryCases qs (Fin.cons raw Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hp := InternalApplicationCertificateConstructorsSupportProof.reconstructPair (raw.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hp (hq 2) (hq 3) (hq 4)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
