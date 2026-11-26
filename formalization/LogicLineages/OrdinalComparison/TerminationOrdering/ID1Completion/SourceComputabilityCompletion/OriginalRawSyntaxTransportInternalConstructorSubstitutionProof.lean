module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport OriginalLambdaTraversalInternalSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal numeral ASTs commute with syntactic parameter substitution. -/
theorem constantSubstitution {m n : Nat} (gs : Fin n → Program m) (k : Nat) :
    Substitutes gs (constant n k) (constant m k) := by
  induction k with
  | zero => exact constantZeroSubstitution gs
  | succ k ih => exact unarySubstitution .succ ih

theorem branchSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p q r : Program n} {p' q' r' : Program m}
    (hp : Substitutes gs p p') (hq : Substitutes gs q q') (hr : Substitutes gs r r') :
    Substitutes gs (InternalAcceptance.branch p q r) (InternalAcceptance.branch p' q' r') :=
  .composition _ _ _ (fun i => Fin.cases hp
    (Fin.cases hq (Fin.cases hr (fun j => Fin.elim0 j))) i)

theorem sameSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p q : Program n} {p' q' : Program m}
    (hp : Substitutes gs p p') (hq : Substitutes gs q q') :
    Substitutes gs (sameOf p q) (sameOf p' q') := binarySubstitution _ hp hq

theorem aritySubstitution {m n : Nat} {gs : Fin n → Program m}
    {p : Program n} {q : Program m} (hp : Substitutes gs p q) :
    Substitutes gs (arityOf p) (arityOf q) := by
  have hl := unarySubstitution InternalUnpair.left hp
  exact branchSubstitution (sameSubstitution hl (constantSubstitution gs 1))
    (branchSubstitution (sameSubstitution hl (constantSubstitution gs 4))
      (branchSubstitution (sameSubstitution hl (constantSubstitution gs 2))
        (branchSubstitution (sameSubstitution hl (constantSubstitution gs 5))
          (branchSubstitution (sameSubstitution hl (constantSubstitution gs 7))
            (constantSubstitution gs 0) (constantSubstitution gs 2))
          (constantSubstitution gs 2)) (constantSubstitution gs 2))
      (constantSubstitution gs 1)) (constantSubstitution gs 1)

theorem firstSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p : Program n} {q : Program m} (hp : Substitutes gs p q) :
    Substitutes gs (firstOf p) (firstOf q) := by
  have hl := unarySubstitution InternalUnpair.left hp
  have h1 := unarySubstitution InternalUnpair.right hp
  have h2 := unarySubstitution InternalUnpair.right h1
  have h3 := unarySubstitution InternalUnpair.right h2
  have h4 := unarySubstitution InternalUnpair.right h3
  exact branchSubstitution (sameSubstitution hl (constantSubstitution gs 1))
    (branchSubstitution (sameSubstitution hl (constantSubstitution gs 4))
      (branchSubstitution (sameSubstitution hl (constantSubstitution gs 5))
        (unarySubstitution InternalUnpair.left h2) (unarySubstitution InternalUnpair.left h4)) h2) h2

theorem secondSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p : Program n} {q : Program m} (hp : Substitutes gs p q) :
    Substitutes gs (secondOf p) (secondOf q) := by
  have hl := unarySubstitution InternalUnpair.left hp
  have h1 := unarySubstitution InternalUnpair.right hp
  have h2 := unarySubstitution InternalUnpair.right h1
  have h3 := unarySubstitution InternalUnpair.right h2
  have h4 := unarySubstitution InternalUnpair.right h3
  have h5 := unarySubstitution InternalUnpair.right h4
  have h6 := unarySubstitution InternalUnpair.right h5
  exact branchSubstitution (sameSubstitution hl (constantSubstitution gs 5)) h3 h6

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem arityValueAt {n : Nat} (p : Program n) (arity raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) arity raw))) :
    Nonempty (Derivation body Delta (programGraph (arityOf p) arity xs)) := by
  apply (substitutionGraph (aritySubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
    (Fin.cons raw Fin.elim0) xs arity (fun i => ?_)).mp ha
  obtain rfl := Fin.eq_zero i
  exact hp

theorem firstValueAt {n : Nat} (p : Program n) (first raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ha : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))) :
    Nonempty (Derivation body Delta (programGraph (firstOf p) first xs)) := by
  apply (substitutionGraph (firstSubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
    (Fin.cons raw Fin.elim0) xs first (fun i => ?_)).mp ha
  obtain rfl := Fin.eq_zero i
  exact hp

theorem secondValueAt {n : Nat} (p : Program n) (second raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p raw xs)))
    (ha : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta (programGraph (secondOf p) second xs)) := by
  apply (substitutionGraph (secondSubstitution (Substitutes.projection (gs := fun _ : Fin 1 => p) 0))
    (Fin.cons raw Fin.elim0) xs second (fun i => ?_)).mp ha
  obtain rfl := Fin.eq_zero i
  exact hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
