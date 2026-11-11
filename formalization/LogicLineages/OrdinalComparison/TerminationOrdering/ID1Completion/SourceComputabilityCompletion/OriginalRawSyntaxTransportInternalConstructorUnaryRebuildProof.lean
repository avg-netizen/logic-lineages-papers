module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalConstructorRankProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem lambdaShiftRebuildForward (raw out domain child first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (programGraph lambdaConstructor out (Fin.cons domain (Fin.cons first Fin.elim0)))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 2 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1]
  have hsub : Substitutes qs lambdaConstructor (pairOf (constant 3 1) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (.projection 1))) :=
    pairSubstitution (constantSubstitution qs 1) (pairSubstitution (Substitutes.projection 0) (Substitutes.projection 1))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![domain,first] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (lambdaDomain (.projection 0) raw domain child xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      · exact Fin.elim0 j1
  have ht := lambdaTag (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 1 1 (leftOf (.projection 0)) _ _ out xs ht ho
  exact (substitutionGraph hsub (Fin.cons domain (Fin.cons first Fin.elim0)) xs out hg).mpr h1

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem lambdaShiftRebuildBackward (raw out domain child first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (programGraph lambdaConstructor out (Fin.cons domain (Fin.cons first Fin.elim0))))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 2 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1]
  have hsub : Substitutes qs lambdaConstructor (pairOf (constant 3 1) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (.projection 1))) :=
    pairSubstitution (constantSubstitution qs 1) (pairSubstitution (Substitutes.projection 0) (Substitutes.projection 1))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![domain,first] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (lambdaDomain (.projection 0) raw domain child xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      · exact Fin.elim0 j1
  have ht := lambdaTag (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 1 1 (leftOf (.projection 0)) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons domain (Fin.cons first Fin.elim0)) xs out hg).mp ho

theorem lambdaRebuildForward (mode : Mode) (raw out domain child first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (UnaryResult mode lambdaConstructor out domain first)) := by
  cases mode with
  | shift => exact lambdaShiftRebuildForward raw out domain child first second hc ho
  | erase => exact lambdaShiftRebuildForward raw out domain child first second hc ho
  | rank =>
    have ha := lambdaArity (.projection 0) raw domain child
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact unaryRankForward raw first second out ha ho

theorem lambdaRebuildBackward (mode : Mode) (raw out domain child first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph lambdaConstructor raw (Fin.cons domain (Fin.cons child Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (UnaryResult mode lambdaConstructor out domain first))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact lambdaShiftRebuildBackward raw out domain child first second hc ho
  | erase => exact lambdaShiftRebuildBackward raw out domain child first second hc ho
  | rank =>
    have ha := lambdaArity (.projection 0) raw domain child
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact unaryRankBackward raw first second out ha ho

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem ordinaryShiftRebuildForward (raw out head base first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (programGraph ordinaryConstructor out (Fin.cons head (Fin.cons first Fin.elim0)))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 2 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1]
  have hsub : Substitutes qs ordinaryConstructor (pairOf (constant 3 4) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (.projection 1))) :=
    pairSubstitution (constantSubstitution qs 4) (pairSubstitution (Substitutes.projection 0) (Substitutes.projection 1))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![head,first] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (ordinaryHead (.projection 0) raw head base xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      · exact Fin.elim0 j1
  have ht := ordinaryTag (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 4 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 4 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 4 4 (leftOf (.projection 0)) _ _ out xs ht h2
  exact (substitutionGraph hsub (Fin.cons head (Fin.cons first Fin.elim0)) xs out hg).mpr h4

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem ordinaryShiftRebuildBackward (raw out head base first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (programGraph ordinaryConstructor out (Fin.cons head (Fin.cons first Fin.elim0))))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 2 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1]
  have hsub : Substitutes qs ordinaryConstructor (pairOf (constant 3 4) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (.projection 1))) :=
    pairSubstitution (constantSubstitution qs 4) (pairSubstitution (Substitutes.projection 0) (Substitutes.projection 1))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![head,first] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (ordinaryHead (.projection 0) raw head base xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      · exact Fin.elim0 j1
  have ht := ordinaryTag (.projection 0) raw head base xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 4 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 4 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 4 4 (leftOf (.projection 0)) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons head (Fin.cons first Fin.elim0)) xs out hg).mp ho

theorem ordinaryRebuildForward (mode : Mode) (raw out head base first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (UnaryResult mode ordinaryConstructor out head first)) := by
  cases mode with
  | shift => exact ordinaryShiftRebuildForward raw out head base first second hc ho
  | erase => exact ordinaryShiftRebuildForward raw out head base first second hc ho
  | rank =>
    have ha := ordinaryArity (.projection 0) raw head base
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact unaryRankForward raw first second out ha ho

theorem ordinaryRebuildBackward (mode : Mode) (raw out head base first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph ordinaryConstructor raw (Fin.cons head (Fin.cons base Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (UnaryResult mode ordinaryConstructor out head first))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact ordinaryShiftRebuildBackward raw out head base first second hc ho
  | erase => exact ordinaryShiftRebuildBackward raw out head base first second hc ho
  | rank =>
    have ha := ordinaryArity (.projection 0) raw head base
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact unaryRankBackward raw first second out ha ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof
