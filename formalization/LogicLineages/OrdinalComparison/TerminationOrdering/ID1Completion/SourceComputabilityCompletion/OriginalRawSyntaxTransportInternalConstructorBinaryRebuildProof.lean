module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof
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
theorem applicationShiftRebuildForward (raw out domain fn arg first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (programGraph applicationConstructor out (Fin.cons domain (Fin.cons first (Fin.cons second Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 3 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1,.projection 2]
  have hsub : Substitutes qs applicationConstructor (pairOf (constant 3 2) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (.projection 1) (.projection 2)))) :=
    pairSubstitution (constantSubstitution qs 2) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (Substitutes.projection 2)))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![domain,first,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (applicationDomain (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (projectionValue 2 xs)
        · exact Fin.elim0 j2
  have ht := applicationTag (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 2 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 2 2 (leftOf (.projection 0)) _ _ out xs ht h1
  exact (substitutionGraph hsub (Fin.cons domain (Fin.cons first (Fin.cons second Fin.elim0))) xs out hg).mpr h2

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem applicationShiftRebuildBackward (raw out domain fn arg first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (programGraph applicationConstructor out (Fin.cons domain (Fin.cons first (Fin.cons second Fin.elim0)))))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 3 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1,.projection 2]
  have hsub : Substitutes qs applicationConstructor (pairOf (constant 3 2) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (.projection 1) (.projection 2)))) :=
    pairSubstitution (constantSubstitution qs 2) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (Substitutes.projection 2)))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![domain,first,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (applicationDomain (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (projectionValue 2 xs)
        · exact Fin.elim0 j2
  have ht := applicationTag (.projection 0) raw domain fn arg xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 2 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 2 2 (leftOf (.projection 0)) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons domain (Fin.cons first (Fin.cons second Fin.elim0))) xs out hg).mp ho

theorem applicationRebuildForward (mode : Mode) (raw out domain fn arg first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (BinaryResult mode applicationConstructor out domain first second)) := by
  cases mode with
  | shift => exact applicationShiftRebuildForward raw out domain fn arg first second hc ho
  | erase => exact applicationShiftRebuildForward raw out domain fn arg first second hc ho
  | rank =>
    have ha := applicationArity (.projection 0) raw domain fn arg
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankForward 2 (by decide) raw first second out ha ho

theorem applicationRebuildBackward (mode : Mode) (raw out domain fn arg first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph applicationConstructor raw (Fin.cons domain (Fin.cons fn (Fin.cons arg Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (BinaryResult mode applicationConstructor out domain first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact applicationShiftRebuildBackward raw out domain fn arg first second hc ho
  | erase => exact applicationShiftRebuildBackward raw out domain fn arg first second hc ho
  | rank =>
    have ha := applicationArity (.projection 0) raw domain fn arg
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankBackward 2 (by decide) raw first second out ha ho

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem consShiftRebuildForward (raw out tau head tail first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (programGraph consConstructor out (Fin.cons tau (Fin.cons first (Fin.cons second Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 3 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1,.projection 2]
  have hsub : Substitutes qs consConstructor (pairOf (constant 3 7) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (.projection 1) (.projection 2)))) :=
    pairSubstitution (constantSubstitution qs 7) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (Substitutes.projection 2)))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![tau,first,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (consType (.projection 0) raw tau head tail xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (projectionValue 2 xs)
        · exact Fin.elim0 j2
  have ht := consTag (.projection 0) raw tau head tail xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 7 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 7 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 7 4 (leftOf (.projection 0)) _ _ out xs ht h2
  have h5 := branchNumeralElim 7 5 (leftOf (.projection 0)) _ _ out xs ht h4
  have h7 := branchNumeralElim 7 7 (leftOf (.projection 0)) _ _ out xs ht h5
  exact (substitutionGraph hsub (Fin.cons tau (Fin.cons first (Fin.cons second Fin.elim0))) xs out hg).mpr h7

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem consShiftRebuildBackward (raw out tau head tail first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (programGraph consConstructor out (Fin.cons tau (Fin.cons first (Fin.cons second Fin.elim0)))))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 3 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),.projection 1,.projection 2]
  have hsub : Substitutes qs consConstructor (pairOf (constant 3 7) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (.projection 1) (.projection 2)))) :=
    pairSubstitution (constantSubstitution qs 7) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (Substitutes.projection 2)))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![tau,first,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (consType (.projection 0) raw tau head tail xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (projectionValue 1 xs)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (projectionValue 2 xs)
        · exact Fin.elim0 j2
  have ht := consTag (.projection 0) raw tau head tail xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 7 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 7 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 7 4 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 7 5 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 7 7 (leftOf (.projection 0)) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons tau (Fin.cons first (Fin.cons second Fin.elim0))) xs out hg).mp ho

theorem consRebuildForward (mode : Mode) (raw out tau head tail first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (BinaryResult mode consConstructor out tau first second)) := by
  cases mode with
  | shift => exact consShiftRebuildForward raw out tau head tail first second hc ho
  | erase => exact consShiftRebuildForward raw out tau head tail first second hc ho
  | rank =>
    have ha := consArity (.projection 0) raw tau head tail
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankForward 2 (by decide) raw first second out ha ho

theorem consRebuildBackward (mode : Mode) (raw out tau head tail first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph consConstructor raw (Fin.cons tau (Fin.cons head (Fin.cons tail Fin.elim0))))))
    (ho : Nonempty (Derivation body Delta (BinaryResult mode consConstructor out tau first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact consShiftRebuildBackward raw out tau head tail first second hc ho
  | erase => exact consShiftRebuildBackward raw out tau head tail first second hc ho
  | rank =>
    have ha := consArity (.projection 0) raw tau head tail
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankBackward 2 (by decide) raw first second out ha ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof
