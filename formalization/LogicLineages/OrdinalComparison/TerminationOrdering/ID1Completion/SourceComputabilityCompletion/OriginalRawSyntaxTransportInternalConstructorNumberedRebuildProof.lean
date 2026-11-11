module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorNumberedRebuildProof
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
theorem numberedShiftRebuildForward (raw out label head tau base types extras first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (programGraph numberedConstructor out (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons first (Fin.cons types (Fin.cons second Fin.elim0)))))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 6 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),leftOf (rightOf (rightOf (.projection 0 : Program 3))),leftOf (rightOf (rightOf (rightOf (.projection 0 : Program 3)))),.projection 1,leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0 : Program 3)))))),.projection 2]
  have hsub : Substitutes qs numberedConstructor (pairOf (constant 3 5) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (leftOf (rightOf (rightOf (.projection 0 : Program 3)))) (pairOf (leftOf (rightOf (rightOf (rightOf (.projection 0 : Program 3))))) (pairOf (.projection 1) (pairOf (leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0 : Program 3))))))) (.projection 2))))))) :=
    pairSubstitution (constantSubstitution qs 5) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (pairSubstitution (Substitutes.projection 2) (pairSubstitution (Substitutes.projection 3) (pairSubstitution (Substitutes.projection 4) (Substitutes.projection 5))))))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![label,head,tau,first,types,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (numberedLabel (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (numberedHead (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (numberedType (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
        ·
          refine Fin.cases ?_ (fun j3 => ?_) j2
          · exact (projectionValue 1 xs)
          ·
            refine Fin.cases ?_ (fun j4 => ?_) j3
            · exact (numberedTypes (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
            ·
              refine Fin.cases ?_ (fun j5 => ?_) j4
              · exact (projectionValue 2 xs)
              · exact Fin.elim0 j5
  have ht := numberedTag (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 5 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 5 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 5 4 (leftOf (.projection 0)) _ _ out xs ht h2
  have h5 := branchNumeralElim 5 5 (leftOf (.projection 0)) _ _ out xs ht h4
  exact (substitutionGraph hsub (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons first (Fin.cons types (Fin.cons second Fin.elim0)))))) xs out hg).mpr h5

/-- Exact copied metadata and ordered child outputs in the original rebuild AST. -/
theorem numberedShiftRebuildBackward (raw out label head tau base types extras first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
    (ho : Nonempty (Derivation body Delta (programGraph numberedConstructor out (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons first (Fin.cons types (Fin.cons second Fin.elim0))))))))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  let qs : Fin 6 → Program 3 := ![leftOf (rightOf (.projection 0 : Program 3)),leftOf (rightOf (rightOf (.projection 0 : Program 3))),leftOf (rightOf (rightOf (rightOf (.projection 0 : Program 3)))),.projection 1,leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0 : Program 3)))))),.projection 2]
  have hsub : Substitutes qs numberedConstructor (pairOf (constant 3 5) (pairOf (leftOf (rightOf (.projection 0 : Program 3))) (pairOf (leftOf (rightOf (rightOf (.projection 0 : Program 3)))) (pairOf (leftOf (rightOf (rightOf (rightOf (.projection 0 : Program 3))))) (pairOf (.projection 1) (pairOf (leftOf (rightOf (rightOf (rightOf (rightOf (rightOf (.projection 0 : Program 3))))))) (.projection 2))))))) :=
    pairSubstitution (constantSubstitution qs 5) (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1) (pairSubstitution (Substitutes.projection 2) (pairSubstitution (Substitutes.projection 3) (pairSubstitution (Substitutes.projection 4) (Substitutes.projection 5))))))
  have hg : ∀ i, Nonempty (Derivation body Delta (programGraph (qs i) (![label,head,tau,first,types,second] i) xs)) := by
    intro i
    refine Fin.cases ?_ (fun j0 => ?_) i
    · exact (numberedLabel (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
    ·
      refine Fin.cases ?_ (fun j1 => ?_) j0
      · exact (numberedHead (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
      ·
        refine Fin.cases ?_ (fun j2 => ?_) j1
        · exact (numberedType (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
        ·
          refine Fin.cases ?_ (fun j3 => ?_) j2
          · exact (projectionValue 1 xs)
          ·
            refine Fin.cases ?_ (fun j4 => ?_) j3
            · exact (numberedTypes (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc)
            ·
              refine Fin.cases ?_ (fun j5 => ?_) j4
              · exact (projectionValue 2 xs)
              · exact Fin.elim0 j5
  have ht := numberedTag (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 5 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 5 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 5 4 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 5 5 (leftOf (.projection 0)) _ _ out xs ht
  exact (substitutionGraph hsub (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons first (Fin.cons types (Fin.cons second Fin.elim0)))))) xs out hg).mp ho

theorem numberedRebuildForward (mode : Mode) (raw out label head tau base types extras first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (NumberedResult mode out label head tau first types second)) := by
  cases mode with
  | shift => exact numberedShiftRebuildForward raw out label head tau base types extras first second hc ho
  | erase => exact numberedShiftRebuildForward raw out label head tau base types extras first second hc ho
  | rank =>
    have ha := numberedArity (.projection 0) raw label head tau base types extras
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankForward 2 (by decide) raw first second out ha ho

theorem numberedRebuildBackward (mode : Mode) (raw out label head tau base types extras first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons tau (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
    (ho : Nonempty (Derivation body Delta (NumberedResult mode out label head tau first types second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact numberedShiftRebuildBackward raw out label head tau base types extras first second hc ho
  | erase => exact numberedShiftRebuildBackward raw out label head tau base types extras first second hc ho
  | rank =>
    have ha := numberedArity (.projection 0) raw label head tau base types extras
      (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) (projectionValue 0 (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0)))) hc
    exact nonunaryRankBackward 2 (by decide) raw first second out ha ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorNumberedRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorNumberedRebuildProof
