module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.RelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.AllowedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem identityImp (A : Formula alpha) : Nonempty (Derivation body Delta (A.imp A)) :=
  ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩

theorem andImp {A B C D : Formula alpha}
    (h1 : Nonempty (Derivation body Delta (A.imp B)))
    (h2 : Nonempty (Derivation body Delta (C.imp D))) :
    Nonempty (Derivation body Delta ((A ⊓ C).imp (B ⊓ D))) := by
  obtain ⟨h1⟩ := h1
  obtain ⟨h2⟩ := h2
  let H := A ⊓ C
  have h : Derivation body (H :: Delta) H := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp h1 H) (Derivation.conjunctionLeft h))
    (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp h2 H) (Derivation.conjunctionRight h)))⟩

theorem orImp {A B C D : Formula alpha}
    (h1 : Nonempty (Derivation body Delta (A.imp B)))
    (h2 : Nonempty (Derivation body Delta (C.imp D))) :
    Nonempty (Derivation body Delta ((A ⊔ C).imp (B ⊔ D))) := by
  obtain ⟨h1⟩ := h1
  obtain ⟨h2⟩ := h2
  let H := A ⊔ C
  have hl : Derivation body (A :: H :: Delta) (B ⊔ D) := InternalQuotientComparisonProof.orLeft
    (Derivation.implicationElimination
      (InternalBetaTotalityProof.addHyp (InternalBetaTotalityProof.addHyp h1 H) A)
      (Derivation.hypothesis List.mem_cons_self))
  have hr : Derivation body (C :: H :: Delta) (B ⊔ D) := InternalQuotientComparisonProof.orRight
    (Derivation.implicationElimination
      (InternalBetaTotalityProof.addHyp (InternalBetaTotalityProof.addHyp h2 H) C)
      (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.implicationIntroduction (InternalBetaTotalityProof.disjunctionElimination
    (Derivation.hypothesis List.mem_cons_self) (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction hr))⟩

theorem lookupImp (bound old next index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (RelationProof.relation bound old next)))
    (hb : Nonempty (Derivation body Delta (Below index (suc bound)))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup (suc z) index old).imp
        (graph2 InternalRawListRecursion.lookup (suc z) index next))) := by
  let A := graph2 InternalRawListRecursion.lookup (suc z) index old
  obtain ⟨h⟩ := RelationProof.relationApply bound old next index (withHyp hr A) (withHyp hb A)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem transport (n : Nat) (bound old next tag payload first second head : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (RelationProof.relation bound old next)))
    (hf : Nonempty (Derivation body Delta (Below first (suc bound))))
    (hs : Nonempty (Derivation body Delta (Below second (suc bound))))
    (ha : Nonempty (Derivation body Delta (OriginalCodeDecoderStep.Targets.allowed n old tag payload first second head))) :
    Nonempty (Derivation body Delta (OriginalCodeDecoderStep.Targets.allowed n next tag payload first second head)) := by
  have hfirst := lookupImp bound old next first hr hf
  have hsecond := lookupImp bound old next second hr hs
  have h0 := identityImp (body := body) (Delta := Delta) (eqn tag (numeral 0) ⊔ eqn tag (numeral 3))
  have h1 := andImp (identityImp (eqn tag (numeral 1))) hfirst
  have h2 := andImp (identityImp (eqn tag (numeral 2) ⊔ eqn tag (numeral 7))) (andImp hfirst hsecond)
  have h4 := andImp (identityImp (eqn tag (numeral 4)))
    (andImp (identityImp (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) hfirst)
  have h5 := andImp (identityImp (eqn tag (numeral 5)))
    (andImp (andImp (identityImp (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) hfirst) hsecond)
  have h6 := identityImp (body := body) (Delta := Delta) (eqn tag (numeral 6) ⊓ eqn payload (numeral 0))
  obtain ⟨h⟩ := orImp h0 (orImp h1 (orImp h2 (orImp h4 (orImp h5 h6))))
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination h ha⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.AllowedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.AllowedProof
