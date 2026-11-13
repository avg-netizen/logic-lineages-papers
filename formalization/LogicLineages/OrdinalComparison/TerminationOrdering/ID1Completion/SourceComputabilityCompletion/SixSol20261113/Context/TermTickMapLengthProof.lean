module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickMapLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zero (F : Program 1) (code row : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph z code)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code))) :
    Nonempty (Derivation body Delta (lengthGraph z row)) := by
  have he := lengthZeroRecover code hl
  have hm0 := headTransport (InternalListMap.map (k := 0) F) row code z Fin.elim0 he hm
  obtain ⟨hr⟩ := valueUnique (InternalListMap.map (k := 0) F) row z (Fin.cons z Fin.elim0) hm0 (AdmittedMapSlotsProof.mapZero F)
  exact headTransport length z z row Fin.elim0 ⟨symm hr⟩ lengthZero

theorem one (F : Program 1) (code row first : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc z) code)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row))) :
    Nonempty (Derivation body Delta (lengthGraph (suc z) row)) :=
  lengthCons row first z z (AdmittedMapSlotsProof.singleton F code row first hl hm hf) lengthZero

theorem two (F : Program 1) (code row first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc (suc z)) code)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row code)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row))) :
    Nonempty (Derivation body Delta (lengthGraph (suc (suc z)) row)) := by
  apply AdmittedMapSlotsProof.binaryCases F code row first second _ hl hm hf hs
  intro beta j Theta tail hj hc ht
  simp only [OriginalContextInsertion.lengthGraph,graph1Rename,sucRelabel,zRelabel]
  exact lengthCons (row.relabel j) (first.relabel j) tail (suc z) hc
    (lengthCons tail (second.relabel j) z z ht lengthZero)

theorem actual (F : Program 1) (count role typ raw jobs annotatedPrefix row first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row))) :
    Nonempty (Derivation body Delta (lengthGraph count row)) := by
  have hl := SixSol20261113.Runtime.SourceFramedScanLengthProof.scanLength count role typ raw jobs annotatedPrefix hscan
  have hv := OriginalRawSyntaxTransportInternalConstructorArityCasesProof.arityRange raw count ha
  apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hv
  · intro Theta inc he
    have heq : Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn count z)) := by
      simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
    have hlen := outputTransport length count z (Fin.cons annotatedPrefix Fin.elim0) heq
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl inc)
    have hr := zero F annotatedPrefix row hlen
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm inc)
    obtain ⟨heq⟩ := heq
    exact outputTransport length z count (Fin.cons row Fin.elim0) ⟨symm heq⟩ hr
  · intro Theta inc hrest
    apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hrest
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn count (suc z))) := by
        simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
      have hlen := outputTransport length count (suc z) (Fin.cons annotatedPrefix Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl incl)
      have hr := one F annotatedPrefix row first hlen
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
      obtain ⟨heq⟩ := heq
      exact outputTransport length (suc z) count (Fin.cons row Fin.elim0) ⟨symm heq⟩ hr
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn count (suc (suc z)))) := by
        simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
      have hlen := outputTransport length count (suc (suc z)) (Fin.cons annotatedPrefix Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl incl)
      have hr := two F annotatedPrefix row first second hlen
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hs incl)
      obtain ⟨heq⟩ := heq
      exact outputTransport length (suc (suc z)) count (Fin.cons row Fin.elim0) ⟨symm heq⟩ hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickMapLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickMapLengthProof
