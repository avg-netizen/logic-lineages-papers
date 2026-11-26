module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalReflexiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalMinimumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum
open InternalApplicationCertificateConstructors (graph2)
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceSupportProof
open InternalEqualityTestCompositionProof InternalLessThanSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (refl)
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Recover the literal scan graph from an accepted minimum computation. -/
theorem scanOfMinimum (T : Program 2) (P : Program 3) (out seed parameter : OTerm α)
    (ht : Nonempty (Derivation body Delta (graph2 T InternalOriginalStepGuard.one seed parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 (minimum T P) out seed parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (scan (reflexiveClassTest T P)) out (suc seed) seed parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons seed (Fin.cons parameter Fin.elim0)
  let control : Program 2 := Program.composition InternalEqualityTest.equalityTest ![T,InternalLessThan.constantOne 2]
  let branch : Program 2 := Program.composition (scan (reflexiveClassTest T P))
    ![.composition .succ (fun _ : Fin 1 => .projection 0),.projection 0,.projection 1]
  have hc : Nonempty (Derivation body Delta (programGraph control (suc z) xs)) := by
    apply compositionValue InternalEqualityTest.equalityTest ![T,InternalLessThan.constantOne 2]
      (suc z) xs (Fin.cons (suc z) (Fin.cons (suc z) Fin.elim0))
      (equalityOfEqual (suc z) (suc z) ⟨refl (suc z)⟩)
    intro i
    exact Fin.cases ht (Fin.cases (oneConstantValue xs) (fun j => Fin.elim0 j)) i
  have hb := successorBranchElim control (InternalAcceptance.constantZero 2) branch out z xs hc hm
  apply compositionRecover (scan (reflexiveClassTest T P))
    ![.composition .succ (fun _ : Fin 1 => .projection 0),.projection 0,.projection 1]
    out xs (Fin.cons (suc seed) (Fin.cons seed (Fin.cons parameter Fin.elim0))) hb
  intro i
  refine Fin.cases ?_ (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j))) i
  apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc seed) xs
    (Fin.cons seed Fin.elim0) (successorValue (Fin.cons seed Fin.elim0))
  intro i
  exact Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j) i

/-- The minimum consumer needs the independently proved scan invariant.
The reflexive hit rules out every result above seed, so no sentinel convention
or native semantic argument enters the internal least-hit proof. -/
theorem minimumOfScan (T : Program 2) (P : Program 3)
    (hscan : ScanLaw (reflexiveClassTest T P)) : MinimumLaw T P := by
  intro body α Delta out seed parameter earlier
  let A := graph2 T InternalOriginalStepGuard.one seed parameter ⊓
    graph2 (minimum T P) out seed parameter
  have hh : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  have ht := Derivation.conjunctionLeft hh
  have hs := scanOfMinimum T P out seed parameter ⟨ht⟩ ⟨Derivation.conjunctionRight hh⟩
  obtain ⟨hs⟩ := hs
  obtain ⟨hr⟩ := OriginalTransparentMinimumInternalReflexiveProof.actualOriginalTransparentMinimumInternalReflexive
    T P body α (A :: Delta) seed parameter
  have href := Derivation.implicationElimination hr ht
  obtain ⟨hseed⟩ := hscan body α (A :: Delta) out (suc seed) seed parameter seed
  have hseed := Derivation.implicationElimination hseed hs
  have hmiss := Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hseed))
  have hn : Derivation body (A :: Delta) (InternalLessThan.strictLess seed out).not := by
    apply Derivation.implicationIntroduction
    exact Derivation.implicationElimination
      (Derivation.implicationElimination (addHyp hmiss _) (Derivation.hypothesis List.mem_cons_self))
      (addHyp href _)
  obtain ⟨hbound⟩ := InternalUnpairArithmeticProof.notLessWeak seed out ⟨hn⟩
  obtain ⟨hearlier⟩ := hscan body α (A :: Delta) out (suc seed) seed parameter earlier
  have hearlier := Derivation.implicationElimination hearlier hs
  have hhit := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.conjunctionRight hearlier)) hbound
  have hminimal := Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight hearlier))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hbound
    (Derivation.conjunctionIntroduction hhit hminimal))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalMinimumProof
