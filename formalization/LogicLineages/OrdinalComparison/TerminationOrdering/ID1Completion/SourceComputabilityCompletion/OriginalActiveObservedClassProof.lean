module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The frozen active class test at the literal raw-rank observer. -/
abbrev rankClass (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Program 3 :=
  OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P

/-- The actual preguard minimum occurring inside the frozen `inputs`. -/
abbrev preguard (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Program 2 :=
  OriginalTransparentMinimum.minimum (OriginalTypedDecoder.target H G) (rankClass p H G W P)

/-- A rejected equality control selects the class branch; the known activation
control then selects the observed branch of the actual `classTest`. -/
theorem activeObserverOfRejected (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (O : Program 1) (P : Program 3)
    (mark seed out parameter : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z out seed)))
    (hw : Nonempty (Derivation body Gamma
      (programGraph (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
        (OriginalActiveObservedClass.classTest p H G W O P)) (suc z)
        (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma ((graph1 O mark out).iff (graph1 O mark seed))) := by
  let xs : Fin 3 → OTerm α := Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0))
  have hc : Nonempty (Derivation body Gamma
      (programGraph (Program.composition InternalEqualityTest.equalityTest
        ![(Program.projection 1 : Program 3),Program.projection 0]) z xs)) :=
    binaryValue InternalEqualityTest.equalityTest (.projection 1) (.projection 0) z out seed xs
      hz (projectionValue 1 xs) (projectionValue 0 xs)
  have hclass : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.branch
        (Program.composition (OriginalActiveObservedClass.activation p H G W)
          ![(Program.projection 0 : Program 3),Program.projection 2])
        P (OriginalObservedClass.observed O P)) (suc z) xs)) :=
    zeroBranchElim
      (Program.composition InternalEqualityTest.equalityTest
        ![(Program.projection 1 : Program 3),Program.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O P)
      (Program.composition (OriginalTypedDecoder.target H G)
        ![(Program.projection 0 : Program 3),Program.projection 2])
      (suc z) xs hc hw
  have hact : Nonempty (Derivation body Gamma
      (programGraph (Program.composition (OriginalActiveObservedClass.activation p H G W)
        ![(Program.projection 0 : Program 3),Program.projection 2]) (suc z) xs)) :=
    binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) seed parameter xs ha (projectionValue 0 xs) (projectionValue 2 xs)
  have ho : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.conjunction P
        (InternalApplicationStepPeel.same (OriginalObservedClassProof.candidateQuery O)
          (OriginalObservedClassProof.seedQuery O))) (suc z) xs)) :=
    successorBranchElim
      (Program.composition (OriginalActiveObservedClass.activation p H G W)
        ![(Program.projection 0 : Program 3),Program.projection 2])
      P (OriginalObservedClass.observed O P) (suc z) z xs hact hclass
  exact OriginalObservedClassProof.observerOfSame O mark seed out parameter
    (andRight (conjunctionRecover P
      (InternalApplicationStepPeel.same (OriginalObservedClassProof.candidateQuery O)
        (OriginalObservedClassProof.seedQuery O)) xs ho))

/-- Internal trichotomy on candidate and seed under the activation premise. -/
theorem activeHit (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (O : Program 1) (P : Program 3)
    (seed out parameter mark : OTerm α) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter ⊓
        programGraph (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
          (OriginalActiveObservedClass.classTest p H G W O P)) (suc z)
          (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))).imp
        ((graph1 O mark out).iff (graph1 O mark seed)))) := by
  let A : Formula α :=
    graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter ⊓
      programGraph (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
        (OriginalActiveObservedClass.classTest p H G W O P)) (suc z)
        (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))
  have hh : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have ha : Derivation body (A :: Gamma)
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter) :=
    Derivation.conjunctionLeft hh
  have hw : Derivation body (A :: Gamma)
      (programGraph (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
        (OriginalActiveObservedClass.classTest p H G W O P)) (suc z)
        (Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0)))) :=
    Derivation.conjunctionRight hh
  obtain ⟨cmp⟩ := actualOriginalComparison body α out seed
  have hc := compareView (weakenClosed cmp (A :: Gamma))
  obtain ⟨hl⟩ := activeObserverOfRejected (body := body) (Gamma := ltF out seed :: A :: Gamma)
    p H G W O P mark seed out parameter ⟨addHyp ha _⟩
    (InternalEqualityTestProof.rejectForwardOrder out seed
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hw _⟩
  obtain ⟨he⟩ := OriginalObservedClassProof.observerOfEqual (body := body)
    (Gamma := eqn out seed :: A :: Gamma) O mark out seed
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := activeObserverOfRejected (body := body) (Gamma := ltF seed out :: A :: Gamma)
    p H G W O P mark seed out parameter ⟨addHyp ha _⟩
    (InternalEqualityTestProof.rejectBackwardOrder out seed
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hw _⟩
  have rest : Derivation body (A :: Gamma)
      ((eqn out seed ⊔ ltF seed out).imp ((graph1 O mark out).iff (graph1 O mark seed))) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination hc (Derivation.implicationIntroduction hl) rest)⟩

theorem actualOriginalActiveObservedClassHit :
    OriginalActiveObservedClassTargets.ActualOriginalActiveObservedClassHit := by
  intro p H G W O P body alpha Delta seed out parameter mark
  exact activeHit p H G W O P seed out parameter mark

/-- Simultaneous internal witnesses: the minimum output and its raw rank. -/
def collapseQueries (R : Program 2) : Fin 2 → Program 2 :=
  Fin.cons R (Fin.cons (Program.composition OriginalRawSyntaxTransport.variableRankPackedRaw
    (fun _ : Fin 1 => R)) Fin.elim0)

theorem collapseQuery0 (R : Program 2) : collapseQueries R (0 : Fin 2) = R := rfl
theorem collapseQuery1 (R : Program 2) : collapseQueries R (1 : Fin 2) =
    Program.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => R) := rfl

/-- At bound witnesses: the actual minimum law gives an accepted hit, the active
Hit gives rank equality, `sameAccept` accepts the rank control, and the
nonzero branch is the literal minimum graph. The fallback never needs refuting
separately: the accepted control selects the minimum branch directly. -/
theorem collapseAtValues (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (hmin : OriginalTransparentMinimum.MinimumLaw (OriginalTypedDecoder.target H G)
      (rankClass p H G W P))
    (out seed parameter candidate bx : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (graph2 (OriginalTypedDecoder.target H G) (suc z) seed parameter)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hw : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch
        (OriginalRankGuardedRepresentative.sameRank (preguard p H G W P))
        (Program.projection 0) (preguard p H G W P)) out seed parameter)))
    (hr : Nonempty (Derivation body Gamma (graph2 (preguard p H G W P) candidate seed parameter)))
    (hxq : Nonempty (Derivation body Gamma
      (programGraph (Program.composition OriginalRawSyntaxTransport.variableRankPackedRaw
        (fun _ : Fin 1 => preguard p H G W P)) bx
        (Fin.cons seed (Fin.cons parameter Fin.elim0))))) :
    Nonempty (Derivation body Gamma (graph2 (preguard p H G W P) out seed parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons seed (Fin.cons parameter Fin.elim0)
  obtain ⟨ht'⟩ := ht
  obtain ⟨ha'⟩ := ha
  obtain ⟨hr'⟩ := hr
  obtain ⟨hx⟩ := unaryRecover (body := body) (Gamma := Gamma)
    OriginalRawSyntaxTransport.variableRankPackedRaw (preguard p H G W P) bx candidate xs
    hxq ⟨hr'⟩
  obtain ⟨hm⟩ := hmin body α Gamma candidate seed parameter seed
  have hlaw := Derivation.implicationElimination hm (Derivation.conjunctionIntroduction ht' hr')
  have hhit0 := Derivation.conjunctionLeft (Derivation.conjunctionRight hlaw)
  have hhit : Derivation body Gamma
      (programGraph (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
        (OriginalActiveObservedClass.classTest p H G W
          OriginalRawSyntaxTransport.variableRankPackedRaw P)) (suc z)
        (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0)))) := hhit0
  obtain ⟨hh⟩ := activeHit (body := body) (Gamma := Gamma) p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P seed candidate parameter bx
  have hiff := Derivation.implicationElimination hh (Derivation.conjunctionIntroduction ha' hhit)
  have hforward : Derivation body Gamma
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw bx candidate).imp
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw bx seed)) :=
    Derivation.conjunctionLeft hiff
  have hseed : Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw bx seed) :=
    Derivation.implicationElimination hforward hx
  have hright := unaryValue (body := body) (Gamma := Gamma)
    OriginalRawSyntaxTransport.variableRankPackedRaw (Program.projection 0 : Program 2)
    bx seed xs ⟨hseed⟩ (projectionValue 0 xs)
  have hacc := sameAccept
    (Program.composition OriginalRawSyntaxTransport.variableRankPackedRaw
      (fun _ : Fin 1 => preguard p H G W P))
    (Program.composition OriginalRawSyntaxTransport.variableRankPackedRaw
      (fun _ : Fin 1 => (Program.projection 0 : Program 2))) bx xs hxq hright
  exact successorBranchElim
    (OriginalRankGuardedRepresentative.sameRank (preguard p H G W P))
    (Program.projection 0) (preguard p H G W P) out z xs hacc hw

/-- Bind the minimum output and its rank by internal Program totality. -/
theorem collapseInner (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (hmin : OriginalTransparentMinimum.MinimumLaw (OriginalTypedDecoder.target H G)
      (rankClass p H G W P))
    (out seed parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (graph2 (OriginalTypedDecoder.target H G) (suc z) seed parameter)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hw : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch
        (OriginalRankGuardedRepresentative.sameRank (preguard p H G W P))
        (Program.projection 0) (preguard p H G W P)) out seed parameter))) :
    Nonempty (Derivation body Gamma (graph2 (preguard p H G W P) out seed parameter)) := by
  apply queryCases (collapseQueries (preguard p H G W P))
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro β j ys Delta hj hys
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hys
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at ht'
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at ha'
  simp only [sucRelabel,zRelabel] at ht' ha'
  have hw' := renameInto hw j Delta hj
  rw [graph2Rename] at hw'
  have hr := hys 0
  rw [collapseQuery0] at hr
  have hx := hys 1
  rw [collapseQuery1] at hx
  exact collapseAtValues p H G W P hmin (out.relabel j) (seed.relabel j) (parameter.relabel j)
    (ys 0) (ys 1) ht' ha' hw' hr hx

/-- The frozen GuardCollapse law from the actual minimum law. Source, window and
representative fields are identified by literal record reduction only. -/
theorem guardCollapseOfMinimum (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (hmin : OriginalTransparentMinimum.MinimumLaw (OriginalTypedDecoder.target H G)
      (rankClass p H G W P)) :
    OriginalActiveObservedClass.GuardCollapseLaw p H G W P := by
  intro body alpha Delta seed out parameter
  let A : Formula alpha :=
    graph2 (OriginalTypedDecoder.target H G) InternalOriginalStepGuard.one seed parameter ⊓
      (graph2 (OriginalActiveObservedClass.activation p H G W)
          InternalOriginalStepGuard.one seed parameter ⊓
        graph2 (OriginalActiveObservedClass.inputs p H G W P).base.oldRepresentative
          out seed parameter)
  have hh : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  have ht : Nonempty (Derivation body (A :: Delta)
      (graph2 (OriginalTypedDecoder.target H G) (suc z) seed parameter)) :=
    ⟨Derivation.conjunctionLeft hh⟩
  have ha : Nonempty (Derivation body (A :: Delta)
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hh)⟩
  have hr : Nonempty (Derivation body (A :: Delta)
      (graph2 (OriginalActiveObservedClass.inputs p H G W P).base.oldRepresentative
        out seed parameter)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hh)⟩
  change Nonempty (Derivation body (A :: Delta)
    (graph2 (OriginalRankGuardedRepresentative.representative
      (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
      (preguard p H G W P) p.window) out seed parameter)) at hr
  have hactive : Nonempty (Derivation body (A :: Delta)
      (graph2 (OriginalRankGuardedRepresentative.active
        (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
        p.window) (suc z) seed parameter)) := ha
  have hinner := successorBranchElim
    (OriginalRankGuardedRepresentative.active
      (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource p.window)
    (preguard p H G W P)
    (InternalAcceptance.branch
      (OriginalRankGuardedRepresentative.sameRank (preguard p H G W P))
      (Program.projection 0) (preguard p H G W P))
    out z (Fin.cons seed (Fin.cons parameter Fin.elim0)) hactive hr
  obtain ⟨h⟩ := collapseInner p H G W P hmin out seed parameter ht ha hinner
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassProof
