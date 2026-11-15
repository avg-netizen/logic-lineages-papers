module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.DependenciesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 NumericDependencyCross
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

theorem atLists (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail lefts rightTail rights rowTail row0 : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    (hrt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightTail b z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights r rightTail)))
    (hrow1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rowTail qb z)))
    (hrow0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row0 qr rowTail)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  have hcross := OriginalDecodedBinaryRecurrence.CrossProof.crossFour q a r b lefts leftTail rights rightTail qr qb ar ab deps d1 d2 d3 row0 rowTail
    hl hlt hr hrt h0 h1 h2 h3 hrow0 hrow1 hp0 hp1 hp2 hp3
  have hleft := ArgumentEntriesChildren.InternalProof.internalNumbered body alpha Delta source k f sigma q ts a leftTail lefts hs hlt hl
  have hright := ArgumentEntriesChildren.InternalProof.internalNumbered body alpha Delta target l g tau r us b rightTail rights ht hrt hr
  let xs : Fin 2 → OTerm alpha := ![source,target]
  have hl' := unaryValue ArgumentEntriesChildren.children (.projection 0) lefts source xs hleft (projectionValue 0 xs)
  have hr' := unaryValue ArgumentEntriesChildren.children (.projection 1) rights target xs hright (projectionValue 1 xs)
  have hraw := binaryValue cross (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0))
    (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 1)) deps lefts rights xs hcross hl' hr'
  have hx := binaryValue rawDependencies OriginalDecodedDependencies.source OriginalDecodedDependencies.target
    deps source target ![node,param] hraw
    (OriginalDecodedDependencies.SupportProof.sourceAt node param source target hn)
    (OriginalDecodedDependencies.SupportProof.targetAt node param source target hn)
  exact successorBranchIntro (OriginalDecodedDependencies.accepted n) (OriginalRawSyntaxTransport.constant 2 0)
    OriginalDecodedDependencies.decodedCross deps z ![node,param]
    (OriginalDecodedLambdaRecurrence.GuardProof.nodeRecover n node z param hg) hx

theorem at5 (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail lefts rightTail rights rowTail : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    (hrt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightTail b z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights r rightTail)))
    (hrow1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rowTail qb z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons qr (Fin.cons rowTail Fin.elim0)) _
  intro beta j Theta row0 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  have hltj := InternalGraphCompositionFunctionalityProof.renameInto hlt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hrtj := InternalGraphCompositionFunctionalityProof.renameInto hrt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrtj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hrow1j := InternalGraphCompositionFunctionalityProof.renameInto hrow1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrow1j
  exact atLists n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) (leftTail.relabel j) (lefts.relabel j) (rightTail.relabel j) (rights.relabel j) (rowTail.relabel j) row0 hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hltj hlj hrtj hrj hrow1j hx

theorem at4 (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail lefts rightTail rights : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    (hrt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightTail b z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights r rightTail)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons qb (Fin.cons z Fin.elim0)) _
  intro beta j Theta rowTail hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  have hltj := InternalGraphCompositionFunctionalityProof.renameInto hlt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hrtj := InternalGraphCompositionFunctionalityProof.renameInto hrt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrtj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  exact at5 n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) (leftTail.relabel j) (lefts.relabel j) (rightTail.relabel j) (rights.relabel j) rowTail hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hltj hlj hrtj hrj hx

theorem at3 (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail lefts rightTail : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    (hrt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightTail b z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons r (Fin.cons rightTail Fin.elim0)) _
  intro beta j Theta rights hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  have hltj := InternalGraphCompositionFunctionalityProof.renameInto hlt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hrtj := InternalGraphCompositionFunctionalityProof.renameInto hrt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrtj
  exact at4 n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) (leftTail.relabel j) (lefts.relabel j) (rightTail.relabel j) rights hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hltj hlj hrtj hx

theorem at2 (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail lefts : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts q leftTail)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons b (Fin.cons z Fin.elim0)) _
  intro beta j Theta rightTail hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  have hltj := InternalGraphCompositionFunctionalityProof.renameInto hlt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact at3 n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) (leftTail.relabel j) (lefts.relabel j) rightTail hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hltj hlj hx

theorem at1 (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 leftTail : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (hlt : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode leftTail a z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons q (Fin.cons leftTail Fin.elim0)) _
  intro beta j Theta lefts hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  have hltj := InternalGraphCompositionFunctionalityProof.renameInto hlt j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
  exact at2 n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) (leftTail.relabel j) lefts hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hltj hx

theorem four (source target k l f g sigma tau ts us q a r b node param qr qb ar ab deps d1 d2 d3 : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,sigma,q,ts,a])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,tau,r,us,b])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qr q r)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ar a r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab a b)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons a (Fin.cons z Fin.elim0)) _
  intro beta j Theta leftTail hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,graph3Rename,ConcreteHeadMoveLayer.SyntaxProof.sixRename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at h3j
  exact at1 n (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (sigma.relabel j) (tau.relabel j) (ts.relabel j) (us.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (param.relabel j) (qr.relabel j) (qb.relabel j) (ar.relabel j) (ab.relabel j) (deps.relabel j) (d1.relabel j) (d2.relabel j) (d3.relabel j) leftTail hsj htj hnj hgj hp0j hp1j hp2j hp3j h0j h1j h2j h3j hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.DependenciesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.DependenciesProof
