module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.NumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SupportProof
attribute [local irreducible] programGraph

theorem internalNumbered : Targets.InternalNumbered := by
  intro n arity body alpha Delta V node code param source target k l f g tau upsilon base dest ts us extras otherExtras ef eg symbolsCode typesCode h0 t0 h1 t1 h2 t2 h3 t3 hV hn hp hs ht hef heg hc0 hc1 hc2 hc3
  constructor
  · intro h
    apply programCases (HeadMoveFields.move n arity V) ![node,code,param] _
    intro beta j Theta move hj hm
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    rw [hv] at hm
    change Nonempty (Derivation body Theta (graph3 (HeadMoveFields.move n arity V) move (node.relabel j) (code.relabel j) (param.relabel j))) at hm
    have hVj := renameInto hV j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hpj := renameInto hp j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
    have hsj := renameInto hs j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
    have htj := renameInto ht j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
    have hefj := renameInto hef j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hj
    have hsjv : (fun i : Fin 6 => (![k,f,tau,base,ts,extras] i).relabel j) = ![k.relabel j,f.relabel j,tau.relabel j,base.relabel j,ts.relabel j,extras.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
    rw [hsjv] at hsj
    have htjv : (fun i : Fin 6 => (![l,g,upsilon,dest,us,otherExtras] i).relabel j) = ![l.relabel j,g.relabel j,upsilon.relabel j,dest.relabel j,us.relabel j,otherExtras.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
    rw [htjv] at htj
    have hmove := (HeadMoveFields.InternalProof.internalNumbered n arity body beta Theta V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (f.relabel j) (tau.relabel j) (base.relabel j) (ts.relabel j) (extras.relabel j) (l.relabel j) (g.relabel j) (upsilon.relabel j) (dest.relabel j) (us.relabel j) (otherExtras.relabel j) (symbolsCode.relabel j) (typesCode.relabel j) move hVj hnj hpj hsj htj).mp hm
    have maps := outputMaps (OriginalHeadMove.headMove n arity) move
      ![(f.relabel j),(base.relabel j),(g.relabel j),(dest.relabel j),(symbolsCode.relabel j),(typesCode.relabel j)] hmove
    have old := StructuralNumberedLayer.Proof.internalNumbered body beta Theta
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun i => Fin.elim0 i)) V) V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (ef.relabel j) (eg.relabel j) move (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsj htj hefj hegj (by simpa only [HeadMoveFields.suppliers,if_pos rfl] using hm) hc0j hc1j hc2j hc3j
    simp only [layer,HeadMoveFields.layer] at hj
    have transformed := (andMap (reflexive _ _) (orMap (orMap (andMap (reflexive _ _) maps.1) (reflexive _ _)) (reflexive _ _))) Theta (fun _ ha => ha) (old.mp hj)
    simpa only [layer,HeadMoveFields.layer,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] using transformed
  · intro h
    apply programCases (HeadMoveFields.move n arity V) ![node,code,param] _
    intro beta j Theta move hj hm
    have hv : (fun i : Fin 3 => (![node,code,param] i).relabel j) =
        ![node.relabel j,code.relabel j,param.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    rw [hv] at hm
    change Nonempty (Derivation body Theta (graph3 (HeadMoveFields.move n arity V) move (node.relabel j) (code.relabel j) (param.relabel j))) at hm
    have hVj := renameInto hV j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hpj := renameInto hp j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
    have hsj := renameInto hs j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
    have htj := renameInto ht j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
    have hefj := renameInto hef j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hc1j := renameInto hc1 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc1j
    have hc2j := renameInto hc2 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc2j
    have hc3j := renameInto hc3 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc3j
    have hj := renameInto h j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hj
    have hsjv : (fun i : Fin 6 => (![k,f,tau,base,ts,extras] i).relabel j) = ![k.relabel j,f.relabel j,tau.relabel j,base.relabel j,ts.relabel j,extras.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
    rw [hsjv] at hsj
    have htjv : (fun i : Fin 6 => (![l,g,upsilon,dest,us,otherExtras] i).relabel j) = ![l.relabel j,g.relabel j,upsilon.relabel j,dest.relabel j,us.relabel j,otherExtras.relabel j] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
    rw [htjv] at htj
    have hmove := (HeadMoveFields.InternalProof.internalNumbered n arity body beta Theta V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (f.relabel j) (tau.relabel j) (base.relabel j) (ts.relabel j) (extras.relabel j) (l.relabel j) (g.relabel j) (upsilon.relabel j) (dest.relabel j) (us.relabel j) (otherExtras.relabel j) (symbolsCode.relabel j) (typesCode.relabel j) move hVj hnj hpj hsj htj).mp hm
    have maps := outputMaps (OriginalHeadMove.headMove n arity) move
      ![(f.relabel j),(base.relabel j),(g.relabel j),(dest.relabel j),(symbolsCode.relabel j),(typesCode.relabel j)] hmove
    have old := StructuralNumberedLayer.Proof.internalNumbered body beta Theta
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun i => Fin.elim0 i)) V) V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (ef.relabel j) (eg.relabel j) move (h0.relabel j) (t0.relabel j) (h1.relabel j) (t1.relabel j) (h2.relabel j) (t2.relabel j) (h3.relabel j) (t3.relabel j)
      hVj hnj hsj htj hefj hegj (by simpa only [HeadMoveFields.suppliers,if_pos rfl] using hm) hc0j hc1j hc2j hc3j
    simp only [layer,HeadMoveFields.layer] at hj
    have transformed := old.mpr ((andMap (reflexive _ _) (orMap (orMap (andMap (reflexive _ _) maps.2) (reflexive _ _)) (reflexive _ _))) Theta (fun _ ha => ha) hj)
    simpa only [layer,HeadMoveFields.layer,graph3Rename,InternalControlGraphSupportProof.programRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] using transformed
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.NumberedProof
