module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SupportProof
attribute [local irreducible] programGraph

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro n arity body alpha Delta V node code param source target f g base dest ef eg rf rg symbolsCode typesCode h0 t0 hV hn hp hs ht hef heg hrf hrg hc0
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
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hpj := renameInto hp j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
    have hsj := renameInto hs j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
    have htj := renameInto ht j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
    have hefj := renameInto hef j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hrfj := renameInto hrf j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hrgj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hj := renameInto h j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hj
    have hmove := (HeadMoveFields.InternalProof.internalOrdinary n arity body beta Theta V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (base.relabel j) (g.relabel j) (dest.relabel j) (symbolsCode.relabel j) (typesCode.relabel j) move hVj hnj hpj hsj htj).mp hm
    have maps := outputMaps (OriginalHeadMove.headMove n arity) move
      ![(f.relabel j),(base.relabel j),(g.relabel j),(dest.relabel j),(symbolsCode.relabel j),(typesCode.relabel j)] hmove
    have old := ResultStructuralFields.InternalProof.internalOrdinary body beta Theta
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun i => Fin.elim0 i)) V) V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) move (h0.relabel j) (t0.relabel j)
      hVj hnj hsj htj hefj hegj hrfj hrgj (by simpa only [HeadMoveFields.suppliers,ite_true] using hm) hc0j
    simp only [layer,HeadMoveFields.layer] at hj
    have transformed := (orMap (andMap maps.1 (reflexive _ _)) (reflexive _ _)) Theta (fun _ ha => ha) (old.mp hj)
    simpa only [layer,HeadMoveFields.layer,graph3Rename,SyntaxProof.sixRename,
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
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hVj
    have hnj := renameInto hn j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
    have hpj := renameInto hp j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
    have hsj := renameInto hs j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
    have htj := renameInto ht j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
    have hefj := renameInto hef j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
    have hegj := renameInto heg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
    have hrfj := renameInto hrf j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
    have hrgj := renameInto hrg j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hrgj
    have hc0j := renameInto hc0 j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hc0j
    have hj := renameInto h j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hj
    have hmove := (HeadMoveFields.InternalProof.internalOrdinary n arity body beta Theta V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (base.relabel j) (g.relabel j) (dest.relabel j) (symbolsCode.relabel j) (typesCode.relabel j) move hVj hnj hpj hsj htj).mp hm
    have maps := outputMaps (OriginalHeadMove.headMove n arity) move
      ![(f.relabel j),(base.relabel j),(g.relabel j),(dest.relabel j),(symbolsCode.relabel j),(typesCode.relabel j)] hmove
    have old := ResultStructuralFields.InternalProof.internalOrdinary body beta Theta
      (HeadMoveFields.suppliers n arity (fun _ => .composition .zero (fun i => Fin.elim0 i)) V) V
      (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) move (h0.relabel j) (t0.relabel j)
      hVj hnj hsj htj hefj hegj hrfj hrgj (by simpa only [HeadMoveFields.suppliers,ite_true] using hm) hc0j
    have transformed := old.mpr ((orMap (andMap maps.2 (reflexive _ _)) (reflexive _ _)) Theta (fun _ ha => ha) hj)
    simpa only [layer,HeadMoveFields.layer,graph3Rename,SyntaxProof.sixRename,
      StructuralExchangeFields.InternalProof.andRename,StructuralExchangeFields.InternalProof.orRename,
      eqnRelabel,GuardedSourceSyntaxProof.numeralRename] using transformed
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
