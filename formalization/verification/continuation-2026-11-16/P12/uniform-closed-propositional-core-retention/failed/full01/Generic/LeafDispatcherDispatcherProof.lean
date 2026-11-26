module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcherLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher.DispatcherProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawUniversalDispatcherRetention.TransportProof
open GorbowPRDefiningEquations GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryRuleSuffix
open HistoryDispatcher HistoryDispatcher.SelectProof

variable (testK testS : Program 1)

theorem logical (old : Program 1) : Preserves (applyOne old lineCode)
 (applyOne (extend testK testS old) lineCode) := by
 intro n p tag tag' ht ht' ctx args
 let g : Fin 1 → Program 4 := fun _ => lineCode
 have ho := Equations.functionChild p tag old g ht
 have hn := Equations.functionChild p tag' (extend testK testS old) g ht'
 have harg := Equations.argumentChild p tag old g ht 0
 have harg' := Equations.argumentChild p tag' (extend testK testS old) g ht' 0
 obtain ⟨ha⟩ := Equations.projection p (tag+argumentTag old g 0) (3 : Fin 4) harg args
 obtain ⟨ha'⟩ := Equations.projection p (tag'+argumentTag (extend testK testS old) g 0) (3 : Fin 4) harg' args
 obtain ⟨oe⟩ := Equations.compositionValues p tag old g ht args (args.get 3 ::ᵥ nil) (fun i => by
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact ⟨ha⟩)
 obtain ⟨ne⟩ := Equations.compositionValues p tag' (extend testK testS old) g ht' args (args.get 3 ::ᵥ nil) (fun i => by
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact ⟨ha'⟩)
 obtain ⟨hl⟩ := LeafProof.internalRetention testK testS n p old (tag+1) (tag'+1) ho hn ctx (args.get 3)
 let H := accepts (call tag args)
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 have inner := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ oe)) hh
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base ne) (.mp (.base hl) inner)))⟩

theorem internalDispatcherRetention : Targets.InternalDispatcherRetention testK testS := by
 intro n p valid old arithmetic x tag tag' ht ht' ctx index fuel history line
 let rest := HistoryDispatcher.ruleSelect 1 (applyOne arithmetic lineCode)
  (HistoryDispatcher.ruleSelect 2 mpBranch (HistoryDispatcher.ruleSelect 3 generalizeBranch
   (HistoryDispatcher.ruleSelect 4 (.composition x axiomArguments) (constant 4 0))))
 have hr : Preserves (HistoryDispatcher.ruleDispatcher old arithmetic x)
  (HistoryDispatcher.ruleDispatcher (extend testK testS old) arithmetic x) :=
  RawUniversalDispatcherRetention.TransportProof.choose (applyTwo equalCode ruleCode (constant 4 0)) rest (applyOne old lineCode)
   rest (applyOne (extend testK testS old) lineCode) (reflexive rest) (logical testK testS old)
 have hd : Preserves (original valid old arithmetic x) (extended testK testS valid old arithmetic x) :=
  RawUniversalDispatcherRetention.TransportProof.choose (applyOne valid lineCode) (constant 4 0)
   (HistoryDispatcher.ruleDispatcher old arithmetic x) (constant 4 0)
   (HistoryDispatcher.ruleDispatcher (extend testK testS old) arithmetic x)
   (reflexive (constant 4 0)) hr
 exact hd n p tag tag' ht ht' ctx (index ::ᵥ fuel ::ᵥ history ::ᵥ line ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher.DispatcherProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher.DispatcherProof.internalDispatcherRetention
