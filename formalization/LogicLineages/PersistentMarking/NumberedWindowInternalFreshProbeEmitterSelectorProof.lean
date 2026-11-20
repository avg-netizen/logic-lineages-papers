module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericTargets
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterSelectorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeEmitter
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowFreeAddress (freshName)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowScalarProgramProof (scalarPrim)
open NumberedWindowSyntaxShapePrograms (pairs)

private theorem packPrim : Primrec pack := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.1
  apply ((Proof.primitiveEvaluation 1 p).comp
    (Primrec.vector_cons.comp Primrec.encode (Primrec.const List.Vector.nil))).of_eq
  exact h

private theorem fieldsPrim (s : Settings) : Primrec (probeFields s) := by
  have arrow : Primrec arrowView := (Primrec.nat_casesOn₁ none pairs).of_eq (fun n => by cases n <;> rfl)
  have fresh : Primrec freshName := (Proof.unaryCorrespondence _).mpr
    NumberedWindowFreeAddressProgramChecks.exact_FreeAddressPrograms.2
  let X := Address × Nat × Nat
  have ctx : Primrec (fun row : X => pack row.1.1) := packPrim.comp (Primrec.fst.comp Primrec.fst)
  have ty : Primrec (fun row : X => row.2.1) := Primrec.fst.comp Primrec.snd
  have name : Primrec (fun row : X => freshName row.1.2.2) :=
    fresh.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have coord : Primrec (fun a : Address => (arrowView a.2.1).map
      (fun b => (pack a.1,b.1,freshName a.2.2))) :=
    Primrec.option_map (arrow.comp (Primrec.fst.comp Primrec.snd))
      (ctx.pair (ty.pair name)).to₂
  apply (Primrec.ite (Primrec.eq.comp (scalarPrim s) (Primrec.const true))
    ((Primrec.option_bind₁ coord).comp addressPrim) (Primrec.const none)).of_eq
  intro q
  unfold probeFields
  split
  · simp only [Option.bind_eq_bind]
    congr 1
    funext a
    cases h : arrowView a.2.1 with
    | none => rfl
    | some b => cases b <;> rfl
  · rfl

private theorem goodPrim (s : Settings) : Primrec (goodSpec s) := by
  have h : Primrec (fun q => (probeFields s q).isSome) :=
    Primrec.option_isSome.comp (fieldsPrim s)
  apply (Primrec.cond h (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
  intro q
  unfold goodSpec
  cases (probeFields s q).isSome <;> rfl

private theorem coordinatePrim (s : Settings) {k : Fields → Nat} (h : Primrec k) :
    Primrec (fun q => ((probeFields s q).map k).getD 0) :=
  Primrec.option_getD.comp ((Primrec.option_map₁ h).comp (fieldsPrim s)) (Primrec.const 0)

/-- These four literal leaves are chosen at the same s from actual
original programs for the optional row and its component projections. -/
theorem selected (s : Settings) : ∃ p : Selectors, calibrated s p := by
  have hc : Primrec (contextSpec s) := coordinatePrim s Primrec.fst
  have ht : Primrec (typeSpec s) := coordinatePrim s (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (nameSpec s) := coordinatePrim s (Primrec.snd.comp Primrec.snd)
  obtain ⟨g,hg⟩ := (Proof.unaryCorrespondence _).mp (goodPrim s)
  obtain ⟨c,hc'⟩ := (Proof.unaryCorrespondence _).mp hc
  obtain ⟨t,ht'⟩ := (Proof.unaryCorrespondence _).mp ht
  obtain ⟨n,hn'⟩ := (Proof.unaryCorrespondence _).mp hn
  exact ⟨⟨g,c,t,n⟩,hg,hc',ht',hn'⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterSelectorProof
