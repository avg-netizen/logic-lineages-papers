module

public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionForwardTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.RankedRestrictionForwardListProof
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof RankedRestrictionMatchingProof
open RankedRestrictionForwardTargets

theorem matchNil (S : Signature) : MatchingMotive S .nil .nil := fun _ _ => .nil

theorem matchCons (S : Signature) (q t : Expr) (qs ts rest : Args) (h : Remove ts t rest)
    (ih : WeakMotive S q t) (ih' : MatchingMotive S qs rest) : MatchingMotive S (.cons q qs) ts := by
  intro hQs hTs
  obtain ⟨ht,hrest⟩ := RankedRestrictionSyntaxProof.remove S h hTs
  exact .cons h (ih.1 (hQs 0 q .here) ht) (ih' (fun i q ha => hQs (i+1) q (.there ha)) hrest)

theorem multi (S : Signature) (qs ts kept removed matched added : Args)
    (hS : Split qs kept removed) (hT : Split ts matched added) (hn : Nonempty removed)
    (ih : MatchingMotive S kept matched) (ih' : CoverageMotive S removed added) :
    MultisetMotive S qs ts := by
  intro hQs hTs
  obtain ⟨hK,hR⟩ := RankedRestrictionSyntaxProof.split S hS hQs
  obtain ⟨hM,hA⟩ := RankedRestrictionSyntaxProof.split S hT hTs
  exact RankedRestrictionMatchingProof.replace S hS hT hn (ih hK hM) (ih' hR hA)

theorem coverNil (S : Signature) (qs : Args) : CoverageMotive S qs .nil := fun _ _ => .nil

theorem coverCons (S : Signature) (qs ts : Args) (q t : Expr) (i : Nat) (h : At qs i q)
    (ih : StrictMotive S q t) (ih' : CoverageMotive S qs ts) : CoverageMotive S qs (.cons t ts) := by
  intro hQs hTs
  exact .cons h (ih (hQs i q h) (hTs 0 t .here)) (ih' hQs (fun j u ha => hTs (j+1) u (.there ha)))

theorem wholeNil (S : Signature) (f : Head) (bs es : Args) : WholeMotive S f bs es .nil :=
  fun _ _ _ => .nil

theorem wholeCons (S : Signature) (f : Head) (bs es ts : Args) (t : Expr)
    (ih : WeakMotive S (.marked f t.type bs es) t) (ih' : WholeMotive S f bs es ts) :
    WholeMotive S f bs es (.cons t ts) := by
  intro hE hs hTs
  have ht := hTs 0 t .here
  have he := annotation t ht.2
  exact .cons (ih.2 f bs (by rw [he,hE]) hs ht) (ih' hE hs (fun j u ha => hTs (j+1) u (.there ha)))

end LogicLineages.PersistentMarking.RankedRestrictionForwardListProof
