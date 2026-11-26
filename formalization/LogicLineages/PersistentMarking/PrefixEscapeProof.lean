import LogicLineages.PersistentMarking.PrefixTwoStageProof
import LogicLineages.PersistentMarking.ConservativeOwnerSupport
namespace LogicLineages.PersistentMarking.PrefixEscapeProof
open Spine

theorem tupleCopies {f : Head} {base extras args : Args} {domains : List Ty}
    (h : PrefixTuple f base extras domains args) : PrefixCopies f base extras args := by
  induction h with
  | nil => exact .nil
  | @cons σ q types qs hc hs ih =>
    have hc' : PrefixCopy f base extras q.type q := by cases hc with | intro hp => exact .intro hp
    exact .cons hc' ih

theorem prefixEscape : AuxiliaryTargets.PrefixEscape := by
  intro S f ρ base extras domains₁ domains₂ τ q as bs r w hp hq ha hb hfirst hsecond
  have hta := ConservativeOwnerSupport.tupleTyped S f ρ base extras hp ha (ArrowPrefix domains₂ τ)
  have htb := ConservativeOwnerSupport.tupleTyped S f ρ base extras hp hb τ
  have hr := SpineCallTypingProof.callPreserves EmptyContext q _ as _ r hq.1 hta hfirst
  have hw := SpineCallTypingProof.callPreserves EmptyContext r _ bs τ w hr htb hsecond
  have htype := SpineShiftProof.annotationExact _ _ _ hw
  cases as with
  | nil =>
    simp only [apply,Option.some.injEq] at hfirst
    subst r
    exact Or.inl (by simpa only [Args.append] using hsecond)
  | cons a rest =>
    have hh := PrefixTwoStageProof.staged S f ρ τ base extras q .nil (.cons a rest) bs r w hp .nil (tupleCopies ha) (tupleCopies hb) htype hfirst hsecond
    simpa only [Args.append,apply] using hh
end LogicLineages.PersistentMarking.PrefixEscapeProof
