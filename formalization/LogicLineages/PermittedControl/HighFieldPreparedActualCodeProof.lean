module
public import LogicLineages.PermittedControl.HighFieldPreparedActualTargets
import LogicLineages.PermittedControl.HighFieldPreparedPacketCodeProof
import LogicLineages.PermittedControl.HighFieldComparisonPrimitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open FieldComparison

theorem fullCompilerEffective : FullCompilerEffective := by
  have F : Primrec (fun p : Args => p.1) := Primrec.fst
  have G : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp Primrec.snd
  have rankF : Primrec (fun p : Args => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have rankG : Primrec (fun p : Args => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have wanted : Primrec (fun p : Args => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have descriptor := highFieldComparisonEffective.2.2.2.2.comp (F.pair (G.pair (rankF.pair rankG)))
  exact postprocessEffective.comp (descriptor.pair (rankF.pair (rankG.pair wanted)))

end LogicLineages.PermittedControl.HighFieldPreparedPacket
