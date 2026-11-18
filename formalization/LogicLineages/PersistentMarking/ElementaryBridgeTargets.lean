import LogicLineages.PersistentMarking.NameBridge
import LogicLineages.PersistentMarking.SpineMarking
namespace LogicLineages.PersistentMarking.ElementaryBridgeTargets
open Spine NameBridge

def MarkEncoding : Prop := ∀ env q,
  mark (encode env q) = (Term.mark q).map (encode env)

end LogicLineages.PersistentMarking.ElementaryBridgeTargets
