---------------- MODULE ReactionSessionBindingHarness_BadReactionOwnSession ----------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: reaction events bind to their own id instead of the message id,
* producing new sessions.
******************************************************************************)

CONSTANTS
  ChannelId,
  MessageId,
  ReactionId

ASSUME
  /\ ChannelId \in {"c"}
  /\ MessageId \in {"m"}
  /\ ReactionId \in {"r"}

SessionKeyForMessage == <<ChannelId, MessageId>>

\* BUG: anchors to ReactionId
SessionKeyForReaction == <<ChannelId, ReactionId>>

Inv_ReactionBindsToMessage == SessionKeyForReaction = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
