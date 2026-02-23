------------------------ MODULE ReactionSessionBindingHarness ------------------------
EXTENDS Naturals

(******************************************************************************
* ReactionSessionBindingHarness.tla
*
* Conformance/correctness model (tiny):
* - A reaction event (emoji add/remove) should be routed/bound to the same
*   session as the message it reacts to.
*
* This prevents "reaction storms" from creating new sessions and ensures
* context continuity for follow-ups.
******************************************************************************)

CONSTANTS
  ChannelId,
  MessageId,
  ReactionId

ASSUME
  /\ ChannelId \in {"c"}
  /\ MessageId \in {"m"}
  /\ ReactionId \in {"r"}

\* Session key abstraction: <<channel, anchorMessage>>
SessionKeyForMessage == <<ChannelId, MessageId>>

\* Intended: reactions anchor to the message id, not the reaction id.
SessionKeyForReaction == <<ChannelId, MessageId>>

Inv_ReactionBindsToMessage == SessionKeyForReaction = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
