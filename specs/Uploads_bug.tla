----------------------------- MODULE Uploads_bug -----------------------------
EXTENDS FiniteSets

CONSTANTS Contents, Keys

VARIABLES objects  \* set of records [content: Contents, key: Keys]

TypeOK ==
  objects \subseteq [content: Contents, key: Keys]

Init ==
  objects = {}

\* First upload of content with some key (random UUID)
UploadNew ==
  \E content \in Contents, randomKey \in Keys :
    /\ objects' = objects \cup {[content |-> content, key |-> randomKey]}

\* Retry of SAME content, but with DIFFERENT key (bug)
RetrySame ==
  \E content \in Contents, existingKey, newKey \in Keys :
    /\ existingKey # newKey
    /\ [content |-> content, key |-> existingKey] \in objects
    /\ objects' = objects \cup {[content |-> content, key |-> newKey]}

Next == UploadNew \/ RetrySame

\* Invariant: one key per content
AtMostOneKeyPerContent ==
  \A object1, object2 \in objects : object1.content = object2.content => object1.key = object2.key

Spec == Init /\ [][Next]_objects
THEOREM Bad == Spec => [] (TypeOK /\ AtMostOneKeyPerContent)
=============================================================================
